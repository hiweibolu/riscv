#define _CRT_SECURE_NO_WARNINGS
//#define __DEBUG
#include<cstdio>
#include<cstring>
using namespace std;

struct predictor {
	int tot, win;
	bool state[2];

	predictor() {
		tot = win = 0;
		state[0] = state[1] = 0;
	}
	void print() {
		printf("%d %d %lf%%\n", win, tot, win * 1.0 / tot * 1e2);
	}
	bool predict() {
		if (tot>100 && win*1.0/tot<0.48) return tot&1;
		return state[1];
		//return 0;
	}
	void update(int winn) {
		tot++;
		if (winn) {
			win++;
			state[0] = state[1];
		}
		else {
			if (state[0] == state[1]) {
				state[0] ^= true;
			}
			else {
				bool x = state[0];
				state[0] = state[1];
				state[1] = x;
			}
		}
	}
}pd;

unsigned translate(const unsigned char* s) {
	unsigned num = 0;
	for (; *s; s++) {
		num = num * 16;
		if (*s >= '0' && *s <= '9') num += *s - '0';
		else num += *s - 'A' + 10;
	}
	return num;
}
unsigned load(const unsigned char* s, int len = 4) {
	unsigned num = 0;
	for (int i = 0; i < len; i++) {
		num += *s << i * 8;
		s++;
	}
	return num;
}
void store(unsigned char* s, unsigned x, int len) {
	for (int i = 0; i < len; i++) {
		*s = x & 255u;
		x >>= 8;
		s++;
	}
}

unsigned getValue(unsigned x, unsigned st, unsigned ed) {
	return (x & ((1ull << ed) - 1)) >> st;
}

const int maxMemoryBytes = 131072;
unsigned char mem[maxMemoryBytes];
unsigned pc, reg[32];
unsigned char inp[10];

struct instruction {
	unsigned text;
	//unsigned imm, rs1, rs2, res, addr;
	unsigned get(unsigned st, unsigned ed) {
		return getValue(text, st, ed);
	}
	unsigned getrd() {
		return get(7, 12);
	}
};

struct IFID :public instruction {
	unsigned pc;
}ifid;

struct IDEX :public instruction {
	unsigned imm, rs1, rs2, pc;
}idex;

struct EXMEM :public instruction {
	unsigned addr, res, rs2, time;
	bool loading, changed;
}exmem;

struct MEMWB :public instruction {
	unsigned res;
	bool loading, changed;
}memwb;

void IF(IFID &tar) {
	tar.text = load(mem + pc);
	if (tar.text == 0) {
		return;
	}
	//printf("%u\n", tar.text);
	tar.pc = pc;
	pc += 4;
}
void ID(IFID& ins, IDEX& tar) {
	unsigned opcode = ins.get(0, 7);
	unsigned r1 = ins.get(15, 20), r2 = ins.get(20, 25);
	if (opcode == 99) {//B-type
		tar.imm = (ins.get(8, 12) << 1) + (ins.get(25, 31) << 5) + (ins.get(7, 8) << 11);
		if (ins.get(31, 32) == 1) tar.imm += (((1 << 20) - 1) << 12);
		tar.rs1 = r1;
		tar.rs2 = r2;

		if (pd.predict()) pc = ins.pc + tar.imm;
	}
	else if (opcode == 3 || opcode == 19 || opcode == 103) {//I-type
		tar.imm = ins.get(20, 21) + (ins.get(21, 25) << 1) + (ins.get(25, 31) << 5);
		if (ins.get(31, 32) == 1) tar.imm += (((1 << 21) - 1) << 11);
		tar.rs1 = r1;
	}
	else if (opcode == 35) {//S-type
		tar.imm = ins.get(7, 8) + (ins.get(8, 12) << 1) + (ins.get(25, 31) << 5);
		if (ins.get(31, 32) == 1) tar.imm += (((1 << 21) - 1) << 11);
		tar.rs1 = r1;
		tar.rs2 = r2;
	}
	else if (opcode == 51) {//R-type
		tar.rs1 = r1;
		tar.rs2 = r2;
	}
	else if (opcode == 55 || opcode == 23) {//U-type
		tar.imm = (ins.get(12, 20) << 12) + (ins.get(20, 31) << 20) + (ins.get(31, 32) << 31);
	}
	else if (opcode == 111) {//J-type
		tar.imm = (ins.get(21, 25) << 1) + (ins.get(25, 31) << 5) + (ins.get(20, 21) << 11) + (ins.get(12, 20) << 12);
		if (ins.get(31, 32) == 1) tar.imm += (((1 << 12) - 1) << 20);
		pc = ins.pc + tar.imm;
	}

	if (exmem.loading && (tar.rs1 && exmem.getrd() == tar.rs1 || tar.rs2 && exmem.getrd() == tar.rs2)) return;

	if (tar.rs1) {
		if (exmem.text && exmem.changed && exmem.getrd() == tar.rs1) tar.rs1 = exmem.res;
		else if (memwb.text && memwb.changed && memwb.getrd() == tar.rs1) tar.rs1 = memwb.res;
		else tar.rs1 = reg[tar.rs1];
	}
	if (tar.rs2) {
		if (exmem.text && exmem.changed && exmem.getrd() == tar.rs2) tar.rs2 = exmem.res;
		else if (memwb.text && memwb.changed && memwb.getrd() == tar.rs2) tar.rs2 = memwb.res;
		else tar.rs2 = reg[tar.rs2];
	}

	tar.text = ins.text;
	tar.pc = ins.pc;
	memset(&ins, 0, sizeof ins);
	//ins.text = 0;
}
void EX(IDEX& ins, EXMEM& tar) {
	unsigned opcode = ins.get(0, 7);
	if (opcode == 99) {//B-type
		unsigned func3 = ins.get(12, 15);
		bool jumping = false;
		if (func3 == 0) jumping = (ins.rs1 == ins.rs2);//BEQ
		else if (func3 == 1) jumping = (ins.rs1 != ins.rs2);//BNE
		else if (func3 == 4) jumping = ((int)ins.rs1 < (int)ins.rs2);//BLT
		else if (func3 == 5) jumping = ((int)ins.rs1 >= (int)ins.rs2);//BGE
		else if (func3 == 6) {
			//printf("%u %u\n", ins.rs1, ins.rs2);
			jumping = (ins.rs1 < ins.rs2);//BLTU
		}
		else if (func3 == 7) jumping = (ins.rs1 >= ins.rs2); //BGEU
		if (jumping != pd.predict()) {
			if (pd.predict()) pc = ins.pc + 4; 
			else pc = ins.pc + ins.imm;
			memset(&ifid, 0, sizeof ifid);
		}
		pd.update(pd.predict() == jumping);
	}
	else if (opcode == 3 || opcode == 19 || opcode == 103) {//I-type
		unsigned func3 = ins.get(12, 15);
		if (opcode == 3) {//LB, LH, LW, LBU, LHU
			tar.addr = ins.rs1 + ins.imm;
			tar.loading = true;
		}
		else if (opcode == 19) {
			if (func3 == 0) {//ADDI
				tar.res = ins.rs1 + ins.imm;
			}
			else if (func3 == 2) {//SLTI
				tar.res = ((int)ins.rs1 < (int)ins.imm);
			}
			else if (func3 == 3) {//SLTIU
				tar.res = ins.rs1 < ins.imm;
			}
			else if (func3 == 4) {//XORI
				tar.res = ins.rs1 ^ ins.imm;
			}
			else if (func3 == 6) {//ORI
				tar.res = ins.rs1 | ins.imm;
			}
			else if (func3 == 7) {//ANDI
				tar.res = ins.rs1 & ins.imm;
			}
			else if (func3 == 1) {//SLLI
				unsigned shamt = ins.get(20, 26);
				tar.res = ins.rs1 << shamt;
			}
			else if (func3 == 5) {
				unsigned shamt = ins.get(20, 26);
				if (ins.get(30, 31) == 0) {//SRLI
					tar.res = ins.rs1 >> shamt;
				}
				else {//SRAI
					tar.res = (((int)ins.rs1) >> ((int)shamt));
				}
			}
		}
		else if (opcode == 103) {//JALR
			tar.res = ins.pc + 4;
			pc = ((ins.rs1 + ins.imm) & ~1);
			memset(&ifid, 0, sizeof ifid);
		}
		tar.changed = true;
	}
	else if (opcode == 35) {//S-type SB, SH, SW
		tar.addr = ins.rs1 + ins.imm;
	}
	else if (opcode == 51) {//R-type
		unsigned func3 = ins.get(12, 15), func7 = ins.get(25, 32);
		if (func3 == 0) {
			if (func7 == 0) {//ADD
				tar.res = ins.rs1 + ins.rs2;
			}
			else {//SUB
				tar.res = ins.rs1 - ins.rs2;
			}
		}
		else if (func3 == 1) {//SLL
			tar.res = ins.rs1 << (ins.rs2 & 31);
		}
		else if (func3 == 2) {//SLT
			tar.res = ((int)ins.rs1 < (int)ins.rs2);
		}
		else if (func3 == 3) {//SLTU
			tar.res = (ins.rs1 < ins.rs2);
		}
		else if (func3 == 4) {//XOR
			tar.res = ins.rs1 ^ ins.rs2;
		}
		else if (func3 == 5) {
			if (func7 == 0) {//SRL
				tar.res = ins.rs1 >> (ins.rs2 & 31);
			}
			else {//SRA
				tar.res = ((int)ins.rs1) >> ((int)ins.rs2 & 31);
			}
		}
		else if (func3 == 6) {//OR
			tar.res = ins.rs1 | ins.rs2;
		}
		else if (func3 == 7) {//AND
			tar.res = ins.rs1 & ins.rs2;
		}
		tar.changed = true;
	}
	else if (opcode == 55 || opcode == 23) {//U-type
		if (opcode == 55) tar.res = ins.imm;//LUI
		else if (opcode == 23) tar.res = ins.pc + ins.imm;//AUIPC
		tar.changed = true;
	}
	else if (opcode == 111) {//J-type JAL
		tar.res = ins.pc + 4;
		tar.changed = true;
		/*pc = ins.pc + ins.imm;
		memset(&ifid, 0, sizeof ifid);*/
	}
	tar.rs2 = ins.rs2;
	tar.time = 3;
	tar.text = ins.text;

	memset(&ins, 0, sizeof ins);
}
void MEM(EXMEM& ins, MEMWB& tar) {
	tar.res = ins.res;
	unsigned opcode = ins.get(0, 7);
	if (opcode == 99) {//B-type
	}
	else if (opcode == 3 || opcode == 19 || opcode == 103) {//I-type
		unsigned func3 = ins.get(12, 15);
		if (opcode == 3) {
			if (--ins.time) return;
			if (func3 == 0) {//LB
				tar.res = load(mem + ins.addr, 1);
				if (tar.res >> 7 & 1) tar.res += ((1 << 24) - 1) << 8;
			}
			else if (func3 == 1) {//LH
				tar.res = load(mem + ins.addr, 2);
				if (tar.res >> 15 & 1) tar.res += ((1 << 16) - 1) << 16;
			}
			else if (func3 == 2) tar.res = load(mem + ins.addr, 4);//LW
			else if (func3 == 4) tar.res = load(mem + ins.addr, 1);//LBU
			else if (func3 == 5) tar.res = load(mem + ins.addr, 2);//LHU
		}
		else if (opcode == 19) {

		}
	}
	else if (opcode == 35) {//S-type
		if (--ins.time) return;
		unsigned func3 = ins.get(12, 15);
		if (func3 == 0) {//SB
			store(mem + ins.addr, ins.rs2, 1);
		}
		else if (func3 == 1) {//SH
			store(mem + ins.addr, ins.rs2, 2);
		}
		else if (func3 == 2) {//SW
			store(mem + ins.addr, ins.rs2, 4);
		}
	}
	else if (opcode == 51) {//R-type
	}
	else if (opcode == 55 || opcode == 23) {//U-type
	}
	else if (opcode == 111) {//J-type
	}

	tar.text = ins.text;
	tar.changed = ins.changed;
	tar.loading = ins.loading;
	memset(&ins, 0, sizeof ins);
}
void WB(MEMWB& ins) {
	unsigned opcode = ins.get(0, 7);
	if (opcode == 99) {//B-type
	}
	else if (opcode == 3 || opcode == 19 || opcode == 103) {//I-type
		unsigned rd = ins.get(7, 12);
		if (opcode == 103 && rd == 0);//JALR
		else reg[rd] = ins.res;
	}
	else if (opcode == 35) {//S-type
	}
	else if (opcode == 51) {//R-type
		reg[ins.get(7, 12)] = ins.res;
	}
	else if (opcode == 55 || opcode == 23) {//U-type
		reg[ins.get(7, 12)] = ins.res;
	}
	else if (opcode == 111) {//J-type JAL
		unsigned rd = ins.get(7, 12);
		if (rd == 0);
		else reg[rd] = ins.res;
	}

	memset(&ins, 0, sizeof ins);
}

void run() {
	while (ifid.text != 0x0ff00513 || idex.text || exmem.text || memwb.text) {
		/*IF();

		if (ins.text == 0x0ff00513) break;

		#ifdef __DEBUG
		printf("%#x: %#x\n", pc, ins.text);
		#endif

		ID(ins);
		EX(ins);
		MEM(ins);
		WB(ins);*/

		if (memwb.text) WB(memwb);

		if (exmem.text && memwb.text == 0) MEM(exmem, memwb);

		if (idex.text && exmem.text==0) EX(idex, exmem);

		if (ifid.text && ifid.text!=0x0ff00513 && idex.text==0) ID(ifid, idex);

		if (ifid.text==0) IF(ifid);
	}
	printf("%u\n", ((unsigned int)reg[10]) & 255u);
}

int main() {
	//freopen("test.data", "r", stdin);
	pc = 0;
	memset(reg, 0, sizeof reg);
	int p = 0;
	while (scanf("%s", inp) != EOF) {
		if (inp[0] == '@') p = translate(inp + 1);
		else mem[p] = translate(inp), p++;
	}
	run();
	//pd.print();
}