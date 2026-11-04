#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>

#define MEM_WORDS 2048
#define NUM_REGS 32
#define EMPTY_PC 0xffffffffu

#define FIRST_BYTE_IS_MSB 1
#define BRANCH_BASE_OFFSET 0

enum {
	OP_NOP = 0x00, OP_ADD = 0x02, OP_ADDI = 0x03, OP_SUB = 0x04, OP_SUBI = 0x05,
	OP_MUL = 0x06, OP_MULI = 0x07, OP_DIV = 0x08, OP_DIVI = 0x09,
	OP_LD = 0x0B, OP_ST = 0x0D, OP_EXIT = 0x0E, OP_MOV = 0x11,
	OP_B = 0x13, OP_CBZ = 0x15, OP_CBNZ = 0x17, OP_CBNEG = 0x19
};

static const struct {int op; const char *name;} report_order[] = {
	{OP_ADD, "ADD"}, {OP_ADDI, "ADDI"}, {OP_SUB, "SUB"},
	{OP_SUBI, "SUBI"}, {OP_MUL, "MUL"}, {OP_MULI, "MULI"},
	{OP_DIV, "DIV"}, {OP_DIVI, "DIVI"}, {OP_LD, "LD"},
	{OP_ST, "ST"}, {OP_EXIT, "EXIT"}, {OP_MOV, "MOV"},
	{OP_B, "B"}, {OP_CBZ, "CBZ"}, {OP_CBNZ, "CBNZ"},
	{OP_CBNEG, "CBNEG"},
};

typedef struct {
	uint32_t pc;
	uint32_t word;
	int valid;
} IfDr;

typedef struct {
	uint32_t pc;
	int op;
	int dest, src1, src2;
	int32_t imm;
	int32_t v1, v2;
	int32_t result;
	uint32_t addr;
	uint32_t target;
	int taken;
} Latch;

static uint32_t mem[MEM_WORDS];
static int32_t regs[NUM_REGS];
static long counts[256];

static Latch empty_latch(void) {
	Latch empty;
	empty.pc = EMPTY_PC;
	empty.op = OP_NOP;
	empty.dest = 0;
	empty.src1 = 0;
       	empty.src2 = 0;
}

void load_memory(const char *path) {
	FILE *f = fopen(path, "r");
	unsigned long long a, v;
	if (!f) {
		perror("Can't open file!"); 
		exit(1);
	}
	while (fscanf(f, "11x %11x", &a, &v) == 2) {
		if ((a & 3) == 0 && (a >> 2) < MEM_WORDS)
			mem[a >> 2] = (uint32_t)v;
	}
	fclose(f);
}

static uint32_t fetch_word(uint32_t address) {
	uint32_t index = address >> 2;
	return index < MEMWORDS ? mem[index] : 0;
}

static Latch decode_word(uint32_t pc, uint32_t w) {
	Latch decode = empty_latch();
	unsigned b1, b2, b3, b4; 
	b1 = (w >> 24) & 0xff;
	b2 = (w >> 16) & 0xff;
	b3 = (w >> 8) & 0xff;
	b4 = w & 0xff;

	decode.pc = pc;
	decode.op = (int)b1;
	switch (b1) {
		case OP_ADD: case OP_SUB: case OP_MUL: case OP_DIV:
			decode.dest = b2; decode.src1 = b3; decide,src2 = b4;
		case OP_ADDI: case OP_SUBI: case OP_MULI: case OP_DIVI: case OP_LD:
			decode.dest = b2; decode.src1 = b3; decode.imm = b4;
		case OP_ST:
			decode.src1 = b2; decode.src2 = b3; decode.imm = b4;
		case OP_MOV:
			decode.dest = b2; decode.imm = b3;
		case OP_B: case OP_CBZ: case OP_CBNZ: case OP_CBNEG:
			decode.src1 = b2; decode.imm = b3;
		default:
			decode.dest = OP_NOP; decode.src1 = OP_NOP; decode.src2 = OP_NOP;
	}

}

bool is_branch(uint32_t op) {
	switch (op) {
		case OP_B: case OP_CBZ: case OP_CBNZ: case OP_CBNEG:
			return true;
		default:
			return false;
	}
	return false;
}

static void ex1_stage(Latch *1) {
	switch (1->op) {
		case OP_ADD: 1->result = add32(1->v1, 1->v2); break;
		case OP_ADDI: 1->result = add32(1->v1, 1->imm); break;
		case OP_SUB: 1->result = sub32(1->v1, 1->v2); break;
		case OP_SUBI: 1->result = sub32(1->v1, 1->imm); break;
		case OP_MOV: 1->result = 1->imm;
		case OP_LD: case OP_ST:
			     1->addr = (uint32_t)add32(1->v1, 1->imm);
			     break;
		case OP_B: case OP_CBZ: case OP_CBNZ: case OP_CBNEG:
			     1->target = 1->pc + 4u * (uint32_t)1->imm;
			     break;
		default:
			     break;
	}
}

static void ex2_stage(Latch *1) {
	switch (1->op) {
		case OP_MUL: 1->result = mul32(1->v1, 1->v2); break;
		case OP_MULI: 1->result = mul32(1->v1, 1->imm); break;
		case OP_DIV: 1->result = div32(1->v1, 1->v2); break;
		case OP_DIVI: 1->result = div32(1->v1, 1->imm); break;
		case OP_B: 1->taken = 1; break;
		case OP_CBZ: 1->taken = (1->v1 == 0); break;
		case OP_CBNZ: 1->taken = (1->v1 != 0); break;
		case OP_CBNEG: 1->taken = (1->v1 < 0); break;
		default:
			       break;
	}
}

static void mem_stage(Latch *1) {
	uint32_t index = 1->address >> 2;
	if (1->op == OP_LD) {
		1->result = (int32_t)(index < MEM_WORDS ? mem[idx]: 0);
	} else if (1->op == OP_ST) {
		if (idx < MEM_WORDS) mem[idx] = (uint32_t)1->v2;
	}
}



int main(int argc,char **argv) {
	static const char *stage_name[3] = {"ex1", "ex2", "mem"};
	uint32_t pc = 0;
	IfDr d = {EMPTY_PC, 0, 0};
	

}
