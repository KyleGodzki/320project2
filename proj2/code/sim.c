#include <stdio.h>
#include <stdlib.h>
#include <stdint.h>
#include <string.h>
#include <stdbool.h>

#define MEM_WORDS 2048
#define NUM_REGS 32
#define EMPTY_PC 0xffffffffu

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

static int32_t add32(int32_t a, int32_t b) {
	return (int32_t)((uint32_t)a + (uint32_t)b);
}
static int32_t sub32(int32_t a, int32_t b) {
	return (int32_t)((uint32_t)a - (uint32_t)b);
}
static int32_t mul32(int32_t a, int32_t b) {
	return (int32_t)((uint32_t)a * (uint32_t)b);
}
static int32_t div32(int32_t a, int32_t b) {
	if (b == 0) return 0;
	if (b == -1) return sub32(0, a);
	return a / b;
}

static Latch empty_latch(void) {
	Latch empty;
	memset(&empty, 0, sizeof empty);
	empty.pc = EMPTY_PC;
	empty.op = OP_NOP;
	empty.dest = -1;
	empty.src1 = -1;
       	empty.src2 = -1;
	return empty;
}

void load_memory(const char *path) {
	FILE *f = fopen(path, "r");
	unsigned long long a, v;
	if (!f) {
		perror("Can't open file!"); 
		exit(1);
	}
	while (fscanf(f, "%llx %llx", &a, &v) == 2) {
		if ((a & 3) == 0 && (a >> 2) < MEM_WORDS)
			mem[a >> 2] = (uint32_t)v;
	}
	fclose(f);
}

static uint32_t fetch_word(uint32_t address) {
	uint32_t index = address >> 2;
	return index < MEM_WORDS ? mem[index] : 0;
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
			decode.dest = b2 & 31; decode.src1 = b3 & 31; decode.src2 = b4 & 31;
			break;
		case OP_ADDI: case OP_SUBI: case OP_MULI: case OP_DIVI: case OP_LD:
			decode.dest = b2 & 31; decode.src1 = b3 & 31; decode.imm = (int8_t)b4;
			break;
		case OP_ST:
			decode.src1 = b3 & 31; decode.src2 = b2 & 31; decode.imm = (int8_t)b4;
			break;
		case OP_MOV:
			decode.dest = b2 & 31; decode.imm = (int16_t)((b3 << 8) | b4);
			break;
		case OP_B:
			decode.imm = (int16_t)((b3 << 8) | b4);
			break;
		case OP_CBZ: case OP_CBNZ: case OP_CBNEG:
			decode.src1 = b2 & 31; decode.imm = (int16_t)((b3 << 8) | b4);
			break;
		case OP_EXIT:
			break;
		default:
			decode.op = OP_NOP;
			break;
	}
	return decode;

}

bool is_branch(uint32_t op) {
	switch (op) {
		case OP_B: case OP_CBZ: case OP_CBNZ: case OP_CBNEG:
			return true;
		default:
			return false;
	}
}

static void ex1_stage(Latch *l) {
	switch (l->op) {
		case OP_ADD: l->result = add32(l->v1, l->v2); break;
		case OP_ADDI: l->result = add32(l->v1, l->imm); break;
		case OP_SUB: l->result = sub32(l->v1, l->v2); break;
		case OP_SUBI: l->result = sub32(l->v1, l->imm); break;
		case OP_MOV: l->result = l->imm; break;
		case OP_LD: case OP_ST:
			     l->addr = (uint32_t)add32(l->v1, l->imm);
			     break;
		case OP_B: case OP_CBZ: case OP_CBNZ: case OP_CBNEG:
			     l->target = l->pc + 4u * (uint32_t)l->imm;
			     break;
		default:
			     break;
	}
}

static void ex2_stage(Latch *l) {
	switch (l->op) {
		case OP_MUL: l->result = mul32(l->v1, l->v2); break;
		case OP_MULI: l->result = mul32(l->v1, l->imm); break;
		case OP_DIV: l->result = div32(l->v1, l->v2); break;
		case OP_DIVI: l->result = div32(l->v1, l->imm); break;
		case OP_B: l->taken = 1; break;
		case OP_CBZ: l->taken = (l->v1 == 0); break;
		case OP_CBNZ: l->taken = (l->v1 != 0); break;
		case OP_CBNEG: l->taken = (l->v1 < 0); break;
		default:
			       break;
	}
}

static void mem_stage(Latch *l) {
	uint32_t index = l->addr >> 2;
	if (l->op == OP_LD) {
		l->result = (int32_t)(index < MEM_WORDS ? mem[index]: 0);
	} else if (l->op == OP_ST) {
		if (index < MEM_WORDS) mem[index] = (uint32_t)l->v2;
	}
}



int main(int argc,char **argv) {
	static const char *stage_name[3] = {"ex1", "ex2", "mem"};
	uint32_t pc = 0;
	IfDr d = {EMPTY_PC, 0, 0};
	Latch e1 = empty_latch(), e2 = empty_latch(), m = empty_latch(), w = empty_latch();
	long total = 0, cycles = 0;
	long cycle;

	if (argc != 2) {
		fprintf(stderr, "usage: %s <initial-memory-file\n", argv[0]);
		return 1;
	}
	load_memory(argv[1]);

	printf("== cycle |    fetch |   decode |  exec1   |  exec2   |   memory | writeBack|\n");
	printf("== ------+----------+----------+----------+----------+----------+----------|\n");

	for (cycle = 0; ; cycle++) {
		Latch d1;
		const Latch *older[3];
		int hz_reg = -1, hz_stage = -1, stall, squash, i, k;
		int srcs[2];

		printf("== %5ld | %8x | %8x | %8x | %8x | %8x | %8x |\n", cycle, pc, d.valid ? d.pc: EMPTY_PC, e1.pc, e2.pc, m.pc, w.pc);

		// WB
		if (w.dest >= 0) regs[w.dest] = w.result;
		if (w.op != OP_NOP) {counts[w.op]++; total++;}
		if (w.op == OP_EXIT) {cycles = cycle + 1; break; }

		mem_stage(&m);
		ex2_stage(&e2);
		ex1_stage(&e1);

		// DR
		d1 = d.valid ? decode_word(d.pc, d.word): empty_latch();
		older[0] = &e1; older[1] = &e2; older[2] = &m;
		srcs[0] = d1.src1; srcs[1] = d1.src2;
		for (i = 0; i < 2 && hz_reg < 0; i++) {
			if (srcs[i] < 0) continue;
			for (k = 0; k < 3; k++) {
				if (older[k]->dest == srcs[i]) {hz_reg = srcs[i]; hz_stage = k; break;}
			}
		}
		if (hz_reg >= 0) {
			printf("Data hazard... register X%d will be written by the instruction in the %s stage\n", hz_reg, stage_name[hz_stage]);
		}
		if (d1.src1 >= 0) d1.v1 = regs[d1.src1];
		if (d1.src2 >= 0) d1.v2 = regs[d1.src2];

		// Control hazadr
		squash = is_branch(e2.op) && e2.taken;
		if (squash) {printf("Control hazard... squashing ID, and EX1 and resetting PC\n");}
		stall = (hz_reg >= 0) && !squash;

		// Advance
		w = m;
		m = e2;
		e2 = e1;
		if (squash) {
			e2 = empty_latch();
			e1 = empty_latch();
			d.valid = 0; d.pc = EMPTY_PC;
			pc = m.target;
		} else if (stall) {
			e1 = empty_latch();
			e1.pc = d.pc;
		} else {
			e1 = d1;
			d.pc = pc; d.word = fetch_word(pc); d.valid = 1;
			pc += 4;
		}
	}

	printf("=== Simulation Reports ===\n");
	printf("Non-Zero Registers....\n");
	
	int reg;
	for (reg = 0; reg < NUM_REGS; reg++) {
		if (regs[reg] != 0) {printf("  X%d = %d\n", reg, regs[reg]);}
	}

	printf("Instruction Count Report...\n");
	printf("   OPCODE - CNT\n");

	size_t n;
	for (n = 0; n < sizeof report_order / sizeof report_order[0]; n++) {
		if (counts[report_order[n].op] > 0) {
			printf("%9s - %3ld\n", report_order[n].name, counts[report_order[n].op]);
		}
	}

	printf("\nTotal Instructions=%ld Cycles = %ld IPC=%5.2f\n",
			total, cycles, cycles ? (double)total / (double)cycles: 0.0);
	return 0;


}
