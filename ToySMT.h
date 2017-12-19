#pragma once

#include <stdint.h>

#define TY_BOOL 0
#define TY_BITVEC 1

#define OP_NOT 0
#define OP_EQ 1
#define OP_AND 2
#define OP_OR 3
#define OP_XOR 4
#define OP_BVNOT 5
#define OP_BVNEG 6
#define OP_BVXOR 7
#define OP_BVADD 8
#define OP_BVSUB 9
#define OP_BVUGE 10
#define OP_BVUGT 11
#define OP_BVULE 12
#define OP_BVULT 13

#define EXPR_ID 0
#define EXPR_UNARY 1
#define EXPR_BINARY 2
#define EXPR_CONST 3

struct expr
{
	int type; // rename to node_type?

	// in case of EXPR_ID
	char* id;

	// in case of EXPR_UNARY or EXPR_BINARY
	int expr_type; // rename to op_type?
	struct expr* op1;
	// in case of EXPR_BINARY
	struct expr* op2;

	// in case of EXPR_CONST
	//uint64_t const_val;
	uint32_t const_val;
	int const_width; // in bits
};

struct expr* create_unary_expr(int t, struct expr* op);
struct expr* create_bin_expr(int t, struct expr* op1, struct expr* op2);
struct expr* create_const_expr(uint32_t c, int w);
struct variable* create_variable(char *name, int type, int width, int internal);
void create_assert (struct expr* e);
void check_sat();
void get_model();

