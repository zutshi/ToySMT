#pragma once

#include <stdint.h>

#define TY_BOOL 0
#define TY_BITVEC 1

enum OP
{
	OP_NOT,
	OP_EQ,
	OP_NEQ,
	OP_AND,
	OP_OR,
	OP_XOR,
	OP_BVNOT,
	OP_BVNEG,
	OP_BVXOR,
	OP_BVADD,
	OP_BVSUB,
	OP_BVUGE,
	OP_BVUGT,
	OP_BVULE,
	OP_BVULT
};

enum EXPR_TYPE
{
	EXPR_ID,
	EXPR_UNARY,
	EXPR_BINARY,
	EXPR_CONST
};

struct expr
{
	enum EXPR_TYPE type; // rename to node_type?

	// in case of EXPR_ID
	char* id;

	// in case of EXPR_UNARY or EXPR_BINARY
	enum OP op;
	struct expr* op1;
	// in case of EXPR_BINARY
	struct expr* op2;

	// in case of EXPR_CONST
	//uint64_t const_val;
	uint32_t const_val;
	int const_width; // in bits

	// in case of chained expressions:
	struct expr *next;
};

struct expr* create_unary_expr(enum OP t, struct expr* op);
struct expr* create_bin_expr(enum OP t, struct expr* op1, struct expr* op2);
struct expr* create_vararg_expr(enum OP t, struct expr* args);
struct expr* create_distinct_expr(struct expr* args);
struct expr* create_const_expr(uint32_t c, int w);
struct variable* create_variable(char *name, int type, int width, int internal);
void create_assert (struct expr* e);
void check_sat();
void get_model();

