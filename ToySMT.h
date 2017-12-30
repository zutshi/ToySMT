#pragma once

#include <stdint.h>
#include <stdbool.h>

#define TY_BOOL 0
#define TY_BITVEC 1

enum OP
{
	OP_NOT,
	OP_BVSHL1,
	OP_BVSHR1,
	OP_EQ,
	OP_NEQ,
	OP_AND,
	OP_OR,
	OP_XOR,
	OP_BVNOT,
	OP_BVNEG,
	OP_BVXOR,
	OP_BVADD,
	OP_BVAND,
	OP_BVMUL,
	OP_BVSUB,
	OP_BVUGE,
	OP_BVUGT,
	OP_BVULE,
	OP_BVULT,
	OP_BVSUBGE,
	OP_BVUDIV,
	OP_BVUREM,
	OP_ITE
};

enum EXPR_TYPE
{
	EXPR_ID,
	EXPR_UNARY,
	EXPR_BINARY,
	EXPR_TERNARY,
	EXPR_CONST,
	EXPR_ZERO_EXTEND, // op1 and const_val are used!
	EXPR_EXTRACT // op1 and const_val and const_width are used!
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
	// in case of EXPR_TERNARY (OP_ITE):
	struct expr* op3;

	// in case of EXPR_CONST
	//uint64_t const_val;
	uint32_t const_val;
	int const_width; // in bits

	// in case of chained expressions:
	struct expr *next;
};

struct expr* create_unary_expr(enum OP t, struct expr* op);
struct expr* create_bin_expr(enum OP t, struct expr* op1, struct expr* op2);
struct expr* create_ternary_expr(enum OP t, struct expr* op1, struct expr* op2, struct expr* op3);
struct expr* create_vararg_expr(enum OP t, struct expr* args);
struct expr* create_distinct_expr(struct expr* args);
struct expr* create_const_expr(uint32_t c, int w);
struct expr* create_zero_extend_expr(int bits, struct expr* e);
struct expr* create_extract_expr(unsigned end, unsigned start, struct expr* e);
struct expr* create_ITE(struct expr* sel, struct expr* t, struct expr* f);

struct variable* create_variable(char *name, int type, int width, int internal);
void init();
void create_assert (struct expr* e);
void check_sat();
void get_model();
void get_all_models(bool dump_variables);

// global switches
bool dump_internal_variables;

