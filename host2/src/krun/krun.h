/* krun.h — the [flow-eval] claim checker's shared contract.
   One TU per leg: sx (wire s-expr reader), wire (Sx -> AST total
   decoders + values), eval (the runK twin), quote (quoteProg twin),
   main (claim check / --emit host).  Refuse = 0/NULL, never guess. */
#ifndef KRUN_H
#define KRUN_H

#define _CRT_SECURE_NO_WARNINGS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <inttypes.h>

/* ---- util (in sx.c) ---- */
void *xmalloc(size_t n);
void *xrealloc(void *p, size_t n);
char *xstrndup(const char *s, size_t n);
char *xstrdup(const char *s);
char *file_read_all(const char *path);

typedef struct Sx {
    int is_list;            /* 0 atom, 1 list */
    char *atom;             /* quoted atoms keep their quotes */
    struct Sx **kids;
    int n;
} Sx;


/* ---- sx.c ---- */
int sx_is_atom(Sx *x, const char *s);
Sx *parse_top(const char *line);

typedef struct Val Val;
struct Val {
    int tag;                /* 0 int, 1 float(n,d), 2 bool, 3 str, 4 arr, 5 cell */
    int64_t i, d;
    int b;
    char *s;
    Val **xs; int nx;       /* arr */
    char **ns; Val **vs; int nf;  /* cell */
};

/* ================= expressions / program ================= */

typedef struct Expr Expr;
struct Expr {
    int tag;               /* 0 lit 1 var 2 bin 3 un 4 cond 5 field 6 index 7 builtin */
    Val *lit;
    char *name;            /* var, field name, builtin name */
    int op;
    Expr *a, *b, *c;       /* bin l/r, un e, cond c/t/e, field/index obj+idx */
    Expr **args; int nargs;
};

typedef struct NE { char *n; Expr *e; } NE;   /* named expr */

typedef struct Arm Arm;
struct Arm {
    char *branch;          /* "" = unset in decode; catchall sets "*" + flag */
    int catchall;
    char *bind;            /* NULL = none */
    Expr *cond;            /* NULL = none */
    int ntag;              /* -1 none, 0 terminal, 1 jump, 2 invoke, 3 produce, 4 retctor */
    char *ntarget;         /* jump/invoke/retctor name */
    NE *nargs; int nnargs; /* jump/invoke named arg exprs */
    Expr *nexpr;           /* produce/retctor */
    Arm **conts; int nconts;
};

typedef struct Flow {
    char *pre;             /* NULL = none */
    char *hname;
    NE *hargs; int nhargs;
    Arm **arms; int narms;
} Flow;

typedef struct Callable {
    int t;                 /* 0 bare, 1 thunk, 2 subflow */
    Expr *bare;
    Flow *flow;
} Callable;

typedef struct NV { char *n; Val *v; } NV;

typedef struct Decl { char *n; Callable *c; } Decl;

typedef struct {
    Decl *graph; int ng;
    char *entry;
    NV *args; int nargs;
} Prog;

typedef struct { char *branch; Val *payload; } Result;

typedef struct {
    char *name; NV *args; int nargs; Result r;
} Leaf;

typedef struct {
    Prog prog;
    Leaf *oracle; int noracle;
    int64_t fuel;
    int has_expected; Result expected;   /* expected==refuse -> has_expected=0 */
} Claim;

/* ---- wire.c ---- */
Val *v_int(int64_t i);
Val *v_float(int64_t n, int64_t d);
Val *v_bool(int b);
Val *v_str(char *s);
Val *v_arr(Val **xs, int n);
Val *v_cell(char **ns, Val **vs, int n);
int is_int(Val *v);
int is_bool(Val *v);
int is_str(Val *v);
int is_arr(Val *v);
int is_cell(Val *v);
int is_float(Val *v);
int val_eq(Val *a, Val *b);
int sx_claim(Sx *x, Claim *out);

/* ---- eval.c ---- */
int eval_prog(Decl *g, int ng, Leaf *o, int no, int64_t fuel,
              char *entry, NV *args, int nargs, Result *out);

/* ---- quote.c ---- */
Val *quote_prog(Prog *p);

#endif
