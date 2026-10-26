/* korufe.h — the koru surface frontend's shared contract.
   One TU per leg: util (alloc/buf), lex (real koru tokens),
   parse (surface -> AST), astio (program.ast.json canon shape +
   JSON reader), lower (ast + case row -> [flow-eval] claim), main.
   Nothing here decides semantics — refusals are the contract. */
#ifndef KORUFE_H
#define KORUFE_H

#define _CRT_SECURE_NO_WARNINGS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <stdarg.h>
#include <limits.h>

/* ---- util.c ---- */
void *xmalloc(size_t n);
char *xstrndup(const char *s, size_t n);
char *xstrdup(const char *s);
char *xasprintf(const char *a, const char *b);

typedef struct { char *p; size_t n, cap; } Buf;
void bput(Buf *b, const char *s);
void bputf(Buf *b, const char *fmt, ...);

typedef struct {
    int kind;      /* 0 ident 1 int 2 float 3 str 4 punct 5 eof 6 nl */
    char *text;
    int line;
    long pos;      /* byte offset — glued-punct adjacency (|*) */
} Tk;

typedef struct { Tk *t; int n, i; } Tks;

/* ---- lex.c ---- */
Tks *lex_k(const char *src, const char *file, char **err);
Tk *peek(Tks *s);
Tk *next_tk(Tks *s);
int at(Tks *s, const char *w);
int at_kind(Tks *s, int k);
int eat(Tks *s, const char *w);
void snl(Tks *s);
int fail_at(Tks *s, char **err, const char *msg);

/* ================= koru AST (C-side) =================
   items -> ast.json; the AST is also the lowerer's input when
   --lower runs against its own JSON — so the writer must emit
   exactly what the JSON reader reads back. */

typedef struct KExpr KExpr;
typedef struct { char *n; KExpr *e; } NArg;
struct KExpr {
    int tag;              /* 0 lit 1 var 2 bin 3 un 4 cond 5 field 6 index
                             7 builtin 8 call(invocation) */
    int64_t i, d;         /* int; float num/den */
    int b;                /* bool */
    char *s;              /* str / var / field name / call-or-builtin name */
    int op;               /* bin/un op codes (wire numbering) */
    KExpr *a, *bb, *c;
    NArg *args; int nargs;                          /* call args */
    KExpr **xs; int nxs;                              /* arr literal */
    struct { char *n; KExpr *e; } *fs; int nfs;       /* cell literal */
};

/* invocation: qname (mod/path:name dotted-or-slashed → wire keeps last
   segment as callable name; qualifier is recorded, resolution refuses
   at lower if a qualifier is present — single-module subset) */
typedef struct {
    char *qual;            /* NULL = local */
    char *name;
    NArg *args; int nargs;
    char *retbind;         /* `inv: name` — binds into the next
                              `|>` continuation arm */
} Inv;

typedef struct ArmD ArmD;
struct ArmD {
    char *branch;          /* "" bare-dispatch arm */
    int catchall;
    char *bind;
    KExpr *cond;
    int kind;              /* -1 none, 0 terminal, 1 produce, 2 ctor,
                              3 invoke, 4 jump */
    char *target;          /* ctor/invoke/jump name; jump label */
    Inv *inv;              /* invoke/jump args */
    KExpr *produce;        /* produce/ctor payload */
    ArmD **conts; int nconts;
};

typedef struct {
    char *pre;             /* #label */
    Inv *head;
    ArmD **arms; int narms;
} FlowD;

typedef struct Item Item;
struct Item {
    int kind;              /* 0 import 1 event_decl 2 impl_bare
                              3 impl_subflow 4 flow_toplevel */
    char *name;
    char *import_path;
    struct { char *n; char *t; } *fields; int nfields;   /* tor inputs */
    char **branches; int nbranches;
    char *ret_type;
    int is_pub;
    KExpr *bare;           /* impl_bare */
    char *ctor; KExpr *ctor_e;   /* impl ctor (name => b expr) */
    FlowD *flow;           /* impl_subflow / flow_toplevel */
    int line;
    Item *next;
};


/* ---- parse.c ---- */
Item *parse_program(Tks *s, char **err);
KExpr *parse_expr(Tks *s, char **err);

/* ---- astio.c ---- */
void write_ast_json(Item *items, const char *file, FILE *f);

typedef struct Jv Jv;
struct Jv {
    int k;            /* 0 null 1 bool 2 num 3 str 4 arr 5 obj */
    int b;
    double num; char *numraw;
    char *s;
    Jv **xs; int nxs;
    struct { char *k; Jv *v; } *fs; int nfs;
};

extern const char *jp;
Jv *jparse(void);
Jv *jget(Jv *o, const char *k);
char *jstr(Jv *o, const char *k);
Jv *jarr(Jv *o, const char *k);
char *jseg0(Jv *path);

/* ---- lower.c ---- */
char *pun_name(KExpr *e);
int lower(Jv *ast, Jv *cspec, Buf *out, char **err);

#endif
