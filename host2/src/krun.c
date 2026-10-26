/*
 * krun.c — host2: the koru wire checker, in C99.
 *
 * The witness twin of ISAR.FlowDialect.runK and the Role-B checker
 * of w:/src/koru's FlowCheck.lean — reading the same `[flow-eval]`
 * claim wire:
 *
 *     [flow-eval] ((entry NAME (ARGV*)) (fuel N) (result R)
 *                  (graph DECL*) (oracle LEAF*))
 *
 * Modes:
 *   krun FILE.k                re-decide the claim; print
 *                              MATCH <rsx> | DRIFT want W got G |
 *                              MALFORMED <why>
 *   krun --emit COMP.k SRC.k   parse SRC's program, quote it to a
 *                              KVal, invoke COMP's entry with
 *                              args [("src", quoted)]; print the
 *                              payload string (the emitted C) or
 *                              REFUSED.
 *
 * Faithfulness obligations — each arm mirrors its Lean arm:
 *   - floats are exact rationals num/den; d=0 refuses at asKRat;
 *     / refuses a zero quotient denominator; % on floats refuses.
 *   - `and`/`or`/`cond` short-circuit; guards must eval to bool.
 *   - env lookup = first binding wins; cell field = last wins.
 *   - fuel is a resource cap: every call frame costs one.
 *   - oracle leaves are the trust boundary; missing leaf refuses.
 *
 * Declared divergences (witness-only):
 *   - ints are int64 with CHECKED arithmetic — overflow refuses,
 *     where Lean's Int would still decide. The corpus never nears
 *     the limits; refusal-not-wrap is the honest shape.
 *   - allocation is process heap, never freed (exit cleans up).
 *
 * CompCert-subset discipline: C99 only — no VLA, no _Complex, no
 * nested functions; stdio/stdlib/string/stdint/limits/errno.
 */
#define _CRT_SECURE_NO_WARNINGS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <errno.h>

/* ================= allocation ================= */

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fprintf(stderr, "krun: out of memory\n"); exit(4); }
    return p;
}
static void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n ? n : 1);
    if (!q) { fprintf(stderr, "krun: out of memory\n"); exit(4); }
    return q;
}
static char *xstrndup(const char *s, size_t n) {
    char *p = xmalloc(n + 1);
    memcpy(p, s, n);
    p[n] = 0;
    return p;
}
static char *xstrdup(const char *s) { return xstrndup(s, strlen(s)); }

/* ================= s-expressions ================= */

typedef struct Sx {
    int is_list;            /* 0 atom, 1 list */
    char *atom;             /* quoted atoms keep their quotes */
    struct Sx **kids;
    int n;
} Sx;

static Sx *sx_atom(const char *s, size_t n) {
    Sx *x = xmalloc(sizeof(Sx));
    x->is_list = 0; x->atom = xstrndup(s, n); x->kids = 0; x->n = 0;
    return x;
}
static Sx *sx_list(Sx **kids, int n) {
    Sx *x = xmalloc(sizeof(Sx));
    x->is_list = 1; x->atom = 0; x->kids = kids; x->n = n;
    return x;
}
static int sx_is_atom(Sx *x, const char *s) {
    return x && !x->is_list && strcmp(x->atom, s) == 0;
}

/* ---- tokenizer: spaces, parens, quoted atoms (kept with quotes,
   unterminated refuses), bare atoms stop at delimiters ---- */

static int tk_space(char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\r';
}

static char *file_read_all(const char *path) {
    FILE *f = fopen(path, "rb");
    long n;
    char *buf;
    if (!f) return 0;
    fseek(f, 0, SEEK_END); n = ftell(f); fseek(f, 0, SEEK_SET);
    if (n < 0) { fclose(f); return 0; }
    buf = xmalloc((size_t)n + 1);
    if (fread(buf, 1, (size_t)n, f) != (size_t)n) { fclose(f); free(buf); return 0; }
    fclose(f); buf[n] = 0;
    return buf;
}

static int tokenize(const char *src, char ***toks_out, int *ntoks) {
    char **v = 0; int n = 0, cap = 0;
    const char *p = src;
    while (*p) {
        const char *q;
        char *t;
        if (tk_space(*p)) { p++; continue; }
        if (*p == '#') {                     /* comment to end of line */
            while (*p && *p != '\n') p++;
            continue;
        }
        if (*p == '(' || *p == ')') {
            t = xstrndup(p, 1); p++;
        } else if (*p == '"') {
            q = p + 1;
            while (*q && *q != '"') q++;
            if (!*q) return 0;      /* unterminated quote refuses */
            q++;
            t = xstrndup(p, (size_t)(q - p)); p = q;
        } else {
            q = p;
            while (*q && !tk_space(*q) && *q != '(' && *q != ')' && *q != '"')
                q++;
            t = xstrndup(p, (size_t)(q - p)); p = q;
        }
        if (n == cap) { cap = cap ? cap * 2 : 64; v = xrealloc(v, cap * sizeof(char *)); }
        v[n++] = t;
    }
    *toks_out = v; *ntoks = n;
    return 1;
}

/* ---- parser: one sexpr, trailing tokens must be exhausted ---- */

typedef struct { char **toks; int n; int i; } PState;

static Sx *parse_sx(PState *st) {
    char *t;
    if (st->i >= st->n) return 0;
    t = st->toks[st->i];
    if (strcmp(t, "(") == 0) {
        Sx **kids = 0; int n = 0, cap = 0;
        st->i++;
        for (;;) {
            Sx *k;
            if (st->i >= st->n) return 0;   /* unbalanced ( */
            if (strcmp(st->toks[st->i], ")") == 0) { st->i++; break; }
            k = parse_sx(st);
            if (!k) return 0;
            if (n == cap) { cap = cap ? cap * 2 : 8; kids = xrealloc(kids, cap * sizeof(Sx *)); }
            kids[n++] = k;
        }
        return sx_list(kids, n);
    }
    if (strcmp(t, ")") == 0) return 0;
    st->i++;
    return sx_atom(t, strlen(t));
}

static Sx *parse_top(const char *line) {
    char **toks = 0; int n = 0;
    PState st; Sx *x;
    if (!tokenize(line, &toks, &n)) return 0;
    st.toks = toks; st.n = n; st.i = 0;
    /* optional [flow-eval] marker atom */
    if (st.i < st.n && strcmp(st.toks[st.i], "[flow-eval]") == 0) st.i++;
    x = parse_sx(&st);
    if (!x || st.i != st.n) return 0;
    if (!x->is_list) return 0;                 /* claim must be a list */
    return x;
}

/* ================= values ================= */

typedef struct Val Val;
struct Val {
    int tag;                /* 0 int, 1 float(n,d), 2 bool, 3 str, 4 arr, 5 cell */
    int64_t i, d;
    int b;
    char *s;
    Val **xs; int nx;       /* arr */
    char **ns; Val **vs; int nf;  /* cell */
};

static Val *v_new(int tag) { Val *v = xmalloc(sizeof(Val)); memset(v, 0, sizeof *v); v->tag = tag; return v; }
static Val *v_int(int64_t i) { Val *v = v_new(0); v->i = i; return v; }
static Val *v_float(int64_t n, int64_t d) { Val *v = v_new(1); v->i = n; v->d = d; return v; }
static Val *v_bool(int b) { Val *v = v_new(2); v->b = b; return v; }
static Val *v_str(char *s) { Val *v = v_new(3); v->s = s; return v; }
static Val *v_arr(Val **xs, int n) { Val *v = v_new(4); v->xs = xs; v->nx = n; return v; }
static Val *v_cell(char **ns, Val **vs, int n) { Val *v = v_new(5); v->ns = ns; v->vs = vs; v->nf = n; return v; }

static int is_int(Val *v) { return v && v->tag == 0; }
static int is_bool(Val *v) { return v && v->tag == 2; }
static int is_str(Val *v) { return v && v->tag == 3; }
static int is_arr(Val *v) { return v && v->tag == 4; }
static int is_cell(Val *v) { return v && v->tag == 5; }
static int is_float(Val *v) { return v && v->tag == 1; }

/* structural equality — kvalBEq twin: floats compare num/den
   pairwise (NOT rational equality), cells order-sensitively */
static int val_eq(Val *a, Val *b) {
    int i;
    if (!a || !b) return 0;
    if (a->tag != b->tag) return 0;
    switch (a->tag) {
    case 0: return a->i == b->i;
    case 1: return a->i == b->i && a->d == b->d;
    case 2: return a->b == b->b;
    case 3: return strcmp(a->s, b->s) == 0;
    case 4:
        if (a->nx != b->nx) return 0;
        for (i = 0; i < a->nx; i++)
            if (!val_eq(a->xs[i], b->xs[i])) return 0;
        return 1;
    case 5:
        if (a->nf != b->nf) return 0;
        for (i = 0; i < a->nf; i++)
            if (strcmp(a->ns[i], b->ns[i]) || !val_eq(a->vs[i], b->vs[i])) return 0;
        return 1;
    }
    return 0;
}

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

/* ================= decoders: Sx -> AST, refusal = NULL/0 =================
   Mirror of FlowCheck's sxVal / sxExpr / sxArmNode / sxArmFields /
   sxArm / sxFlowBody / sxDecl / sxNamed / sxLeaf / sxThunkResult /
   sxExpected / claimFields — same refusal discipline: malformed
   structure is a rejection, never an approximation; duplicated
   claim fields refuse. */

static int sx_int(const char *s, int64_t *out) {
    /* sxInt: optional '-', then digits; refuse empty/non-numeric/overflow */
    const char *p = s;
    int neg = 0;
    if (*p == '-') { neg = 1; p++; }
    if (!*p) return 0;
    {
        int64_t v = 0;
        while (*p) {
            int dgt;
            if (*p < '0' || *p > '9') return 0;
            dgt = *p - '0';
            if (v > (INT64_MAX - dgt) / 10) return 0;
            v = v * 10 + dgt;
            p++;
        }
        if (neg) {
            if (v == INT64_MIN) return 0;   /* |INT64_MIN| unrepresentable */
            v = -v;
        }
        *out = v;
        return 1;
    }
}

static int sx_name(Sx *x, char **out) {
    /* bare atom — quoted atoms refuse as names */
    if (!x || x->is_list || x->atom[0] == '"') return 0;
    *out = x->atom;
    return 1;
}

static int sx_str(Sx *x, char **out) {
    /* quoted atom, quotes stripped — no escapes */
    size_t n;
    if (!x || x->is_list) return 0;
    n = strlen(x->atom);
    if (n < 2 || x->atom[0] != '"' || x->atom[n - 1] != '"') return 0;
    *out = xstrndup(x->atom + 1, n - 2);
    return 1;
}

static int sx_binop(const char *s) {
    static const char *ops[] = {
        "add","sub","mul","div","mod","eq","ne","lt","le","gt","ge",
        "and","or","concat" };
    int i;
    for (i = 0; i < 14; i++) if (strcmp(s, ops[i]) == 0) return i;
    return -1;
}

static int sx_unop(const char *s) {
    if (strcmp(s, "neg") == 0) return 0;
    if (strcmp(s, "not") == 0) return 1;
    return -1;
}

static Expr *e_new(int tag) { Expr *e = xmalloc(sizeof(Expr)); memset(e, 0, sizeof *e); e->tag = tag; return e; }

static Val *sx_val(Sx *x);
static Expr *sx_expr(Sx *x);
static int sx_named_val(Sx *x, NV *out);
static int sx_named_expr(Sx *x, NE *out);
static Arm *sx_arm(Sx *x);

static Val *sx_val(Sx *x) {
    if (!x || !x->is_list || x->n == 0) return 0;
    {
        Sx *h = x->kids[0];
        if (sx_is_atom(h, "int") && x->n == 2) {
            int64_t i;
            if (!x->kids[1] || x->kids[1]->is_list || x->kids[1]->atom[0] == '"')
                return 0;
            if (!sx_int(x->kids[1]->atom, &i)) return 0;
            return v_int(i);
        }
        if (sx_is_atom(h, "float") && x->n == 3) {
            int64_t n, d;
            if (x->kids[1]->is_list || x->kids[2]->is_list) return 0;
            if (!sx_int(x->kids[1]->atom, &n) || !sx_int(x->kids[2]->atom, &d)) return 0;
            if (d == 0) return 0;
            return v_float(n, d);
        }
        if (sx_is_atom(h, "bool") && x->n == 2) {
            if (sx_is_atom(x->kids[1], "true")) return v_bool(1);
            if (sx_is_atom(x->kids[1], "false")) return v_bool(0);
            return 0;
        }
        if (sx_is_atom(h, "str") && x->n == 2) {
            char *s;
            if (!sx_str(x->kids[1], &s)) return 0;
            return v_str(s);
        }
        if (sx_is_atom(h, "arr")) {
            int i, n = x->n - 1;
            Val **xs = n ? xmalloc(n * sizeof(Val *)) : 0;
            for (i = 0; i < n; i++) {
                xs[i] = sx_val(x->kids[i + 1]);
                if (!xs[i]) return 0;
            }
            return v_arr(xs, n);
        }
        if (sx_is_atom(h, "cell")) {
            int i, n = x->n - 1;
            char **ns = n ? xmalloc(n * sizeof(char *)) : 0;
            Val **vs = n ? xmalloc(n * sizeof(Val *)) : 0;
            for (i = 0; i < n; i++) {
                Sx *f = x->kids[i + 1];
                if (!f || !f->is_list || f->n != 2) return 0;
                if (f->kids[0]->is_list) return 0;
                ns[i] = f->kids[0]->atom;
                vs[i] = sx_val(f->kids[1]);
                if (!vs[i]) return 0;
            }
            return v_cell(ns, vs, n);
        }
    }
    return 0;
}

static Expr *sx_expr(Sx *x) {
    if (!x || !x->is_list || x->n == 0) return 0;
    {
        Sx *h = x->kids[0];
        if (sx_is_atom(h, "lit") && x->n == 2) {
            Val *v = sx_val(x->kids[1]);
            Expr *e;
            if (!v) return 0;
            e = e_new(0); e->lit = v; return e;
        }
        if (sx_is_atom(h, "var") && x->n == 2) {
            Expr *e = e_new(1);
            if (!sx_name(x->kids[1], &e->name)) return 0;
            return e;
        }
        if (sx_is_atom(h, "bin") && x->n == 4) {
            int op; Expr *e, *a, *b;
            if (x->kids[1]->is_list || x->kids[1]->atom[0] == '"') return 0;
            op = sx_binop(x->kids[1]->atom);
            if (op < 0) return 0;
            a = sx_expr(x->kids[2]); b = sx_expr(x->kids[3]);
            if (!a || !b) return 0;
            e = e_new(2); e->op = op; e->a = a; e->b = b; return e;
        }
        if (sx_is_atom(h, "un") && x->n == 3) {
            int op; Expr *e, *a;
            if (x->kids[1]->is_list || x->kids[1]->atom[0] == '"') return 0;
            op = sx_unop(x->kids[1]->atom);
            if (op < 0) return 0;
            a = sx_expr(x->kids[2]);
            if (!a) return 0;
            e = e_new(3); e->op = op; e->a = a; return e;
        }
        if (sx_is_atom(h, "cond") && x->n == 4) {
            Expr *e = e_new(4);
            e->a = sx_expr(x->kids[1]);
            e->b = sx_expr(x->kids[2]);
            e->c = sx_expr(x->kids[3]);
            if (!e->a || !e->b || !e->c) return 0;
            return e;
        }
        if (sx_is_atom(h, "field") && x->n == 3) {
            Expr *e = e_new(5);
            e->a = sx_expr(x->kids[1]);
            if (!e->a) return 0;
            if (!sx_name(x->kids[2], &e->name)) return 0;
            return e;
        }
        if (sx_is_atom(h, "index") && x->n == 3) {
            Expr *e = e_new(6);
            e->a = sx_expr(x->kids[1]);
            e->b = sx_expr(x->kids[2]);
            if (!e->a || !e->b) return 0;
            return e;
        }
        if (sx_is_atom(h, "builtin") && x->n >= 2) {
            Expr *e = e_new(7);
            int i;
            if (!sx_name(x->kids[1], &e->name)) return 0;
            e->nargs = x->n - 2;
            e->args = e->nargs ? xmalloc(e->nargs * sizeof(Expr *)) : 0;
            for (i = 0; i < e->nargs; i++) {
                e->args[i] = sx_expr(x->kids[i + 2]);
                if (!e->args[i]) return 0;
            }
            return e;
        }
    }
    return 0;
}

static int sx_named_val(Sx *x, NV *out) {
    if (!x || !x->is_list || x->n != 2 || x->kids[0]->is_list) return 0;
    out->n = x->kids[0]->atom;
    out->v = sx_val(x->kids[1]);
    return out->v != 0;
}

static int sx_named_expr(Sx *x, NE *out) {
    if (!x || !x->is_list || x->n != 2 || x->kids[0]->is_list) return 0;
    out->n = x->kids[0]->atom;
    out->e = sx_expr(x->kids[1]);
    return out->e != 0;
}

static NE *sx_named_expr_list(Sx **xs, int n) {
    NE *out = n ? xmalloc(n * sizeof(NE)) : 0;
    int i;
    for (i = 0; i < n; i++)
        if (!sx_named_expr(xs[i], &out[i])) return 0;
    return out;
}

/* arm node: terminal | (jump N NE*) | (invoke N NE*) | (produce E) |
   (ctor N E) */
static int sx_armnode_into(Sx *x, Arm *a) {
    if (sx_is_atom(x, "terminal")) { a->ntag = 0; return 1; }
    if (!x || !x->is_list || x->n == 0) return 0;
    {
        Sx *h = x->kids[0];
        if ((sx_is_atom(h, "jump") || sx_is_atom(h, "invoke")) && x->n >= 2) {
            if (!sx_name(x->kids[1], &a->ntarget)) return 0;
            a->ntag = sx_is_atom(h, "jump") ? 1 : 2;
            a->nnargs = x->n - 2;
            a->nargs = sx_named_expr_list(x->kids + 2, a->nnargs);
            if (!a->nargs && a->nnargs) return 0;
            return 1;
        }
        if (sx_is_atom(h, "produce") && x->n == 2) {
            a->nexpr = sx_expr(x->kids[1]);
            if (!a->nexpr) return 0;
            a->ntag = 3; return 1;
        }
        if (sx_is_atom(h, "ctor") && x->n == 3) {
            if (!sx_name(x->kids[1], &a->ntarget)) return 0;
            a->nexpr = sx_expr(x->kids[2]);
            if (!a->nexpr) return 0;
            a->ntag = 4; return 1;
        }
    }
    return 0;
}

static Arm **sx_arm_list(Sx **xs, int n) {
    Arm **out = n ? xmalloc(n * sizeof(Arm *)) : 0;
    int i;
    for (i = 0; i < n; i++) {
        out[i] = sx_arm(xs[i]);
        if (!out[i]) return 0;
    }
    return out;
}

/* (arm FIELD*) — order-free, each field at most once;
   catchall => branch "*" + flag. */
static Arm *sx_arm(Sx *x) {
    Arm *a;
    int i;
    if (!x || !x->is_list || x->n == 0 || !sx_is_atom(x->kids[0], "arm"))
        return 0;
    a = xmalloc(sizeof(Arm));
    memset(a, 0, sizeof *a);
    a->branch = "";
    a->ntag = -1;
    for (i = 1; i < x->n; i++) {
        Sx *f = x->kids[i];
        if (f->is_list && f->n == 2 && sx_is_atom(f->kids[0], "tag")) {
            char *n;
            if (a->branch[0] || !sx_name(f->kids[1], &n)) return 0;
            a->branch = n;
        } else if (!f->is_list && strcmp(f->atom, "catchall") == 0) {
            if (a->catchall || a->branch[0]) return 0;
            a->branch = "*"; a->catchall = 1;
        } else if (f->is_list && f->n == 2 && sx_is_atom(f->kids[0], "bind")) {
            char *n;
            if (a->bind || !sx_name(f->kids[1], &n)) return 0;
            a->bind = n;
        } else if (f->is_list && f->n == 2 && sx_is_atom(f->kids[0], "when")) {
            if (a->cond) return 0;
            a->cond = sx_expr(f->kids[1]);
            if (!a->cond) return 0;
        } else if (f->is_list && f->n == 2 && sx_is_atom(f->kids[0], "node")) {
            if (a->ntag != -1) return 0;
            if (!sx_armnode_into(f->kids[1], a)) return 0;
        } else if (f->is_list && f->n >= 1 && sx_is_atom(f->kids[0], "conts")) {
            if (a->conts) return 0;
            a->nconts = f->n - 1;
            a->conts = sx_arm_list(f->kids + 1, a->nconts);
            if (!a->conts && a->nconts) return 0;
        } else {
            return 0;
        }
    }
    return a;
}

/* ((label L))? (head NAME NE*) ARM* */
static Flow *sx_flow_body(Sx **xs, int n) {
    Flow *f = xmalloc(sizeof(Flow));
    int i = 0;
    memset(f, 0, sizeof *f);
    if (n >= 1 && xs[0]->is_list && xs[0]->n == 2 &&
        sx_is_atom(xs[0]->kids[0], "label")) {
        if (!sx_name(xs[0]->kids[1], &f->pre)) return 0;
        i = 1;
    }
    if (i >= n) return 0;
    {
        Sx *h = xs[i];
        if (!h->is_list || h->n < 2 || !sx_is_atom(h->kids[0], "head")) return 0;
        if (!sx_name(h->kids[1], &f->hname)) return 0;
        f->nhargs = h->n - 2;
        f->hargs = sx_named_expr_list(h->kids + 2, f->nhargs);
        if (!f->hargs && f->nhargs) return 0;
        i++;
    }
    f->narms = n - i;
    f->arms = sx_arm_list(xs + i, f->narms);
    if (!f->arms && f->narms) return 0;
    return f;
}

static int sx_decl(Sx *x, Decl *out) {
    Callable *c;
    if (!x || !x->is_list || x->n != 3 || !sx_is_atom(x->kids[0], "def"))
        return 0;
    if (!sx_name(x->kids[1], &out->n)) return 0;
    c = xmalloc(sizeof(Callable));
    memset(c, 0, sizeof *c);
    out->c = c;
    if (sx_is_atom(x->kids[2], "thunk")) { c->t = 1; return 1; }
    {
        Sx *b = x->kids[2];
        if (!b->is_list || b->n < 1) return 0;
        if (sx_is_atom(b->kids[0], "bare") && b->n == 2) {
            c->bare = sx_expr(b->kids[1]);
            if (!c->bare) return 0;
            c->t = 0; return 1;
        }
        if (sx_is_atom(b->kids[0], "subflow")) {
            c->flow = sx_flow_body(b->kids + 1, b->n - 1);
            if (!c->flow) return 0;
            c->t = 2; return 1;
        }
    }
    return 0;
}

/* thunk-result: (void)|(bare V)|(tag N)|(tag N V) — refuse NOT allowed */
static int sx_thunk_result(Sx *x, Result *r) {
    r->branch = 0; r->payload = 0;
    if (!x || !x->is_list || x->n == 0) return 0;
    if (sx_is_atom(x->kids[0], "void") && x->n == 1) return 1;
    if (sx_is_atom(x->kids[0], "bare") && x->n == 2) {
        r->payload = sx_val(x->kids[1]);
        return r->payload != 0;
    }
    if (sx_is_atom(x->kids[0], "tag") && (x->n == 2 || x->n == 3)) {
        if (!sx_name(x->kids[1], &r->branch)) return 0;
        if (x->n == 3) {
            r->payload = sx_val(x->kids[2]);
            return r->payload != 0;
        }
        return 1;
    }
    return 0;
}

static int sx_leaf(Sx *x, Leaf *out) {
    if (!x || !x->is_list || x->n != 4 || !sx_is_atom(x->kids[0], "leaf"))
        return 0;
    if (!sx_name(x->kids[1], &out->name)) return 0;
    {
        Sx *args = x->kids[2];
        int i;
        if (!args->is_list) return 0;
        out->nargs = args->n;
        out->args = args->n ? xmalloc(args->n * sizeof(NV)) : 0;
        for (i = 0; i < args->n; i++)
            if (!sx_named_val(args->kids[i], &out->args[i])) return 0;
    }
    return sx_thunk_result(x->kids[3], &out->r);
}

/* claim fields: order-free, each exactly once; `residue` is a real
   FlowCheck field we do not model — refuse it, name the axis. */
static int sx_claim(Sx *x, Claim *out) {
    int i;
    int have_entry = 0, have_fuel = 0, have_result = 0,
        have_graph = 0, have_oracle = 0;
    memset(out, 0, sizeof *out);
    if (!x || !x->is_list) return 0;
    for (i = 0; i < x->n; i++) {
        Sx *f = x->kids[i];
        if (!f->is_list || f->n < 1 || f->kids[0]->is_list) return 0;
        if (sx_is_atom(f->kids[0], "entry") && f->n >= 2) {
            int j;
            if (have_entry) return 0;
            if (!sx_name(f->kids[1], &out->prog.entry)) return 0;
            out->prog.nargs = f->n - 2;
            out->prog.args = out->prog.nargs ?
                xmalloc(out->prog.nargs * sizeof(NV)) : 0;
            for (j = 0; j < out->prog.nargs; j++)
                if (!sx_named_val(f->kids[j + 2], &out->prog.args[j])) return 0;
            have_entry = 1;
        } else if (sx_is_atom(f->kids[0], "fuel") && f->n == 2) {
            int64_t n;
            if (have_fuel) return 0;
            if (f->kids[1]->is_list || f->kids[1]->atom[0] == '"') return 0;
            if (!sx_int(f->kids[1]->atom, &n) || n < 0) return 0;
            out->fuel = n;
            have_fuel = 1;
        } else if (sx_is_atom(f->kids[0], "result") && f->n == 2) {
            if (have_result) return 0;
            if (sx_is_atom(f->kids[1], "refuse")) {
                out->has_expected = 0;
            } else {
                out->has_expected = 1;
                if (!sx_thunk_result(f->kids[1], &out->expected)) return 0;
            }
            have_result = 1;
        } else if (sx_is_atom(f->kids[0], "graph")) {
            int j;
            if (have_graph) return 0;
            out->prog.ng = f->n - 1;
            out->prog.graph = out->prog.ng ?
                xmalloc(out->prog.ng * sizeof(Decl)) : 0;
            for (j = 0; j < out->prog.ng; j++)
                if (!sx_decl(f->kids[j + 1], &out->prog.graph[j])) return 0;
            have_graph = 1;
        } else if (sx_is_atom(f->kids[0], "oracle")) {
            int j;
            if (have_oracle) return 0;
            out->noracle = f->n - 1;
            out->oracle = out->noracle ?
                xmalloc(out->noracle * sizeof(Leaf)) : 0;
            for (j = 0; j < out->noracle; j++)
                if (!sx_leaf(f->kids[j + 1], &out->oracle[j])) return 0;
            have_oracle = 1;
        } else {
            /* unknown claim field — includes (residue ...) */
            return 0;
        }
    }
    return have_entry && have_fuel && have_result && have_graph && have_oracle;
}

/* ================= evaluator — the runK twin =================
   int64 arithmetic is CHECKED: overflow refuses where Lean's Int
   would still decide (declared witness divergence, corpus-safe). */

static int ck_add(int64_t a, int64_t b, int64_t *o) {
    if ((b > 0 && a > INT64_MAX - b) || (b < 0 && a < INT64_MIN - b)) return 0;
    *o = a + b; return 1;
}
static int ck_sub(int64_t a, int64_t b, int64_t *o) {
    if ((b < 0 && a > INT64_MAX + b) || (b > 0 && a < INT64_MIN + b)) return 0;
    *o = a - b; return 1;
}
static int ck_mul(int64_t a, int64_t b, int64_t *o) {
    int64_t r;
    if (a > 0) {
        if (b > 0) { if (a > INT64_MAX / b) return 0; }
        else { if (b < INT64_MIN / a) return 0; }
    } else if (a < 0) {
        if (b > 0) { if (a < INT64_MIN / b) return 0; }
        else { if (b < 0 && (a == -1 || b == -1 || a < INT64_MAX / b)) return 0; }
    }
    r = a * b; *o = r; return 1;
}
static int ck_neg(int64_t a, int64_t *o) {
    if (a == INT64_MIN) return 0;
    *o = -a; return 1;
}

/* zig divTrunc/rem/@mod on i64 — trunc toward zero / floor */
static int ktdiv(int64_t a, int64_t b, int64_t *o) {
    uint64_t q, ua, ub;
    int neg;
    if (b == 0 || (a == INT64_MIN && b == -1)) return 0;
    neg = (a < 0) != (b < 0);
    ua = a < 0 ? (uint64_t)(-(a + 1)) + 1 : (uint64_t)a;
    ub = b < 0 ? (uint64_t)(-(b + 1)) + 1 : (uint64_t)b;
    q = ua / ub;
    if (neg) {
        if (q > (uint64_t)INT64_MAX + 1) return 0;
        *o = -(int64_t)q;
    } else {
        if (q > (uint64_t)INT64_MAX) return 0;
        *o = (int64_t)q;
    }
    return 1;
}
static int ktmod(int64_t a, int64_t b, int64_t *o) {
    int64_t q, qb;
    if (!ktdiv(a, b, &q)) return 0;
    if (!ck_mul(q, b, &qb)) return 0;
    return ck_sub(a, qb, o);
}
static int kfmod(int64_t a, int64_t b, int64_t *o) {
    /* @mod twin: floor modulus — r = a - floorDiv(a,b)*b, i.e. trunc
       remainder adjusted when signs differ */
    int64_t q, r, qb;
    if (!ktdiv(a, b, &q)) return 0;
    if (!ck_mul(q, b, &qb) || !ck_sub(a, qb, &r)) return 0;
    if (r != 0 && ((r < 0) != (b < 0))) {
        if (!ck_sub(q, 1, &q) || !ck_mul(q, b, &qb)) return 0;
        return ck_sub(a, qb, o);
    }
    *o = r;
    return 1;
}

/* asKRat twin */
static int as_krat(Val *v, int64_t *n, int64_t *d) {
    if (is_float(v)) {
        if (v->d == 0) return 0;
        if (v->d < 0) {
            int64_t nn;
            if (!ck_neg(v->i, &nn) || v->d == INT64_MIN) return 0;
            *n = nn; *d = -v->d;
            return 1;
        }
        *n = v->i; *d = v->d;
        return 1;
    }
    if (is_int(v)) { *n = v->i; *d = 1; return 1; }
    return 0;
}

static Val *kfloat_bin(int op, int64_t n1, int64_t d1, int64_t n2, int64_t d2) {
    int64_t x = 0, y = 0, z;
    if (op != 2 && op != 3) {   /* cross-compare numerator terms */
        if (!ck_mul(n1, d2, &x) || !ck_mul(n2, d1, &y)) return 0;
    }
    switch (op) {
    case 0:  /* add */
        if (!ck_add(x, y, &z) || !ck_mul(d1, d2, &d1)) return 0;
        return v_float(z, d1);
    case 1:
        if (!ck_sub(x, y, &z) || !ck_mul(d1, d2, &d1)) return 0;
        return v_float(z, d1);
    case 2:
        if (!ck_mul(n1, n2, &x) || !ck_mul(d1, d2, &y)) return 0;
        return v_float(x, y);
    case 3:
        if (d1 == 0 || n2 == 0) return 0;
        if (!ck_mul(n1, d2, &x) || !ck_mul(d1, n2, &y)) return 0;
        return v_float(x, y);
    case 4: return 0;                        /* mod on floats refuses */
    case 5: return v_bool(x == y);
    case 6: return v_bool(x != y);
    case 7: return v_bool(x < y);
    case 8: return v_bool(x <= y);
    case 9: return v_bool(x > y);
    case 10: return v_bool(x >= y);
    }
    return 0;
}

static Val *eval_kbin(int op, Val *a, Val *b) {
    int64_t x;
    if (is_float(a) || is_float(b)) {
        int64_t n1, d1, n2, d2;
        if (!as_krat(a, &n1, &d1) || !as_krat(b, &n2, &d2)) return 0;
        return kfloat_bin(op, n1, d1, n2, d2);
    }
    if (is_int(a) && is_int(b)) {
        switch (op) {
        case 0: if (!ck_add(a->i, b->i, &x)) return 0; return v_int(x);
        case 1: if (!ck_sub(a->i, b->i, &x)) return 0; return v_int(x);
        case 2: if (!ck_mul(a->i, b->i, &x)) return 0; return v_int(x);
        case 3: if (!ktdiv(a->i, b->i, &x)) return 0; return v_int(x);
        case 4: if (!ktmod(a->i, b->i, &x)) return 0; return v_int(x);
        case 5: return v_bool(a->i == b->i);
        case 6: return v_bool(a->i != b->i);
        case 7: return v_bool(a->i < b->i);
        case 8: return v_bool(a->i <= b->i);
        case 9: return v_bool(a->i > b->i);
        case 10: return v_bool(a->i >= b->i);
        }
        return 0;
    }
    if (is_bool(a) && is_bool(b)) {
        if (op == 5) return v_bool(a->b == b->b);
        if (op == 6) return v_bool(a->b != b->b);
        return 0;
    }
    if (is_str(a) && is_str(b)) {
        if (op == 5) return v_bool(strcmp(a->s, b->s) == 0);
        if (op == 6) return v_bool(strcmp(a->s, b->s) != 0);
        if (op == 13) {
            size_t na = strlen(a->s), nb = strlen(b->s);
            char *s = xmalloc(na + nb + 1);
            memcpy(s, a->s, na); memcpy(s + na, b->s, nb + 1);
            return v_str(s);
        }
        return 0;
    }
    return 0;
}

static Val *eval_kun(int op, Val *v) {
    int64_t n;
    if (op == 1 && is_bool(v)) return v_bool(!v->b);
    if (op == 0 && is_int(v)) {
        if (!ck_neg(v->i, &n)) return 0;
        return v_int(n);
    }
    if (op == 0 && is_float(v)) {
        if (!ck_neg(v->i, &n)) return 0;
        return v_float(n, v->d);
    }
    return 0;
}

static Val *eval_ke(NV *env, int nenv, Expr *e);

static Val *eval_kbuiltin(NV *env, int nenv, char *name, Expr **args, int nargs) {
    Val *va, *vb;
    int64_t x;
    if (strcmp(name, "as") == 0 && nargs == 2)
        return eval_ke(env, nenv, args[1]);
    if ((strcmp(name, "intCast") == 0 || strcmp(name, "truncate") == 0) && nargs == 1) {
        va = eval_ke(env, nenv, args[0]);
        return is_int(va) ? va : 0;
    }
    if ((strcmp(name, "divTrunc") == 0 || strcmp(name, "rem") == 0 ||
         strcmp(name, "mod") == 0) && nargs == 2) {
        va = eval_ke(env, nenv, args[0]);
        vb = eval_ke(env, nenv, args[1]);
        if (!is_int(va) || !is_int(vb)) return 0;
        if (strcmp(name, "divTrunc") == 0) {
            if (!ktdiv(va->i, vb->i, &x)) return 0;
        } else if (strcmp(name, "rem") == 0) {
            if (!ktmod(va->i, vb->i, &x)) return 0;
        } else {
            if (!kfmod(va->i, vb->i, &x)) return 0;
        }
        return v_int(x);
    }
    if (strcmp(name, "len") == 0 && nargs == 1) {
        va = eval_ke(env, nenv, args[0]);
        return is_arr(va) ? v_int(va->nx) : 0;
    }
    if (strcmp(name, "intToString") == 0 && nargs == 1) {
        char buf[24];
        va = eval_ke(env, nenv, args[0]);
        if (!is_int(va)) return 0;
        snprintf(buf, sizeof buf, "%lld", (long long)va->i);
        return v_str(xstrdup(buf));
    }
    return 0;
}

static Val *eval_ke(NV *env, int nenv, Expr *e) {
    int i;
    switch (e->tag) {
    case 0: return e->lit;
    case 1:
        for (i = 0; i < nenv; i++)
            if (strcmp(env[i].n, e->name) == 0) return env[i].v;
        return 0;
    case 2: {   /* bin */
        Val *va, *vb;
        if (e->op == 11) {      /* and — short-circuit */
            va = eval_ke(env, nenv, e->a);
            if (!is_bool(va)) return 0;
            if (!va->b) return v_bool(0);
            vb = eval_ke(env, nenv, e->b);
            return is_bool(vb) ? vb : 0;
        }
        if (e->op == 12) {      /* or — short-circuit */
            va = eval_ke(env, nenv, e->a);
            if (!is_bool(va)) return 0;
            if (va->b) return v_bool(1);
            vb = eval_ke(env, nenv, e->b);
            return is_bool(vb) ? vb : 0;
        }
        va = eval_ke(env, nenv, e->a);
        vb = eval_ke(env, nenv, e->b);
        if (!va || !vb) return 0;
        return eval_kbin(e->op, va, vb);
    }
    case 3: {
        Val *va = eval_ke(env, nenv, e->a);
        return va ? eval_kun(e->op, va) : 0;
    }
    case 4: {   /* cond */
        Val *vc = eval_ke(env, nenv, e->a);
        if (vc && is_bool(vc))
            return eval_ke(env, nenv, vc->b ? e->b : e->c);
        return 0;
    }
    case 5: {   /* field — last binding wins */
        Val *vo = eval_ke(env, nenv, e->a);
        if (!is_cell(vo)) return 0;
        for (i = vo->nf - 1; i >= 0; i--)
            if (strcmp(vo->ns[i], e->name) == 0) return vo->vs[i];
        return 0;
    }
    case 6: {   /* index */
        Val *vo = eval_ke(env, nenv, e->a);
        Val *vi = eval_ke(env, nenv, e->b);
        if (!is_arr(vo) || !is_int(vi)) return 0;
        if (vi->i < 0 || vi->i >= vo->nx) return 0;
        return vo->xs[vi->i];
    }
    case 7:
        return eval_kbuiltin(env, nenv, e->name, e->args, e->nargs);
    }
    return 0;
}

static NV *eval_kargs(NV *env, int nenv, NE *as_, int n) {
    NV *out = n ? xmalloc(n * sizeof(NV)) : 0;
    int i;
    for (i = 0; i < n; i++) {
        out[i].n = as_[i].n;
        out[i].v = eval_ke(env, nenv, as_[i].e);
        if (!out[i].v) return 0;
    }
    return out;
}

/* outcomes: tagged struct by value; tag 0 = refuse */
typedef struct {
    int t;                /* 0 refuse, 1 result, 2 jump, 3 done, 4 skip */
    Result r;
    char *lbl;
    NV *jargs; int nj;
} Outc;

static Outc outc(int t) { Outc o; memset(&o, 0, sizeof o); o.t = t; return o; }
static Outc outc_res(Result r) { Outc o = outc(1); o.r = r; return o; }

typedef struct {
    int tag;              /* 0 invoke 1 flow 2 loop 3 dtag 4 dbare 5 armtry 6 armwalk */
    char *name; NV *args; int nargs;
    Flow *fl;
    NV *env; int nenv;
    NV *hargs; int nhargs;
    Arm **arms; int narms;
    char *branch;
    Arm *arm;
    Result res;
} Call;

static Outc run_k(Decl *g, int ng, Leaf *o, int no, int64_t fuel, Call c) {
    int i;
    if (fuel <= 0) return outc(0);
    fuel--;

    if (c.tag == 0) {       /* invoke */
        Callable *cb = 0;
        for (i = 0; i < ng; i++)
            if (strcmp(g[i].n, c.name) == 0) { cb = g[i].c; break; }
        if (!cb) return outc(0);
        if (cb->t == 1) {   /* thunk — oracle boundary */
            int j;
            for (j = 0; j < no; j++)
                if (strcmp(o[j].name, c.name) == 0) {
                    int k, ok = o[j].nargs == c.nargs;
                    for (k = 0; ok && k < c.nargs; k++)
                        ok = strcmp(o[j].args[k].n, c.args[k].n) == 0
                          && val_eq(o[j].args[k].v, c.args[k].v);
                    if (ok) return outc_res(o[j].r);
                }
            return outc(0);
        }
        if (cb->t == 0) {   /* bare */
            Val *v = eval_ke(c.args, c.nargs, cb->bare);
            if (!v) return outc(0);
            { Result r = {0, v}; return outc_res(r); }
        }
        {   /* subflow */
            Call n;
            memset(&n, 0, sizeof n);
            n.tag = 1;
            n.fl = cb->flow; n.args = c.args; n.nargs = c.nargs;
            return run_k(g, ng, o, no, fuel, n);
        }
    }

    if (c.tag == 1) {       /* flow */
        NV *hargs = eval_kargs(c.args, c.nargs, c.fl->hargs, c.fl->nhargs);
        Call n;
        if (!hargs && c.fl->nhargs) return outc(0);
        memset(&n, 0, sizeof n);
        n.tag = 2; n.fl = c.fl; n.env = c.args; n.nenv = c.nargs;
        n.hargs = hargs; n.nhargs = c.fl->nhargs;
        return run_k(g, ng, o, no, fuel, n);
    }

    if (c.tag == 2) {       /* loop */
        Outc inner, d;
        {
            Call n = {0};
            n.tag = 0; n.name = c.fl->hname;
            n.args = c.hargs; n.nargs = c.nhargs;
            inner = run_k(g, ng, o, no, fuel, n);
        }
        if (inner.t != 1) return outc(0);
        if (c.fl->narms == 0) return inner;
        {
            Call n = {0};
            n.env = c.env; n.nenv = c.nenv;
            n.arms = c.fl->arms; n.narms = c.fl->narms;
            n.res = inner.r;
            if (inner.r.branch) {
                n.tag = 3; n.branch = inner.r.branch;
            } else {
                n.tag = 4;
            }
            d = run_k(g, ng, o, no, fuel, n);
        }
        if (d.t == 0 || d.t == 4) return outc(0);
        if (d.t == 3) { Result r = {0, 0}; return outc_res(r); }
        if (d.t == 2) {     /* jump */
            if (c.fl->pre && strcmp(c.fl->pre, d.lbl) == 0) {
                Call n = {0};
                n.tag = 2; n.fl = c.fl; n.env = c.env; n.nenv = c.nenv;
                n.hargs = d.jargs; n.nhargs = d.nj;
                return run_k(g, ng, o, no, fuel, n);
            }
            return outc(0);
        }
        return d;
    }

    if (c.tag == 3) {       /* dispatchTag */
        for (i = 0; i < c.narms; i++) {
            Arm *a = c.arms[i];
            Outc o1;
            Call n = {0};
            if (strcmp(a->branch, c.branch) != 0) continue;
            n.tag = 5; n.env = c.env; n.nenv = c.nenv;
            n.arm = a; n.res = c.res;
            o1 = run_k(g, ng, o, no, fuel, n);
            if (o1.t == 0) return outc(0);
            if (o1.t == 4) continue;
            return o1;
        }
        return outc(0);
    }

    if (c.tag == 4) {       /* dispatchBare */
        if (!c.res.payload) return outc(0);
        for (i = 0; i < c.narms; i++) {
            Arm *a = c.arms[i];
            Outc o1;
            Call n = {0};
            if (a->catchall || a->branch[0] == 0) return outc(0);
            n.tag = 5; n.env = c.env; n.nenv = c.nenv;
            n.arm = a; n.res = c.res;
            o1 = run_k(g, ng, o, no, fuel, n);
            if (o1.t == 0) return outc(0);
            if (o1.t == 4) continue;
            return o1;
        }
        return outc(0);
    }

    if (c.tag == 5) {       /* armTry: bind + guard */
        Arm *a = c.arm;
        NV *env2 = c.env;
        int nenv2 = c.nenv;
        int gp;
        if (a->bind) {
            if (!c.res.payload) return outc(0);
            env2 = xmalloc((nenv2 + 1) * sizeof(NV));
            env2[0].n = a->bind; env2[0].v = c.res.payload;
            for (i = 0; i < nenv2; i++) env2[i + 1] = c.env[i];
            nenv2++;
        }
        if (!a->cond) {
            gp = 1;
        } else {
            Val *gv = eval_ke(env2, nenv2, a->cond);
            if (!is_bool(gv)) return outc(0);
            gp = gv->b;
        }
        if (!gp) return outc(4);
        {
            Call n = {0};
            n.tag = 6; n.env = env2; n.nenv = nenv2;
            n.arm = a; n.res = c.res;
            return run_k(g, ng, o, no, fuel, n);
        }
    }

    if (c.tag == 6) {       /* armWalk */
        Arm *a = c.arm;
        Val *v;
        if (a->ntag == -1 || a->ntag == 0) return outc(3);
        if (a->ntag == 1 || a->ntag == 2) {   /* jump / invoke */
            NV *hargs = eval_kargs(c.env, c.nenv, a->nargs, a->nnargs);
            if (!hargs && a->nnargs) return outc(0);
            if (a->ntag == 1) {
                Outc o1 = outc(2);
                o1.lbl = a->ntarget; o1.jargs = hargs; o1.nj = a->nnargs;
                return o1;
            }
            {
                Outc inner;
                Call n = {0};
                n.tag = 0; n.name = a->ntarget;
                n.args = hargs; n.nargs = a->nnargs;
                inner = run_k(g, ng, o, no, fuel, n);
                if (inner.t != 1) return outc(0);
                if (a->nconts == 0) return inner;
                {
                    Call n2 = {0};
                    n2.env = c.env; n2.nenv = c.nenv;
                    n2.arms = a->conts; n2.narms = a->nconts;
                    n2.res = inner.r;
                    if (inner.r.branch) {
                        n2.tag = 3; n2.branch = inner.r.branch;
                    } else {
                        n2.tag = 4;
                    }
                    return run_k(g, ng, o, no, fuel, n2);
                }
            }
        }
        if (a->ntag == 3) {   /* produce */
            v = eval_ke(c.env, c.nenv, a->nexpr);
            if (!v) return outc(0);
            { Result r = {0, v}; return outc_res(r); }
        }
        /* ntag == 4: retCtor */
        v = eval_ke(c.env, c.nenv, a->nexpr);
        if (!v) return outc(0);
        { Result r = {a->ntarget, v}; return outc_res(r); }
    }
    return outc(0);
}

/* evalKProg twin — Option<Result>; refuse = has=0 */
static int eval_prog(Decl *g, int ng, Leaf *o, int no, int64_t fuel,
                     char *entry, NV *args, int nargs, Result *out) {
    Call c = {0};
    Outc oc;
    c.tag = 0; c.name = entry; c.args = args; c.nargs = nargs;
    oc = run_k(g, ng, o, no, fuel, c);
    if (oc.t != 1) return 0;
    *out = oc.r;
    return 1;
}

/* ================= quotation — quoteProg twin =================
   Mirrors encProg's tag table as KVal data (KoruEmit.lean):
   nodes  = cell [("tag", int n), ("kids", arr children)]
   pairs  = cell [("name", str), ("v", _)]
   option = node 23 [] / node 24 [x]; lists are arr.
   Src programs cross into the compiler as a `src` arg whose value
   is this quotation — the calling convention of emitCall. */

static Val *qnode(int64_t tag, Val **kids, int nk) {
    /* kids is a caller's stack array — copy into owned storage */
    Val **kk = nk ? xmalloc(nk * sizeof(Val *)) : 0;
    char **ns = xmalloc(2 * sizeof(char *));
    Val **vs = xmalloc(2 * sizeof(Val *));
    int i;
    for (i = 0; i < nk; i++) kk[i] = kids[i];
    ns[0] = xstrdup("tag"); ns[1] = xstrdup("kids");
    vs[0] = v_int(tag);    vs[1] = v_arr(kk, nk);
    return v_cell(ns, vs, 2);
}
static Val *qnode0(int64_t t) { return qnode(t, 0, 0); }
static Val *qnode1(int64_t t, Val *a) {
    Val *k[1]; k[0] = a; return qnode(t, k, 1);
}
static Val *qnode2(int64_t t, Val *a, Val *b) {
    Val *k[2]; k[0] = a; k[1] = b; return qnode(t, k, 2);
}
static Val *qpair(const char *n, Val *v) {
    char **ns = xmalloc(2 * sizeof(char *));
    Val **vs = xmalloc(2 * sizeof(Val *));
    ns[0] = xstrdup("name"); ns[1] = xstrdup("v");
    vs[0] = v_str(xstrdup(n)); vs[1] = v;
    return v_cell(ns, vs, 2);
}
static Val *qopt(Val *v) {        /* NULL = none */
    Val *k[1];
    if (!v) return qnode0(23);
    k[0] = v; return qnode(24, k, 1);
}

static Val *quote_val(Val *v) {
    int i;
    if (is_int(v))   return qnode1(1, v_int(v->i));
    if (is_float(v)) return qnode2(2, v_int(v->i), v_int(v->d));
    if (is_bool(v))  return qnode1(3, v_int(v->b ? 1 : 0));
    if (is_str(v))   return qnode1(4, v_str(xstrdup(v->s)));
    if (is_arr(v)) {
        Val **kids = xmalloc(v->nx * sizeof(Val *));
        for (i = 0; i < v->nx; i++) kids[i] = quote_val(v->xs[i]);
        return qnode1(5, v_arr(kids, v->nx));
    }
    {   /* cell → node 6 [arr of qpairs] */
        Val **kids = xmalloc(v->nf * sizeof(Val *));
        for (i = 0; i < v->nf; i++)
            kids[i] = qpair(v->ns[i], quote_val(v->vs[i]));
        return qnode1(6, v_arr(kids, v->nf));
    }
}

static Val *quote_expr(Expr *e);
static Val *quote_nes(NE *es, int n) {
    Val **kids = n ? xmalloc(n * sizeof(Val *)) : 0;
    int i;
    for (i = 0; i < n; i++) kids[i] = qpair(es[i].n, quote_expr(es[i].e));
    return v_arr(kids, n);
}
static Val *quote_expr(Expr *e) {
    Val *k[3];
    switch (e->tag) {
    case 0: return qnode1(8, quote_val(e->lit));
    case 1: return qnode1(9, v_str(xstrdup(e->name)));
    case 2: k[0] = v_int(e->op); k[1] = quote_expr(e->a);
            k[2] = quote_expr(e->b); return qnode(10, k, 3);
    case 3: k[0] = v_int(e->op); k[1] = quote_expr(e->a);
            return qnode(11, k, 2);
    case 4: k[0] = quote_expr(e->a); k[1] = quote_expr(e->b);
            k[2] = quote_expr(e->c); return qnode(12, k, 3);
    case 5: k[0] = quote_expr(e->a); k[1] = v_str(xstrdup(e->name));
            return qnode(13, k, 2);
    case 6: k[0] = quote_expr(e->a); k[1] = quote_expr(e->b);
            return qnode(14, k, 2);
    case 7: {   /* builtin — kids = [str name, arr of quoted exprs] */
        Val **as_ = e->nargs ? xmalloc(e->nargs * sizeof(Val *)) : 0;
        int i;
        for (i = 0; i < e->nargs; i++) as_[i] = quote_expr(e->args[i]);
        k[0] = v_str(xstrdup(e->name)); k[1] = v_arr(as_, e->nargs);
        return qnode(15, k, 2);
    }
    }
    return 0;
}

static Val *quote_armnode(Arm *a) {
    Val *k[2];
    switch (a->ntag) {
    case 0: return qnode0(16);
    case 1: case 2:
        k[0] = v_str(xstrdup(a->ntarget));
        k[1] = quote_nes(a->nargs, a->nnargs);
        return qnode(a->ntag == 1 ? 17 : 18, k, 2);
    case 3: return qnode1(19, quote_expr(a->nexpr));
    case 4:
        k[0] = v_str(xstrdup(a->ntarget));
        k[1] = quote_expr(a->nexpr);
        return qnode(20, k, 2);
    }
    return 0;
}

static Val *quote_arm(Arm *a) {
    Val **conts = a->nconts ? xmalloc(a->nconts * sizeof(Val *)) : 0;
    Val *k[6];
    int i;
    for (i = 0; i < a->nconts; i++) conts[i] = quote_arm(a->conts[i]);
    k[0] = v_str(xstrdup(a->branch));
    k[1] = v_int(a->catchall ? 1 : 0);
    k[2] = qopt(a->bind ? v_str(xstrdup(a->bind)) : 0);
    k[3] = qopt(a->cond ? quote_expr(a->cond) : 0);
    k[4] = qopt(a->ntag == -1 ? 0 : quote_armnode(a));
    k[5] = v_arr(conts, a->nconts);
    return qnode(22, k, 6);
}

static Val *quote_flow(Flow *f) {
    Val **arms = f->narms ? xmalloc(f->narms * sizeof(Val *)) : 0;
    Val *k[3], *hk[2];
    int i;
    for (i = 0; i < f->narms; i++) arms[i] = quote_arm(f->arms[i]);
    hk[0] = v_str(xstrdup(f->hname));
    hk[1] = quote_nes(f->hargs, f->nhargs);
    k[0] = qopt(f->pre ? v_str(xstrdup(f->pre)) : 0);
    k[1] = qnode(26, hk, 2);
    k[2] = v_arr(arms, f->narms);
    return qnode(25, k, 3);
}

static Val *quote_callable(Callable *c) {
    if (c->t == 1) return qnode0(28);
    if (c->t == 0) return qnode1(27, quote_expr(c->bare));
    return qnode1(29, quote_flow(c->flow));
}

/* qnode 30 [arr of decl qpairs, str entry, arr of arg qpairs] —
   oracle is not part of KProg and never quoted. */
static Val *quote_prog(Prog *p) {
    Val **ga = p->ng ? xmalloc(p->ng * sizeof(Val *)) : 0;
    Val **ea = p->nargs ? xmalloc(p->nargs * sizeof(Val *)) : 0;
    Val *k[3];
    int i;
    for (i = 0; i < p->ng; i++)
        ga[i] = qpair(p->graph[i].n, quote_callable(p->graph[i].c));
    for (i = 0; i < p->nargs; i++)
        ea[i] = qpair(p->args[i].n, quote_val(p->args[i].v));
    k[0] = v_arr(ga, p->ng);
    k[1] = v_str(xstrdup(p->entry));
    k[2] = v_arr(ea, p->nargs);
    return qnode(30, k, 3);
}

/* ================= result compare + printers ================= */

static int result_eq(Result *a, Result *b) {
    if ((a->branch == 0) != (b->branch == 0)) return 0;
    if (a->branch && strcmp(a->branch, b->branch) != 0) return 0;
    if ((a->payload == 0) != (b->payload == 0)) return 0;
    if (a->payload && !val_eq(a->payload, b->payload)) return 0;
    return 1;
}

static void print_val(Val *v, FILE *f) {
    int i;
    if (!v) { fputs("refuse", f); return; }
    switch (v->tag) {
    case 0: fprintf(f, "(int %lld)", (long long)v->i); break;
    case 1: fprintf(f, "(float %lld %lld)", (long long)v->i, (long long)v->d); break;
    case 2: fprintf(f, "(bool %s)", v->b ? "true" : "false"); break;
    case 3: fprintf(f, "(str \"%s\")", v->s); break;
    case 4:
        fputs("(arr", f);
        for (i = 0; i < v->nx; i++) { fputc(' ', f); print_val(v->xs[i], f); }
        fputc(')', f);
        break;
    case 5:
        fputs("(cell", f);
        for (i = 0; i < v->nf; i++) {
            fprintf(f, " (%s ", v->ns[i]);
            print_val(v->vs[i], f);
            fputc(')', f);
        }
        fputc(')', f);
        break;
    }
}

static void print_result(Result *r, FILE *f) {
    if (!r->branch && !r->payload) { fputs("(void)", f); return; }
    if (!r->branch) { fputs("(bare ", f); print_val(r->payload, f); fputc(')', f); return; }
    fprintf(f, "(tag %s", r->branch);
    if (r->payload) { fputc(' ', f); print_val(r->payload, f); }
    fputc(')', f);
}

/* ================= claim check + main =================
   krun FILE.k            — parse the [flow-eval] claim, re-decide,
                            compare with asserted result.
   krun FILE.k --emit SRC.k
                          — take THIS file's program (a compiler such
                            as kemit.k), quote SRC.k's program, feed
                            it as `src` arg, print the str payload
                            (the emitted C). This is the host-side
                            fixpoint leg: the compiler is data, the C
                            binary only interprets. */

int main(int argc, char **argv) {
    char *buf;
    Sx *sx;
    Claim c;
    Result got;

    if (argc != 2 && argc != 4) {
        fputs("usage: krun FILE.k | krun FILE.k --emit SRC.k\n", stderr);
        return 2;
    }
    if (argc == 4 && strcmp(argv[2], "--emit") != 0) {
        fputs("usage: krun FILE.k | krun FILE.k --emit SRC.k\n", stderr);
        return 2;
    }

    buf = file_read_all(argv[1]);
    if (!buf) { fprintf(stderr, "refuse: cannot read %s\n", argv[1]); return 2; }
    sx = parse_top(buf);
    if (!sx) {
        fprintf(stderr, "refuse: %s not a [flow-eval] claim\n", argv[1]);
        return 2;
    }
    if (!sx_claim(sx, &c)) {
        fprintf(stderr, "refuse: %s malformed claim fields\n", argv[1]);
        return 2;
    }

    if (argc == 4) {
        /* emit mode: this file is the compiler; quote SRC's prog,
           invoke its `emit` entry with [("src", quoted)] */
        char *sbuf; Sx *ssx; Claim sc;
        sbuf = file_read_all(argv[3]);
        ssx = sbuf ? parse_top(sbuf) : 0;
        if (!ssx || !sx_claim(ssx, &sc)) {
            fprintf(stderr, "refuse: %s not a [flow-eval] claim\n", argv[3]);
            return 2;
        }
        {
            NV arg;
            arg.n = "src";
            arg.v = quote_prog(&sc.prog);
            if (!eval_prog(c.prog.graph, c.prog.ng, c.oracle, c.noracle,
                           c.fuel, "emit", &arg, 1, &got)) {
                fprintf(stderr, "refuse: %s did not decide emit\n", argv[1]);
                return 3;
            }
            if (!got.payload || !is_str(got.payload)) {
                fprintf(stderr, "refuse: emit payload not a str\n");
                return 3;
            }
            fputs(got.payload->s, stdout);
            fputc('\n', stdout);
            return 0;
        }
    }

    if (!eval_prog(c.prog.graph, c.prog.ng, c.oracle, c.noracle,
                   c.fuel, c.prog.entry, c.prog.args, c.prog.nargs, &got)) {
        if (c.has_expected) {
            fputs("drift: program refused but claim expected ", stderr);
            print_result(&c.expected, stderr);
            fputc('\n', stderr);
            return 4;
        }
        fputs("ok refuse\n", stdout);
        return 0;
    }
    if (!c.has_expected) {
        fputs("drift: program decided but claim expected refuse: ", stderr);
        print_result(&got, stderr);
        fputc('\n', stderr);
        return 4;
    }
    if (!result_eq(&got, &c.expected)) {
        fputs("drift: got ", stderr);
        print_result(&got, stderr);
        fputs(" expected ", stderr);
        print_result(&c.expected, stderr);
        fputc('\n', stderr);
        return 4;
    }
    fputs("ok ", stdout);
    print_result(&got, stdout);
    fputc('\n', stdout);
    return 0;
}
