/*
 * korufe.c — host2: the koru surface frontend, in C99.
 *
 * The parse + lower legs of the koru pipeline, twinning the real
 * frontend's *shape* for a declared subset:
 *
 *   korufe FILE.k                              program.ast.json on stdout
 *   korufe --lower FILE.ast.json CASE.json     [flow-eval] claim on stdout
 *
 * The AST emitted follows the canonical post-parse AST JSON shape
 * (keyed-dict items: event_decl / immediate_impl / flow / import_decl)
 * that `koruc --ast-canon` prints — for the declared subset only.
 * Arg and impl values stay source strings, matching the real AST
 * (expressions parse at lower time, where the pipeline needs trees).
 *
 * Declared subset (refuses anything else, naming the axis):
 *   items    : // comments, import_decl, [pub] tor NAME { f: t } -> T
 *              with | branch payload decls, NAME -> EXPR, NAME = FLOW
 *   flows    : (label)? head-invocation + arm rows
 *   arms     : | branch [bind] [when COND] (=> NAME [EXPR] | -> EXPR |
 *              |> INVOKE | |> @LABEL)
 *   exprs    : int/float/str/bool literals, identifiers, {f: e} cells,
 *              [e..] arrays, (e), !e -e, + - * / % == != < <= > >=
 *              && || ++, if(c) a else b, obj.field, obj[i],
 *              name(args) (builtin when name in the builtin table)
 *   refused  : proc bodies (.kz territory), ~ annotations, => with no
 *              payload (wire ctor requires one — koru carries the
 *              empty cell, spelled `=> name` lowers to empty cell),
 *              host blocks, ~if/~for taps, `! as` catchall-bare, top-
 *              level flow items without impl_of (module-init flows).
 *
 * Declared divergences: floats parse as exact rationals (0.5 = 1/2 —
 * the wire is rational-pair, not f64); int64 range checked.
 */
#define _CRT_SECURE_NO_WARNINGS
#include <stdio.h>
#include <stdlib.h>
#include <string.h>
#include <stdint.h>
#include <limits.h>
#include <stdarg.h>

static void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fputs("korufe: out of memory\n", stderr); exit(4); }
    return p;
}
static char *xstrndup(const char *s, size_t n) {
    char *p = xmalloc(n + 1); memcpy(p, s, n); p[n] = 0; return p;
}
static char *xstrdup(const char *s) { return xstrndup(s, strlen(s)); }
static char *xasprintf(const char *a, const char *b) {
    size_t n = strlen(a) + strlen(b) + 1;
    char *p = xmalloc(n); snprintf(p, n, "%s%s", a, b); return p;
}

/* ================= koru source tokens ================= */

typedef struct {
    int kind;      /* 0 ident 1 int 2 float 3 str 4 punct 5 eof 6 nl */
    char *text;
    int line;
} Tk;

typedef struct { Tk *t; int n, i; } Tks;

static int punct2(const char *s) {
    return !strcmp(s, "->") || !strcmp(s, "=>") || !strcmp(s, "|>") ||
           !strcmp(s, "==") || !strcmp(s, "!=") || !strcmp(s, "<=") ||
           !strcmp(s, ">=") || !strcmp(s, "&&") || !strcmp(s, "||") ||
           !strcmp(s, "++") || !strcmp(s, "..");
}
static int punct1(char c) {
    return strchr("(){}[],:|+-*/%<>=!#.@&", c) != 0;
}

#define GROW_TS \
    if (n == cap) { \
        cap *= 2; \
        { Tk *nt = xmalloc(cap * sizeof(Tk)); \
          memcpy(nt, ts->t, n * sizeof(Tk)); ts->t = nt; } \
    }

static Tks *lex_k(const char *src, const char *file, char **err) {
    Tks *ts = xmalloc(sizeof(Tks));
    int cap = 64, n = 0, line = 1;
    const char *p = src;
    ts->t = xmalloc(cap * sizeof(Tk));
    while (*p) {
        char c = *p;
        if (c == '\n') {
            /* newline is a real token — koru is line-oriented; arm
               payloads and item boundaries are line-scoped */
            GROW_TS
            ts->t[n].kind = 6; ts->t[n].text = "nl"; ts->t[n].line = line;
            n++; line++; p++;
            continue;
        }
        if (c == ' ' || c == '\t' || c == '\r') { p++; continue; }
        if (c == '/' && p[1] == '/') {
            while (*p && *p != '\n') p++;
            continue;
        }
        GROW_TS
        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_') {
            const char *b = p;
            while ((*p >= 'a' && *p <= 'z') || (*p >= 'A' && *p <= 'Z') ||
                   (*p >= '0' && *p <= '9') || *p == '_') p++;
            ts->t[n].kind = 0;
            ts->t[n].text = xstrndup(b, (size_t)(p - b));
            ts->t[n].line = line; n++;
            continue;
        }
        if (c >= '0' && c <= '9') {
            const char *b = p;
            int isf = 0;
            while (*p >= '0' && *p <= '9') p++;
            if (*p == '.' && p[1] >= '0' && p[1] <= '9') {
                isf = 1; p++;
                while (*p >= '0' && *p <= '9') p++;
            }
            ts->t[n].kind = isf ? 2 : 1;
            ts->t[n].text = xstrndup(b, (size_t)(p - b));
            ts->t[n].line = line; n++;
            continue;
        }
        if (c == '"') {
            const char *b = p;
            p++;
            while (*p && *p != '"') {
                if (*p == '{' && p[1] == '{') {  /* interpolation */
                    *err = xstrdup("str interpolation {{ }} out of subset");
                    return 0;
                }
                p++;
            }
            if (!*p) { *err = xstrdup("unterminated string"); return 0; }
            p++;
            ts->t[n].kind = 3;
            ts->t[n].text = xstrndup(b, (size_t)(p - b));
            ts->t[n].line = line; n++;
            continue;
        }
        if (punct1(c)) {
            if (p[1] && punct2((char[]){c, p[1], 0})) {
                ts->t[n].kind = 4;
                ts->t[n].text = xstrndup(p, 2);
                ts->t[n].line = line; n++; p += 2;
            } else {
                ts->t[n].kind = 4;
                ts->t[n].text = xstrndup(p, 1);
                ts->t[n].line = line; n++; p++;
            }
            continue;
        }
        {
            char m[64];
            snprintf(m, sizeof m, "unexpected character '%c' at line %d of %s",
                     c, line, file);
            *err = xstrdup(m);
            return 0;
        }
    }
    if (n == cap) {
        cap++;
        { Tk *nt = xmalloc(cap * sizeof(Tk));
          memcpy(nt, ts->t, n * sizeof(Tk)); ts->t = nt; }
    }
    ts->t[n].kind = 5; ts->t[n].text = "eof"; ts->t[n].line = line; n++;
    ts->n = n; ts->i = 0;
    return ts;
}

/* ---- token ops ---- */
static Tk *peek(Tks *s) { return s->i < s->n ? &s->t[s->i] : &s->t[s->n - 1]; }
static Tk *next_tk(Tks *s) { return s->i < s->n ? &s->t[s->i++] : &s->t[s->n - 1]; }
static int at(Tks *s, const char *w) {
    return peek(s)->kind != 5 && strcmp(peek(s)->text, w) == 0;
}
static int at_kind(Tks *s, int k) { return peek(s)->kind == k; }
static int eat(Tks *s, const char *w) {
    if (at(s, w)) { s->i++; return 1; }
    return 0;
}
static void snl(Tks *s) {                       /* skip newlines */
    while (peek(s)->kind == 6) s->i++;
}
static int fail_at(Tks *s, char **err, const char *msg) {
    static char buf[256];
    snprintf(buf, sizeof buf, "parse: %s at line %d (near '%s')",
             msg, peek(s)->line, peek(s)->text);
    *err = xstrdup(buf);
    return 0;
}

/* ================= koru AST (C-side) =================
   items -> ast.json; the AST is also the lowerer's input when
   --lower runs against its own JSON — so the writer must emit
   exactly what the JSON reader reads back. */

typedef struct KExpr KExpr;
struct KExpr {
    int tag;              /* 0 lit 1 var 2 bin 3 un 4 cond 5 field 6 index
                             7 builtin 8 call(invocation) */
    int64_t i, d;         /* int; float num/den */
    int b;                /* bool */
    char *s;              /* str / var / field name / call-or-builtin name */
    int op;               /* bin/un op codes (wire numbering) */
    KExpr *a, *bb, *c;
    struct { char *n; KExpr *e; } *args; int nargs;   /* call args */
    KExpr **xs; int nxs;                              /* arr literal */
    struct { char *n; KExpr *e; } *fs; int nfs;       /* cell literal */
};

/* invocation: qname (mod/path:name dotted-or-slashed → wire keeps last
   segment as callable name; qualifier is recorded, resolution refuses
   at lower if a qualifier is present — single-module subset) */
typedef struct {
    char *qual;            /* NULL = local */
    char *name;
    struct { char *n; KExpr *e; } *args; int nargs;
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

/* ================= expression parser =================
   precedence: || < && < == != < < <= > >= < ++ < + - < * / % < unary <
   postfix (.field [i] (args)) < primary                         */

static KExpr *ke_new(int tag) {
    KExpr *e = xmalloc(sizeof(KExpr));
    memset(e, 0, sizeof *e); e->tag = tag; return e;
}
static KExpr *ke_var(const char *n) { KExpr *e = ke_new(1); e->s = xstrdup(n); return e; }
static KExpr *ke_bin(int op, KExpr *a, KExpr *b) {
    KExpr *e = ke_new(2); e->op = op; e->a = a; e->bb = b; return e;
}
static KExpr *ke_un(int op, KExpr *a) {
    KExpr *e = ke_new(3); e->op = op; e->a = a; return e;
}

static int parse_i64(const char *s, int64_t *o) {
    const char *p = s; int neg = 0; int64_t v = 0;
    if (*p == '-') { neg = 1; p++; }
    if (!*p) return 0;
    while (*p) {
        if (*p < '0' || *p > '9') return 0;
        if (v > (INT64_MAX - (*p - '0')) / 10) return 0;
        v = v * 10 + (*p - '0'); p++;
    }
    if (neg) { if (v == INT64_MIN) return 0; v = -v; }
    *o = v; return 1;
}

/* decimal -> exact rational (wire float is num/den) */
static int parse_rat(const char *s, int64_t *on, int64_t *od) {
    char buf[64];
    const char *dot = strchr(s, '.');
    int64_t w, f = 0, d = 1;
    if (!dot) return 0;
    snprintf(buf, sizeof buf, "%.*s", (int)(dot - s), s);
    if (!parse_i64(buf, &w)) return 0;
    {
        const char *p = dot + 1;
        if (!*p) return 0;
        while (*p) {
            if (*p < '0' || *p > '9') return 0;
            if (f > (INT64_MAX - (*p - '0')) / 10 ||
                d > INT64_MAX / 10) return 0;
            f = f * 10 + (*p - '0'); d *= 10; p++;
        }
    }
    /* reduce by gcd — the wire normalizes (asKRat refuses d<=0) */
    {
        int64_t a = f < 0 ? -f : f, b = d;
        while (b) { int64_t t = a % b; a = b; b = t; }
        if (a) { f /= a; d /= a; }
    }
    {   /* w * d + f */
        int64_t t;
        if (d != 0 && (w > INT64_MAX / d || w < INT64_MIN / d)) return 0;
        t = w * d;
        if ((f > 0 && t > INT64_MAX - f) || (f < 0 && t < INT64_MIN - f)) return 0;
        t += f;
        *on = t; *od = d;
    }
    return 1;
}

static KExpr *parse_expr(Tks *s, char **err);
static KExpr *parse_postfix(Tks *s, char **err);

static KExpr *parse_call_args(Tks *s, char **err, KExpr *e /* the call node */) {
    /* ( name: expr, expr, name: expr ) — named or positional */
    int cap = 4;
    e->args = xmalloc(cap * sizeof(*e->args));
    e->nargs = 0;
    if (eat(s, ")")) return e;
    for (;;) {
        char *an = 0;
        KExpr *ae;
        if (at_kind(s, 0) && s->i + 1 < s->n &&
            strcmp(s->t[s->i + 1].text, ":") == 0) {
            an = xstrdup(next_tk(s)->text);
            s->i++;            /* ':' */
        }
        ae = parse_expr(s, err);
        if (!ae) return 0;
        if (e->nargs == cap) {
            cap *= 2;
            { void *na = xmalloc(cap * sizeof(*e->args));
              memcpy(na, e->args, e->nargs * sizeof(*e->args));
              e->args = na; }
        }
        e->args[e->nargs].n = an;
        e->args[e->nargs].e = ae;
        e->nargs++;
        if (eat(s, ",")) continue;
        if (eat(s, ")")) return e;
        fail_at(s, err, "expected ',' or ')' in call args");
        return 0;
    }
}

static KExpr *parse_primary(Tks *s, char **err) {
    Tk *t = peek(s);
    if (at(s, "(")) {
        KExpr *e;
        s->i++;
        e = parse_expr(s, err);
        if (!e) return 0;
        if (!eat(s, ")")) { fail_at(s, err, "expected ')'"); return 0; }
        return e;
    }
    if (at(s, "[")) {
        KExpr *e = ke_new(0);   /* lit arr — stored in xs */
        int cap = 4;
        e->tag = 9;             /* internal: array literal */
        s->i++;
        e->xs = xmalloc(cap * sizeof(KExpr *));
        e->nxs = 0;
        if (!at(s, "]")) {
            for (;;) {
                KExpr *x = parse_expr(s, err);
                if (!x) return 0;
                if (e->nxs == cap) {
                    cap *= 2;
                    { KExpr **nx = xmalloc(cap * sizeof(KExpr *));
                      memcpy(nx, e->xs, e->nxs * sizeof(KExpr *));
                      e->xs = nx; }
                }
                e->xs[e->nxs++] = x;
                if (eat(s, ",")) continue;
                break;
            }
        }
        if (!eat(s, "]")) { fail_at(s, err, "expected ']'"); return 0; }
        return e;
    }
    if (at(s, "{")) {
        KExpr *e = ke_new(10);  /* internal: cell literal */
        int cap = 4;
        s->i++;
        e->fs = xmalloc(cap * sizeof(*e->fs));
        e->nfs = 0;
        if (!at(s, "}")) {
            for (;;) {
                char *fn;
                KExpr *fe;
                if (!at_kind(s, 0)) { fail_at(s, err, "cell field name"); return 0; }
                fn = xstrdup(next_tk(s)->text);
                if (!eat(s, ":")) { fail_at(s, err, "':' after cell field"); return 0; }
                fe = parse_expr(s, err);
                if (!fe) return 0;
                /* optional [type] annotation on the value — strip it */
                if (at(s, "[")) {
                    s->i++;
                    if (at_kind(s, 0) || at_kind(s, 1)) s->i++;
                    while (at_kind(s, 0) || at(s, ".")) s->i++;   /* qualified ty */
                    if (!eat(s, "]")) { fail_at(s, err, "']' after field type"); return 0; }
                }
                if (e->nfs == cap) {
                    cap *= 2;
                    { void *nf = xmalloc(cap * sizeof(*e->fs));
                      memcpy(nf, e->fs, e->nfs * sizeof(*e->fs));
                      e->fs = nf; }
                }
                e->fs[e->nfs].n = fn; e->fs[e->nfs].e = fe; e->nfs++;
                if (eat(s, ",")) continue;
                break;
            }
        }
        if (!eat(s, "}")) { fail_at(s, err, "expected '}'"); return 0; }
        return e;
    }
    if (at(s, "if")) {
        KExpr *e = ke_new(4);
        s->i++;
        if (!eat(s, "(")) { fail_at(s, err, "'(' after if"); return 0; }
        e->a = parse_expr(s, err);
        if (!e->a) return 0;
        if (!eat(s, ")")) { fail_at(s, err, "')' after if-cond"); return 0; }
        e->bb = parse_expr(s, err);
        if (!e->bb) return 0;
        if (!eat(s, "else")) { fail_at(s, err, "else"); return 0; }
        e->c = parse_expr(s, err);
        if (!e->c) return 0;
        return e;
    }
    if (at(s, "true") || at(s, "false")) {
        KExpr *e = ke_new(0);
        e->tag = 11; e->b = at(s, "true");
        s->i++;
        return e;
    }
    if (t->kind == 1) {           /* int */
        KExpr *e = ke_new(0);
        s->i++;
        if (!parse_i64(t->text, &e->i)) { fail_at(s, err, "int out of range"); return 0; }
        return e;
    }
    if (t->kind == 2) {           /* float → rational */
        KExpr *e = ke_new(12);
        s->i++;
        if (!parse_rat(t->text, &e->i, &e->d)) { fail_at(s, err, "float literal"); return 0; }
        return e;
    }
    if (t->kind == 3) {           /* "str" — quotes kept by lexer */
        KExpr *e = ke_new(13);
        size_t n = strlen(t->text);
        s->i++;
        e->s = xstrndup(t->text + 1, n - 2);
        return e;
    }
    if (t->kind == 0) {
        KExpr *e = ke_var(t->text);
        s->i++;
        return e;
    }
    fail_at(s, err, "expected expression");
    return 0;
}

static int type_tok(const char *t) {
    static const char *ts[] = {"i64","i32","i16","i8","u64","u32","u16",
                               "u8","f64","f32","bool","string","program",
                               "void","unit",0};
    int i;
    for (i = 0; ts[i]; i++) if (!strcmp(t, ts[i])) return 1;
    return 0;
}

static KExpr *parse_postfix(Tks *s, char **err) {
    KExpr *e = parse_primary(s, err);
    if (!e) return 0;
    for (;;) {
        if (at(s, ".")) {
            s->i++;
            if (!at_kind(s, 0)) { fail_at(s, err, "field name after '.'"); return 0; }
            {
                KExpr *f = ke_new(5);
                f->a = e; f->s = xstrdup(next_tk(s)->text);
                e = f;
            }
            continue;
        }
        if (at(s, "[")) {
            KExpr *ix, *f;
            /* `literal[T]` is a type annotation on the literal
               (`0[i64]`), not an index — only when e is a literal and
               the bracket holds a bare type name */
            if ((e->tag == 0 || e->tag == 12 || e->tag == 13 ||
                 e->tag == 11) &&
                s->i + 2 < s->n && s->t[s->i + 1].kind == 0 &&
                type_tok(s->t[s->i + 1].text) &&
                strcmp(s->t[s->i + 2].text, "]") == 0) {
                s->i += 3;
                continue;
            }
            s->i++;
            ix = parse_expr(s, err);
            if (!ix) return 0;
            if (!eat(s, "]")) { fail_at(s, err, "']' after index"); return 0; }
            f = ke_new(6); f->a = e; f->bb = ix; e = f;
            continue;
        }
        if (at(s, "(")) {
            /* call — only on a bare identifier */
            KExpr *c;
            if (e->tag != 1) {
                fail_at(s, err, "call target must be a name");
                return 0;
            }
            s->i++;
            c = ke_new(8);                 /* call */
            c->s = e->s;
            if (!parse_call_args(s, err, c)) return 0;
            e = c;
            continue;
        }
        return e;
    }
}

static const char *binop_at(Tks *s, int *op) {
    static const struct { const char *w; int op; } tab[] = {
        {"||", 12}, {"or", 12}, {"&&", 11}, {"and", 11},
        {"==", 5}, {"!=", 6}, {"<", 7}, {"<=", 8}, {">", 9}, {">=", 10},
        {"++", 13}, {"+", 0}, {"-", 1}, {"*", 2}, {"/", 3}, {"%", 4},
        {0, -1}
    };
    int i;
    for (i = 0; tab[i].w; i++)
        if (at(s, tab[i].w)) {
            *op = tab[i].op;
            return tab[i].w;
        }
    return 0;
}
static int op_prec(int op) {
    switch (op) {
    case 12: return 1;    /* or  */
    case 11: return 2;    /* and */
    case 5: case 6: return 3;
    case 7: case 8: case 9: case 10: return 4;
    case 13: return 5;    /* ++ */
    case 0: case 1: return 6;
    case 2: case 3: case 4: return 7;
    }
    return 0;
}

static KExpr *parse_bin(Tks *s, char **err, int minprec) {
    KExpr *l = parse_postfix(s, err);
    if (!l) return 0;
    for (;;) {
        int op, prec;
        const char *w;
        KExpr *r;
        /* newlines are transparent inside an expression — koru source
           wraps long conditionals across lines */
        snl(s);
        w = binop_at(s, &op);
        if (!w) break;
        prec = op_prec(op);
        if (prec < minprec) break;
        s->i++;
        snl(s);
        r = parse_bin(s, err, prec + 1);
        if (!r) return 0;
        l = ke_bin(op, l, r);
    }
    return l;
}

static KExpr *parse_expr(Tks *s, char **err) {
    snl(s);
    if (at(s, "!")) {
        KExpr *a;
        s->i++;
        a = parse_expr(s, err);
        if (!a) return 0;
        return ke_un(1, a);          /* not */
    }
    if (at(s, "-")) {
        KExpr *a;
        s->i++;
        a = parse_expr(s, err);
        if (!a) return 0;
        /* -<int literal> folds — keeps `-3` surface working */
        if (a->tag == 0) {
            if (a->i == INT64_MIN) { fail_at(s, err, "int underflow"); return 0; }
            a->i = -a->i;
            return a;
        }
        return ke_un(0, a);          /* neg */
    }
    return parse_bin(s, err, 1);
}

/* ================= item parser =================
   line-oriented like real koru: items are top-level declarations,
   arms are `|`-led lines belonging to the preceding flow/impl.
   We tokenize the WHOLE file (koru is layout-sensitive via indents —
   for the declared subset we accept a line-free spelling where every
   arm row starts with `|` at top level, matching real koru).        */

static int is_ident_tk(Tks *s) { return at_kind(s, 0); }

/* qualified name: ident ((':'|'/'|'.') ident)* — mod/name or mod:name */
static char *parse_qname(Tks *s, char **err, char **qual) {
    char *name;
    *qual = 0;
    if (!is_ident_tk(s)) { fail_at(s, err, "name"); return 0; }
    name = xstrdup(next_tk(s)->text);
    while ((at(s, ":") || at(s, "/") || at(s, ".")) &&
           s->i + 1 < s->n && s->t[s->i + 1].kind == 0) {
        char *sep = xstrdup(next_tk(s)->text);
        char *seg = xstrdup(next_tk(s)->text);
        if (*qual) {
            char *nq = xmalloc(strlen(*qual) + strlen(name) + 2);
            sprintf(nq, "%s%s%s", *qual, sep, name);
            *qual = nq;
        } else {
            *qual = name;
        }
        name = seg;
    }
    return name;
}

static Inv *parse_inv(Tks *s, char **err, int allow_label) {
    Inv *v = xmalloc(sizeof(Inv));
    memset(v, 0, sizeof *v);
    if (allow_label && at(s, "@")) {
        s->i++;
        if (!is_ident_tk(s)) { fail_at(s, err, "label name after @"); return 0; }
        v->name = xstrdup(next_tk(s)->text);
        v->qual = xstrdup("@");
    } else {
        v->name = parse_qname(s, err, &v->qual);
        if (!v->name) return 0;
    }
    if (eat(s, "(")) {
        int cap = 4;
        v->args = xmalloc(cap * sizeof(*v->args));
        v->nargs = 0;
        if (!at(s, ")")) {
            for (;;) {
                char *an = 0;
                KExpr *ae;
                if (at_kind(s, 0) && s->i + 1 < s->n &&
                    strcmp(s->t[s->i + 1].text, ":") == 0) {
                    an = xstrdup(next_tk(s)->text);
                    s->i++;
                }
                ae = parse_expr(s, err);
                if (!ae) return 0;
                if (v->nargs == cap) {
                    cap *= 2;
                    { void *na = xmalloc(cap * sizeof(*v->args));
                      memcpy(na, v->args, v->nargs * sizeof(*v->args));
                      v->args = na; }
                }
                v->args[v->nargs].n = an;
                v->args[v->nargs].e = ae;
                v->nargs++;
                if (eat(s, ",")) continue;
                break;
            }
        }
        if (!eat(s, ")")) { fail_at(s, err, "')' after args"); return 0; }
    } else if (v->qual && v->qual[0] == '@') {
        /* @label with no args is fine */
    }
    /* `: bind` on a bare invocation is koru's head-result bind — the
       wire expresses it through arm binds instead; refuse rather than
       drop it */
    if (at(s, ":")) {
        fail_at(s, err, "'inv: bind' out of subset (bind on the arm row)");
        return 0;
    }
    return v;
}

static ArmD *parse_arm(Tks *s, char **err) {
    /* consumed the leading '|' already */
    ArmD *a = xmalloc(sizeof(ArmD));
    memset(a, 0, sizeof *a);
    a->kind = -1;
    a->branch = "";
    snl(s);
    if (eat(s, "*")) {
        a->catchall = 1; a->branch = "*";
    } else if (is_ident_tk(s)) {
        a->branch = xstrdup(next_tk(s)->text);
    } else {
        fail_at(s, err, "arm branch or catchall");
        return 0;
    }
    if (is_ident_tk(s))                       /* bind */
        a->bind = xstrdup(next_tk(s)->text);
    if (eat(s, "when")) {                     /* guard */
        if (!eat(s, "(")) { fail_at(s, err, "'(' after when"); return 0; }
        a->cond = parse_expr(s, err);
        if (!a->cond) return 0;
        if (!eat(s, ")")) { fail_at(s, err, "')' after when"); return 0; }
    }
    /* step */
    if (at(s, "=>")) {
        s->i++;
        if (!is_ident_tk(s)) { fail_at(s, err, "ctor name after =>"); return 0; }
        a->kind = 2;
        a->target = xstrdup(next_tk(s)->text);
        /* optional payload — only on the same line: `=> name` alone
           carries the empty cell, matching koru's payload:{fields:[]} */
        if (peek(s)->kind != 6 && !at_kind(s, 5) &&
            !at(s, "|") && !at(s, "}")) {
            a->produce = parse_expr(s, err);
            if (!a->produce) return 0;
        }
    } else if (at(s, "->")) {
        s->i++;
        a->kind = 1;
        a->produce = parse_expr(s, err);
        if (!a->produce) return 0;
    } else if (at(s, "|>")) {
        s->i++;
        a->kind = 3;
        a->inv = parse_inv(s, err, 1);
        if (!a->inv) return 0;
        if (a->inv->qual && a->inv->qual[0] == '@') {
            a->kind = 4;
            a->target = a->inv->name;
        } else {
            a->kind = 3;
            a->target = a->inv->name;
        }
    } else {
        a->kind = 0;                          /* terminal */
    }
    return a;
}

static FlowD *parse_flow(Tks *s, char **err) {
    FlowD *f = xmalloc(sizeof(FlowD));
    memset(f, 0, sizeof *f);
    if (at(s, "#")) {
        s->i++;
        if (!is_ident_tk(s)) { fail_at(s, err, "label after #"); return 0; }
        f->pre = xstrdup(next_tk(s)->text);
    }
    f->head = parse_inv(s, err, 0);
    if (!f->head) return 0;
    {
        int cap = 4;
        f->arms = xmalloc(cap * sizeof(ArmD *));
        f->narms = 0;
        for (;;) {
            ArmD *a;
            snl(s);
            if (!at(s, "|")) break;
            if (s->i + 1 < s->n &&
                strcmp(s->t[s->i + 1].text, ">") == 0) break;  /* '|>' */
            s->i++;
            a = parse_arm(s, err);
            if (!a) return 0;
            if (f->narms == cap) {
                cap *= 2;
                { ArmD **na = xmalloc(cap * sizeof(ArmD *));
                  memcpy(na, f->arms, f->narms * sizeof(ArmD *));
                  f->arms = na; }
            }
            f->arms[f->narms++] = a;
        }
    }
    return f;
}

static Item *item_new(int kind) {
    Item *it = xmalloc(sizeof(Item));
    memset(it, 0, sizeof *it);
    it->kind = kind;
    return it;
}

static Item *parse_program(Tks *s, char **err) {
    Item *head = 0, **tail = &head;
    for (;;) {
        Item *it;
        snl(s);
        if (at_kind(s, 5)) break;
        if (eat(s, "import")) {
            char *q;
            it = item_new(0);
            it->name = parse_qname(s, err, &q);
            it->import_path = q ? xasprintf(q, xasprintf("/", it->name))
                                : it->name;
            if (!it->name) return 0;
            *tail = it; tail = &it->next;
            continue;
        }
        it = item_new(-1);
        it->line = peek(s)->line;
        if (eat(s, "pub")) it->is_pub = 1;
        if (eat(s, "tor")) {
            it->kind = 1;
            if (!is_ident_tk(s)) { fail_at(s, err, "tor name"); return 0; }
            it->name = xstrdup(next_tk(s)->text);
            if (!eat(s, "{")) { fail_at(s, err, "'{' after tor name"); return 0; }
            {
                int cap = 4;
                it->fields = xmalloc(cap * sizeof(*it->fields));
                it->nfields = 0;
                while (!at(s, "}")) {
                    if (!is_ident_tk(s)) { fail_at(s, err, "field name"); return 0; }
                    if (it->nfields == cap) {
                        cap *= 2;
                        { void *nf = xmalloc(cap * sizeof(*it->fields));
                          memcpy(nf, it->fields, it->nfields * sizeof(*it->fields));
                          it->fields = nf; }
                    }
                    it->fields[it->nfields].n = xstrdup(next_tk(s)->text);
                    if (!eat(s, ":")) { fail_at(s, err, "':' after field"); return 0; }
                    /* type tokens: ident (qualifiers/brackets skipped) */
                    if (!is_ident_tk(s)) { fail_at(s, err, "field type"); return 0; }
                    it->fields[it->nfields].t = xstrdup(next_tk(s)->text);
                    while (at(s, ".") || at(s, "/")) {
                        s->i++;
                        if (is_ident_tk(s))
                            it->fields[it->nfields].t =
                                xasprintf(it->fields[it->nfields].t,
                                          xasprintf("/", next_tk(s)->text));
                    }
                    if (at(s, "[")) {       /* phantom/type params — skip */
                        int depth = 0;
                        do {
                            if (at(s, "[")) depth++;
                            if (at(s, "]")) depth--;
                            s->i++;
                        } while (depth > 0 && !at_kind(s, 5));
                    }
                    it->nfields++;
                    eat(s, ",");
                }
                if (!eat(s, "}")) { fail_at(s, err, "'}' after fields"); return 0; }
            }
            /* branch decls: | name [payload] — payload groups skipped
               (declared, not interpreted by the wire) */
            {
                int cap = 4;
                it->branches = xmalloc(cap * sizeof(char *));
                it->nbranches = 0;
                for (;;) {
                    snl(s);
                    if (!at(s, "|") ||
                        (s->i + 1 < s->n &&
                         strcmp(s->t[s->i + 1].text, ">") == 0))
                        break;
                    s->i++;
                    if (!is_ident_tk(s)) { fail_at(s, err, "branch name"); return 0; }
                    if (it->nbranches == cap) {
                        cap *= 2;
                        { char **nb = xmalloc(cap * sizeof(char *));
                          memcpy(nb, it->branches, it->nbranches * sizeof(char *));
                          it->branches = nb; }
                    }
                    it->branches[it->nbranches++] = xstrdup(next_tk(s)->text);
                    if (at(s, "(") || at(s, "{")) {   /* payload decl — skip */
                        char open = peek(s)->text[0];
                        char close = open == '(' ? ')' : '}';
                        int depth = 0;
                        do {
                            if (peek(s)->text[0] == open) depth++;
                            if (peek(s)->text[0] == close) depth--;
                            s->i++;
                        } while (depth > 0 && !at_kind(s, 5));
                    }
                }
            }
            if (eat(s, "->")) {              /* return type */
                if (!is_ident_tk(s)) { fail_at(s, err, "return type"); return 0; }
                it->ret_type = xstrdup(next_tk(s)->text);
                while (at(s, "/") || at(s, ".")) {
                    s->i++;
                    if (is_ident_tk(s))
                        it->ret_type = xasprintf(it->ret_type,
                                                 xasprintf("/", next_tk(s)->text));
                }
            }
            *tail = it; tail = &it->next;
            continue;
        }
        if (!is_ident_tk(s)) {
            fail_at(s, err, "item (import|tor|name)");
            return 0;
        }
        it->name = xstrdup(next_tk(s)->text);
        if (eat(s, "->")) {
            it->kind = 2;
            it->bare = parse_expr(s, err);
            if (!it->bare) return 0;
        } else if (at(s, "=>")) {
            fail_at(s, err,
                    "name => branch impl out of subset (write 'name = ...' "
                    "or give the ctor a payload via arms)");
            return 0;
        } else if (at(s, "=")) {
            s->i++;
            it->kind = 3;
            it->flow = parse_flow(s, err);
            if (!it->flow) return 0;
        } else if (at(s, "(")) {
            /* top-level flow item: name(args) + arm rows */
            s->i--;                      /* re-parse as invocation incl name */
            it->kind = 4;
            {
                Inv *h = parse_inv(s, err, 0);
                FlowD *f = xmalloc(sizeof(FlowD));
                memset(f, 0, sizeof *f);
                if (!h) return 0;
                f->head = h;
                {
                    int cap = 4;
                    f->arms = xmalloc(cap * sizeof(ArmD *));
                    f->narms = 0;
                    for (;;) {
                        ArmD *a;
                        snl(s);
                        if (!at(s, "|") ||
                            (s->i + 1 < s->n &&
                             strcmp(s->t[s->i + 1].text, ">") == 0))
                            break;
                        s->i++;
                        a = parse_arm(s, err);
                        if (!a) return 0;
                        if (f->narms == cap) {
                            cap *= 2;
                            { ArmD **na = xmalloc(cap * sizeof(ArmD *));
                              memcpy(na, f->arms, f->narms * sizeof(ArmD *));
                              f->arms = na; }
                        }
                        f->arms[f->narms++] = a;
                    }
                }
                it->flow = f;
            }
        } else {
            fail_at(s, err, "after name: -> | => | = | (");
            return 0;
        }
        *tail = it; tail = &it->next;
    }
    return head;
}

/* ================= ast.json writer (canon shape) ================= */

static void jesc(FILE *f, const char *s) {
    fputc('"', f);
    for (; *s; s++) {
        if (*s == '"' || *s == '\\') fprintf(f, "\\%c", *s);
        else if (*s == '\n') fputs("\\n", f);
        else fputc(*s, f);
    }
    fputc('"', f);
}

/* expr back to source text — the canon AST keeps values as strings.
   Buffer-accumulating; used for plain_value fields. */
typedef struct { char *p; size_t n, cap; } Buf;
static void bput(Buf *b, const char *s) {
    size_t n = strlen(s);
    while (b->n + n + 1 > b->cap) {
        b->cap = b->cap ? b->cap * 2 : 256;
        b->p = realloc(b->p, b->cap);
    }
    memcpy(b->p + b->n, s, n); b->n += n; b->p[b->n] = 0;
}
static void bputf(Buf *b, const char *fmt, ...) {
    char tmp[128];
    va_list ap;
    va_start(ap, fmt);
    vsnprintf(tmp, sizeof tmp, fmt, ap);
    va_end(ap);
    bput(b, tmp);
}

/* rational → finite decimal text (koru floats are decimals; only
   d = 2^a·5^b is surface-expressible — anything else can't be spelled,
   emits a marker that re-parse will refuse, which is the honest
   failure for a value koru syntax cannot represent) */
static void rat_to_dec(int64_t n, int64_t d, Buf *b) {
    int64_t rem = d, a2 = 0, a5 = 0, k;
    int64_t scale, pw = 1;
    int64_t scaled, an, whole, frac;
    char fr[32], pad[32];
    int i, fl;
    while (rem % 2 == 0 && rem) { rem /= 2; a2++; }
    while (rem % 5 == 0 && rem) { rem /= 5; a5++; }
    if (rem != 1) {
        bput(b, "{{unspellable-rational}}");
        return;
    }
    k = a2 > a5 ? a2 : a5;       /* decimal places needed */
    for (i = 0; i < k; i++) pw *= 10;
    scale = pw / d;              /* = 2^(k-a2)·5^(k-a5), integer */
    scaled = n * scale;
    an = scaled < 0 ? -scaled : scaled;
    whole = an / pw;
    frac = an % pw;
    if (scaled < 0) bput(b, "-");
    bputf(b, "%lld", (long long)whole);
    snprintf(fr, sizeof fr, "%lld", (long long)frac);
    fl = (int)strlen(fr);
    for (i = 0; i < (int)k - fl; i++) pad[i] = '0';
    pad[(int)k - fl] = 0;
    bput(b, "."); bput(b, pad); bput(b, fr);
}

static void expr_src_b(KExpr *e, Buf *b) {
    int i;
    switch (e->tag) {
    case 0: bputf(b, "%lld", (long long)e->i); break;
    case 1: bput(b, e->s); break;
    case 2: {
        static const char *os[] = {"+","-","*","/","%","==","!=","<",
                                   "<=",">",">=","&&","||","++"};
        bput(b, "("); expr_src_b(e->a, b);
        bputf(b, " %s ", os[e->op]); expr_src_b(e->bb, b); bput(b, ")");
        break;
    }
    case 3: bput(b, e->op == 0 ? "-" : "!"); expr_src_b(e->a, b); break;
    case 4: bput(b, "if("); expr_src_b(e->a, b); bput(b, ") ");
        expr_src_b(e->bb, b); bput(b, " else "); expr_src_b(e->c, b); break;
    case 5: expr_src_b(e->a, b); bputf(b, ".%s", e->s); break;
    case 6: expr_src_b(e->a, b); bput(b, "["); expr_src_b(e->bb, b); bput(b, "]"); break;
    case 8:
        bput(b, e->s); bput(b, "(");
        for (i = 0; i < e->nargs; i++) {
            if (i) bput(b, ", ");
            if (e->args[i].n) bputf(b, "%s: ", e->args[i].n);
            expr_src_b(e->args[i].e, b);
        }
        bput(b, ")"); break;
    case 9:
        bput(b, "[");
        for (i = 0; i < e->nxs; i++) {
            if (i) bput(b, ", "); expr_src_b(e->xs[i], b);
        }
        bput(b, "]"); break;
    case 10:
        bput(b, "{");
        for (i = 0; i < e->nfs; i++) {
            if (i) bput(b, ", ");
            bputf(b, "%s: ", e->fs[i].n); expr_src_b(e->fs[i].e, b);
        }
        bput(b, "}"); break;
    case 11: bput(b, e->b ? "true" : "false"); break;
    case 12:
        rat_to_dec(e->i, e->d, b);
        break;
    case 13:
        bput(b, "\""); bput(b, e->s); bput(b, "\""); break;
    }
}

static void write_ast_json(Item *items, const char *file, FILE *f) {
    fputs("{\"module_annotations\":[],\"items\":[", f);
    /* the real frontend injects `import std/compiler` first */
    fprintf(f, "{\"import_decl\":{\"path\":\"std/compiler\",\"local_name\":\"std.compiler\",\"module\":\"%s\"}}",
            file);
    for (Item *it = items; it; it = it->next) {
        fputc(',', f);
        switch (it->kind) {
        case 0:
            fputs("{\"import_decl\":{\"path\":", f);
            jesc(f, it->import_path);
            fputs(",\"local_name\":", f);
            jesc(f, it->import_path);
            fprintf(f, ",\"module\":\"%s\"}}", file);
            break;
        case 1: {
            int i;
            fputs("{\"event_decl\":{\"path\":{\"module_qualifier\":null,\"segments\":[", f);
            jesc(f, it->name);
            fputs("]},\"input\":{\"fields\":[", f);
            for (i = 0; i < it->nfields; i++) {
                if (i) fputc(',', f);
                fputs("{\"name\":", f); jesc(f, it->fields[i].n);
                fputs(",\"type\":", f); jesc(f, it->fields[i].t);
                fputs(",\"module_path\":null,\"phantom\":null,\"is_source\":false,\"is_file\":false,\"is_embed_file\":false,\"is_expression\":false,\"is_invocation_meta\":false,\"expression\":null,\"expression_str\":null,\"owns_expression\":false,\"default\":null}", f);
            }
            fputs("],\"is_wildcard\":false},\"branches\":[", f);
            for (i = 0; i < it->nbranches; i++) {
                if (i) fputc(',', f);
                fputs("{\"name\":", f); jesc(f, it->branches[i]);
                fputs(",\"kind\":\"terminal\",\"resume\":null,\"resume_phantom\":null,\"is_optional\":false,\"is_panic\":false,\"payload\":{\"fields\":[]}}", f);
            }
            fputs("],\"return_type\":", f);
            if (it->ret_type) jesc(f, it->ret_type); else fputs("null", f);
            fprintf(f, ",\"return_phantom\":null,\"is_public\":%s,\"is_implicit_flow\":false,\"annotations\":[],\"prose\":\"\",\"is_pure\":false,\"is_transitively_pure\":false,\"module\":\"%s\"}}",
                    it->is_pub ? "true" : "false", file);
            break;
        }
        case 2: {
            Buf b = {0, 0, 0};
            expr_src_b(it->bare, &b);
            fputs("{\"immediate_impl\":{\"event_path\":{\"module_qualifier\":null,\"segments\":[", f);
            jesc(f, it->name);
            fputs("]},\"value\":{\"branch_name\":\"\",\"fields\":[],\"plain_value\":", f);
            jesc(f, b.p ? b.p : "");
            fprintf(f, ",\"has_expressions\":true,\"is_bare_return\":true},\"annotations\":[],\"module\":\"%s\",\"is_impl\":false}}", file);
            break;
        }
        case 3:
            /* subflow impl → flow with impl_of */
            fputs("{\"flow\":{\"invocation\":{\"event\":[", f);
            jesc(f, it->flow->head->name);
            fputs("],\"args\":[", f);
            {
                int i;
                for (i = 0; i < it->flow->head->nargs; i++) {
                    Buf ab = {0, 0, 0};
                    if (i) fputc(',', f);
                    fputs("{\"name\":", f);
                    if (it->flow->head->args[i].n) jesc(f, it->flow->head->args[i].n);
                    else jesc(f, "");
                    fputs(",\"value\":", f);
                    expr_src_b(it->flow->head->args[i].e, &ab);
                    jesc(f, ab.p ? ab.p : "");
                    fputc('}', f);
                }
            }
            fputs("],\"variant\":null},\"continuations\":[", f);
            {
                int i;
                for (i = 0; i < it->flow->narms; i++) {
                    ArmD *a = it->flow->arms[i];
                    Buf cb = {0, 0, 0};
                    if (i) fputc(',', f);
                    fputs("{\"branch\":", f); jesc(f, a->branch);
                    fprintf(f, ",\"kind\":\"terminal\",\"is_catchall\":%s,\"binding\":",
                            a->catchall ? "true" : "false");
                    if (a->bind) jesc(f, a->bind); else fputs("null", f);
                    fputs(",\"binding_type\":\"branch_payload\",\"condition\":", f);
                    if (a->cond) { expr_src_b(a->cond, &cb); jesc(f, cb.p ? cb.p : ""); }
                    else fputs("null", f);
                    fputs(",\"step\":", f);
                    if (a->kind == 1) {      /* produce */
                        Buf pb = {0, 0, 0};
                        expr_src_b(a->produce, &pb);
                        fputs("{\"type\":\"produce\",\"plain_value\":", f);
                        jesc(f, pb.p ? pb.p : "");
                        fputs("}", f);
                    } else if (a->kind == 2) {  /* ctor */
                        fputs("{\"type\":\"branch_constructor\",\"branch_constructor\":{\"branch_name\":", f);
                        jesc(f, a->target);
                        fputs(",\"fields\":[],\"plain_value\":", f);
                        if (a->produce) { Buf pb = {0,0,0}; expr_src_b(a->produce, &pb); jesc(f, pb.p?pb.p:""); }
                        else fputs("null", f);
                        fputs(",\"has_expressions\":", f);
                        fputs(a->produce ? "true" : "false", f);
                        fputs(",\"is_bare_return\":false}}", f);
                    } else if (a->kind == 3 || a->kind == 4) { /* invoke/jump */
                        int j;
                        fputs("{\"type\":\"invocation\",\"invocation\":{\"event\":[", f);
                        if (a->kind == 4)
                            fprintf(f, "\"@%s\"", a->target);
                        else
                            jesc(f, a->target);
                        fputs("],\"args\":[", f);
                        for (j = 0; j < a->inv->nargs; j++) {
                            Buf ab = {0,0,0};
                            if (j) fputc(',', f);
                            fputs("{\"name\":", f);
                            if (a->inv->args[j].n) jesc(f, a->inv->args[j].n);
                            else jesc(f, "");
                            fputs(",\"value\":", f);
                            expr_src_b(a->inv->args[j].e, &ab);
                            jesc(f, ab.p ? ab.p : "");
                            fputc('}', f);
                        }
                        fputs("],\"variant\":null}}", f);
                    } else {
                        fputs("{\"type\":\"terminal\"}", f);
                    }
                    fprintf(f, ",\"continuations\":[],\"location\":{\"file\":\"%s\",\"line\":%d,\"col\":0}}",
                            file, it->line);
                }
            }
            fputs("],\"pre_label\":", f);
            if (it->flow->pre) jesc(f, it->flow->pre); else fputs("null", f);
            fputs(",\"impl_of\":[", f);
            jesc(f, it->name);
            fprintf(f, "],\"location\":{\"file\":\"%s\",\"line\":%d,\"col\":0}}}",
                    file, it->line);
            break;
        case 4:
            /* top-level flow — same shape, impl_of null */
            fputs("{\"flow\":{\"invocation\":{\"event\":[", f);
            jesc(f, it->flow->head->name);
            fputs("],\"args\":[],\"variant\":null},\"continuations\":[],\"pre_label\":null,\"impl_of\":null,\"location\":{\"file\":\"", f);
            fputs(file, f);
            fprintf(f, "\",\"line\":%d,\"col\":0}}}", it->line);
            break;
        }
    }
    fprintf(f, "],\"main_module_name\":\"%s\",\"parts\":[]}", file);
}

/* ================= JSON reader (for --lower) ================= */

typedef struct Jv Jv;
struct Jv {
    int k;            /* 0 null 1 bool 2 num 3 str 4 arr 5 obj */
    int b;
    double num; char *numraw;
    char *s;
    Jv **xs; int nxs;
    struct { char *k; Jv *v; } *fs; int nfs;
};

static const char *jp;
static int jws(void) { while (*jp == ' ' || *jp == '\t' || *jp == '\n' || *jp == '\r') jp++; return *jp != 0; }
static Jv *jnew(int k) { Jv *v = xmalloc(sizeof(Jv)); memset(v, 0, sizeof *v); v->k = k; return v; }

static Jv *jparse(void) {
    Jv *v;
    if (!jws()) return 0;
    if (*jp == 'n' && !strncmp(jp, "null", 4)) { jp += 4; return jnew(0); }
    if (*jp == 't' && !strncmp(jp, "true", 4)) { jp += 4; v = jnew(1); v->b = 1; return v; }
    if (*jp == 'f' && !strncmp(jp, "false", 5)) { jp += 5; v = jnew(1); return v; }
    if (*jp == '"') {
        Buf b = {0,0,0};
        jp++;
        while (*jp && *jp != '"') {
            if (*jp == '\\' && jp[1]) {
                jp++;
                switch (*jp) {
                case 'n': bput(&b, "\n"); break;
                case 't': bput(&b, "\t"); break;
                default: { char c2[2] = {*jp, 0}; bput(&b, c2); break; }
                }
                jp++;
                continue;
            }
            { char c2[2] = {*jp, 0}; bput(&b, c2); }
            jp++;
        }
        if (!*jp) return 0;
        v = jnew(3);
        v->s = b.p ? b.p : xstrdup("");
        jp++;
        return v;
    }
    if (*jp == '-' || (*jp >= '0' && *jp <= '9')) {
        const char *b = jp;
        if (*jp == '-') jp++;
        while (*jp >= '0' && *jp <= '9') jp++;
        if (*jp == '.') { jp++; while (*jp >= '0' && *jp <= '9') jp++; }
        v = jnew(2);
        v->numraw = xstrndup(b, (size_t)(jp - b));
        v->num = strtod(v->numraw, 0);
        return v;
    }
    if (*jp == '[') {
        int cap = 8;
        jp++;
        v = jnew(4);
        v->xs = xmalloc(cap * sizeof(Jv *));
        while (1) {
            Jv *e;
            jws();
            if (*jp == ']') { jp++; return v; }
            e = jparse();
            if (!e) return 0;
            if (v->nxs == cap) {
                cap *= 2;
                { Jv **nx = xmalloc(cap * sizeof(Jv *));
                  memcpy(nx, v->xs, v->nxs * sizeof(Jv *)); v->xs = nx; }
            }
            v->xs[v->nxs++] = e;
            jws();
            if (*jp == ',') { jp++; continue; }
            if (*jp == ']') { jp++; return v; }
            return 0;
        }
    }
    if (*jp == '{') {
        int cap = 8;
        jp++;
        v = jnew(5);
        v->fs = xmalloc(cap * sizeof(*v->fs));
        while (1) {
            Jv *k, *val;
            jws();
            if (*jp == '}') { jp++; return v; }
            k = jparse();
            if (!k || k->k != 3) return 0;
            jws();
            if (*jp != ':') return 0;
            jp++;
            val = jparse();
            if (!val) return 0;
            if (v->nfs == cap) {
                cap *= 2;
                { void *nf = xmalloc(cap * sizeof(*v->fs));
                  memcpy(nf, v->fs, v->nfs * sizeof(*v->fs)); v->fs = nf; }
            }
            v->fs[v->nfs].k = k->s; v->fs[v->nfs].v = val; v->nfs++;
            jws();
            if (*jp == ',') { jp++; continue; }
            if (*jp == '}') { jp++; return v; }
            return 0;
        }
    }
    return 0;
}

static Jv *jget(Jv *o, const char *k) {
    int i;
    if (!o || o->k != 5) return 0;
    for (i = 0; i < o->nfs; i++)
        if (!strcmp(o->fs[i].k, k)) return o->fs[i].v;
    return 0;
}
static char *jstr(Jv *o, const char *k) {
    Jv *v = jget(o, k);
    return v && v->k == 3 ? v->s : 0;
}
static Jv *jarr(Jv *o, const char *k) {
    Jv *v = jget(o, k);
    return v && v->k == 4 ? v : 0;
}
static char *jseg0(Jv *path) {    /* event path segments[0] */
    Jv *seg = jarr(path, "segments");
    if (!seg || seg->nxs == 0 || seg->xs[0]->k != 3) return 0;
    return seg->xs[0]->s;
}

/* ================= lower: ast.json + case row -> [flow-eval] claim == */

/* wire s-expr writer for KExpr */
static void sx_expr(KExpr *e, Buf *b, char **err);

static int is_builtin(const char *n) {
    static const char *t[] = {"as","intCast","truncate","divTrunc","rem",
                              "mod","len","intToString",0};
    int i;
    for (i = 0; t[i]; i++) if (!strcmp(n, t[i])) return 1;
    return 0;
}

static void sx_lit(KExpr *e, Buf *b, char **err) {
    int i;
    switch (e->tag) {
    case 0: bputf(b, "(int %lld)", (long long)e->i); break;
    case 12: bputf(b, "(float %lld %lld)", (long long)e->i, (long long)e->d); break;
    case 13: bput(b, "(str "); bput(b, "\""); bput(b, e->s); bput(b, "\")"); break;
    case 11: bputf(b, "(bool %s)", e->b ? "true" : "false"); break;
    case 9:
        bput(b, "(arr");
        for (i = 0; i < e->nxs; i++) {
            bput(b, " "); sx_lit(e->xs[i], b, err);
            if (*err) return;
        }
        bput(b, ")"); break;
    case 10:
        bput(b, "(cell");
        for (i = 0; i < e->nfs; i++) {
            bputf(b, " (%s ", e->fs[i].n); sx_lit(e->fs[i].e, b, err);
            if (*err) return;
            bput(b, ")");
        }
        bput(b, ")"); break;
    default:
        *err = xstrdup("non-literal inside literal position");
        break;
    }
}

static void sx_expr(KExpr *e, Buf *b, char **err) {
    static const char *ops[] = {"add","sub","mul","div","mod","eq","ne",
                                "lt","le","gt","ge","and","or","concat"};
    int i;
    switch (e->tag) {
    case 0: case 11: case 12: case 13: case 9: case 10:
        bput(b, "(lit "); sx_lit(e, b, err); bput(b, ")"); break;
    case 1: bputf(b, "(var %s)", e->s); break;
    case 2:
        bputf(b, "(bin %s ", ops[e->op]); sx_expr(e->a, b, err);
        bput(b, " "); sx_expr(e->bb, b, err); bput(b, ")"); break;
    case 3:
        bputf(b, "(un %s ", e->op == 0 ? "neg" : "not");
        sx_expr(e->a, b, err); bput(b, ")"); break;
    case 4:
        bput(b, "(cond "); sx_expr(e->a, b, err); bput(b, " ");
        sx_expr(e->bb, b, err); bput(b, " "); sx_expr(e->c, b, err);
        bput(b, ")"); break;
    case 5: bput(b, "(field "); sx_expr(e->a, b, err);
        bputf(b, " %s)", e->s); break;
    case 6: bput(b, "(index "); sx_expr(e->a, b, err); bput(b, " ");
        sx_expr(e->bb, b, err); bput(b, ")"); break;
    case 8:
        if (!is_builtin(e->s)) {
            *err = xasprintf("invocation '", e->s);
            *err = xasprintf(*err, "' inside expression — callables "
                           "invoke through flow nodes, not exprs");
            return;
        }
        bputf(b, "(builtin %s", e->s);
        for (i = 0; i < e->nargs; i++) {
            if (e->args[i].n) {
                *err = xstrdup("builtin args are positional");
                return;
            }
            bput(b, " "); sx_expr(e->args[i].e, b, err);
            if (*err) return;
        }
        bput(b, ")"); break;
    }
}

static void sx_arm(ArmD *a, Buf *b, char **err);

static void sx_armnode(ArmD *a, Buf *b, char **err) {
    int i;
    switch (a->kind) {
    case -1: case 0: bput(b, "terminal"); break;
    case 1: bput(b, "(produce "); sx_expr(a->produce, b, err); bput(b, ")"); break;
    case 2: {
        bputf(b, "(ctor %s ", a->target);
        if (a->produce) sx_expr(a->produce, b, err);
        else bput(b, "(lit (cell))");
        bput(b, ")"); break;
    }
    case 3: case 4: {
        bputf(b, "(%s %s", a->kind == 4 ? "jump" : "invoke", a->target);
        for (i = 0; i < a->inv->nargs; i++) {
            if (!a->inv->args[i].n) {
                *err = xstrdup("invoke/jump args must be named");
                return;
            }
            bputf(b, " (%s ", a->inv->args[i].n);
            sx_expr(a->inv->args[i].e, b, err);
            if (*err) return;
            bput(b, ")");
        }
        bput(b, ")"); break;
    }
    }
}

static void sx_arm(ArmD *a, Buf *b, char **err) {
    int i;
    bput(b, "(arm");
    if (a->catchall) bput(b, " catchall");
    else if (a->branch[0]) bputf(b, " (tag %s)", a->branch);
    if (a->bind) bputf(b, " (bind %s)", a->bind);
    if (a->cond) {
        bput(b, " (when "); sx_expr(a->cond, b, err); bput(b, ")");
        if (*err) return;
    }
    if (a->kind != -1) {
        bput(b, " (node "); sx_armnode(a, b, err); bput(b, ")");
        if (*err) return;
    }
    if (a->nconts) {
        bput(b, " (conts");
        for (i = 0; i < a->nconts; i++) {
            bput(b, " "); sx_arm(a->conts[i], b, err);
            if (*err) return;
        }
        bput(b, ")");
    }
    bput(b, ")");
}

/* --- the JSON-AST → same ArmD tree (lower reads canon items) --- */

static KExpr *expr_from_src(const char *src, char **err) {
    Tks *ts;
    KExpr *e;
    if (!src || !*src) { *err = xstrdup("empty expression"); return 0; }
    ts = lex_k(src, "<ast expr>", err);
    if (!ts) return 0;
    e = parse_expr(ts, err);
    if (!e) return 0;
    if (!at_kind(ts, 5)) {
        *err = xstrdup("trailing tokens in expression");
        return 0;
    }
    return e;
}

static int inv_from_ast(Jv *inv, Inv *out, char **err) {
    Jv *ev = jget(inv, "event");
    Jv *args = jarr(inv, "args");
    int i;
    memset(out, 0, sizeof *out);
    if (!ev || ev->k != 4 || ev->nxs != 1 || ev->xs[0]->k != 3) {
        *err = xstrdup("invocation.event must be [name]");
        return 0;
    }
    {
        const char *s = ev->xs[0]->s;
        if (s[0] == '@') { out->qual = xstrdup("@"); out->name = xstrdup(s + 1); }
        else out->name = xstrdup(s);
    }
    if (args) {
        out->nargs = args->nxs;
        out->args = out->nargs ? xmalloc(out->nargs * sizeof(*out->args)) : 0;
        for (i = 0; i < args->nxs; i++) {
            char *an = jstr(args->xs[i], "name");
            char *av = jstr(args->xs[i], "value");
            out->args[i].n = an && *an ? an : 0;
            out->args[i].e = expr_from_src(av ? av : "", err);
            if (!out->args[i].e) return 0;
        }
    }
    return 1;
}

static int arm_from_ast(Jv *c, ArmD *a, char **err) {
    Jv *step, *conts;
    char *br = jstr(c, "branch");
    char *bind = jstr(c, "binding");
    Jv *catchall = jget(c, "is_catchall");
    char *cond = jstr(c, "condition");
    int i;
    memset(a, 0, sizeof *a);
    a->kind = -1;
    a->branch = br ? br : "";
    a->catchall = catchall && catchall->k == 1 && catchall->b;
    a->bind = bind;
    if (cond) {
        a->cond = expr_from_src(cond, err);
        if (!a->cond) return 0;
    }
    step = jget(c, "step");
    if (step && step->k == 5) {
        char *st = jstr(step, "type");
        if (st && !strcmp(st, "produce")) {
            a->kind = 1;
            a->produce = expr_from_src(jstr(step, "plain_value"), err);
            if (!a->produce) return 0;
        } else if (st && !strcmp(st, "branch_constructor")) {
            Jv *bc = jget(step, "branch_constructor");
            a->kind = 2;
            a->target = xstrdup(jstr(bc, "branch_name"));
            if (jstr(bc, "plain_value")) {
                a->produce = expr_from_src(jstr(bc, "plain_value"), err);
                if (!a->produce) return 0;
            }
        } else if (st && !strcmp(st, "invocation")) {
            Jv *inv = jget(step, "invocation");
            a->inv = xmalloc(sizeof(Inv));
            if (!inv_from_ast(inv, a->inv, err)) return 0;
            if (a->inv->qual && a->inv->qual[0] == '@') {
                a->kind = 4; a->target = a->inv->name;
            } else {
                a->kind = 3; a->target = a->inv->name;
            }
        } else {
            a->kind = 0;          /* terminal */
        }
    } else {
        a->kind = 0;
    }
    conts = jarr(c, "continuations");
    if (conts) {
        a->nconts = conts->nxs;
        a->conts = a->nconts ? xmalloc(a->nconts * sizeof(ArmD *)) : 0;
        for (i = 0; i < a->nconts; i++) {
            a->conts[i] = xmalloc(sizeof(ArmD));
            if (!arm_from_ast(conts->xs[i], a->conts[i], err)) return 0;
        }
    }
    return 1;
}

/* emit the claim for a program ast + case row */
static int lower(Jv *ast, Jv *cspec, Buf *out, char **err) {
    Jv *items = jarr(ast, "items");
    Buf graph = {0,0,0}, oracle = {0,0,0};
    char *entry;
    int64_t fuel;
    Jv *expect;
    int i;
    if (!items) { *err = xstrdup("ast: no items"); return 0; }
    entry = jstr(cspec, "entry");
    if (!entry) { *err = xstrdup("case: no entry"); return 0; }
    {
        Jv *fv = jget(cspec, "fuel");
        fuel = fv && fv->k == 2 ? (int64_t)fv->num : 64;
    }
    bput(&graph, "(graph");
    /* pass 1: impls + tor-decls (decl-only → thunk) */
    {
        /* collect tor decls and impls by name */
        typedef struct { char *n; int has_impl; } DeclSeen;
        DeclSeen *seen = xmalloc(items->nxs * sizeof(DeclSeen));
        int nseen = 0;
        for (i = 0; i < items->nxs; i++) {
            Jv *it = items->xs[i];
            if (jget(it, "event_decl")) {
                Jv *d = jget(it, "event_decl");
                char *nm = jseg0(jget(d, "path"));
                int j, dup = 0;
                if (!nm) { *err = xstrdup("event_decl: no name"); return 0; }
                for (j = 0; j < nseen; j++)
                    if (!strcmp(seen[j].n, nm)) dup = 1;
                if (!dup) { seen[nseen].n = nm; seen[nseen].has_impl = 0; nseen++; }
            } else if (jget(it, "immediate_impl")) {
                Jv *im = jget(it, "immediate_impl");
                char *nm = jseg0(jget(im, "event_path"));
                Jv *val = jget(im, "value");
                char *pv = jstr(val, "plain_value");
                char *bn = jstr(val, "branch_name");
                KExpr *e;
                int j, dup = 0;
                for (j = 0; j < nseen; j++)
                    if (!strcmp(seen[j].n, nm)) { dup = 1; seen[j].has_impl = 1; }
                if (!dup) { seen[nseen].n = nm; seen[nseen].has_impl = 1; nseen++; }
                if (bn && *bn) {
                    *err = xasprintf("impl '", nm);
                    *err = xasprintf(*err, "' => branch out of subset");
                    return 0;
                }
                e = expr_from_src(pv ? pv : "", err);
                if (!e) return 0;
                bputf(&graph, " (def %s (bare ", nm);
                sx_expr(e, &graph, err);
                if (*err) return 0;
                bput(&graph, "))");
            } else if (jget(it, "flow")) {
                Jv *fl = jget(it, "flow");
                Jv *impl = jarr(fl, "impl_of");
                Jv *inv, *conts;
                FlowD fd;
                int j;
                if (!impl || impl->nxs == 0) {
                    *err = xstrdup("top-level flow out of subset "
                                   "(wrap in an impl: name = flow)");
                    return 0;
                }
                if (impl->xs[0]->k != 3) { *err = xstrdup("impl_of bad"); return 0; }
                memset(&fd, 0, sizeof fd);
                fd.pre = jstr(fl, "pre_label");
                inv = jget(fl, "invocation");
                fd.head = xmalloc(sizeof(Inv));
                if (!inv_from_ast(inv, fd.head, err)) return 0;
                conts = jarr(fl, "continuations");
                fd.narms = conts ? conts->nxs : 0;
                fd.arms = fd.narms ? xmalloc(fd.narms * sizeof(ArmD *)) : 0;
                for (j = 0; j < fd.narms; j++) {
                    fd.arms[j] = xmalloc(sizeof(ArmD));
                    if (!arm_from_ast(conts->xs[j], fd.arms[j], err)) return 0;
                }
                {
                    char *nm = impl->xs[0]->s;
                    int dup = 0;
                    for (j = 0; j < nseen; j++)
                        if (!strcmp(seen[j].n, nm)) { dup = 1; seen[j].has_impl = 1; }
                    if (!dup) { seen[nseen].n = nm; seen[nseen].has_impl = 1; nseen++; }
                    bputf(&graph, " (def %s (subflow", nm);
                    if (fd.pre) bputf(&graph, " (label %s)", fd.pre);
                    bputf(&graph, " (head %s", fd.head->name);
                    for (j = 0; j < fd.head->nargs; j++) {
                        if (!fd.head->args[j].n) {
                            *err = xstrdup("head args must be named");
                            return 0;
                        }
                        bputf(&graph, " (%s ", fd.head->args[j].n);
                        sx_expr(fd.head->args[j].e, &graph, err);
                        if (*err) return 0;
                        bput(&graph, ")");
                    }
                    bput(&graph, ")");
                    for (j = 0; j < fd.narms; j++) {
                        bput(&graph, " ");
                        sx_arm(fd.arms[j], &graph, err);
                        if (*err) return 0;
                    }
                    bput(&graph, "))");
                }
            }
        }
        /* decl-only names → thunk */
        for (i = 0; i < nseen; i++)
            if (!seen[i].has_impl)
                bputf(&graph, " (def %s thunk)", seen[i].n);
    }
    bput(&graph, ")");

    /* oracle leaves from the case row */
    bput(&oracle, "(oracle");
    {
        Jv *ol = jarr(cspec, "oracle");
        if (ol) {
            for (i = 0; i < ol->nxs; i++) {
                Jv *leaf = ol->xs[i];
                char *ln = jstr(leaf, "name");
                Jv *args = jget(leaf, "args");
                Jv *res = jget(leaf, "result");
                bputf(&oracle, " (leaf %s (", ln);
                if (args && args->k == 5) {
                    int j;
                    for (j = 0; j < args->nfs; j++) {
                        bputf(&oracle, "(%s ", args->fs[j].k);
                        /* leaf arg values as sx vals — small writer */
                        {
                            Jv *v = args->fs[j].v;
                            /* only scalars for now: {"int":5} {"str":"s"} */
                            if (jget(v, "int"))
                                bputf(&oracle, "(int %lld)",
                                      (long long)jget(v, "int")->num);
                            else if (jget(v, "str"))
                                bputf(&oracle, "(str \"%s\")", jget(v, "str")->s);
                            else if (jget(v, "bool"))
                                bputf(&oracle, "(bool %s)",
                                      jget(v, "bool")->b ? "true" : "false");
                            else { *err = xstrdup("oracle arg val"); return 0; }
                        }
                        bput(&oracle, ") ");
                    }
                }
                bput(&oracle, ") ");
                /* result: {"bare":v} {"tag":"b","payload":v} {"void":true} */
                if (jget(res, "void")) bput(&oracle, "(void)");
                else if (jget(res, "bare")) {
                    Jv *v = jget(res, "bare");
                    bput(&oracle, "(bare ");
                    if (jget(v, "int")) bputf(&oracle, "(int %lld)", (long long)jget(v, "int")->num);
                    else if (jget(v, "str")) bputf(&oracle, "(str \"%s\")", jget(v, "str")->s);
                    else if (jget(v, "bool")) bputf(&oracle, "(bool %s)", jget(v, "bool")->b ? "true" : "false");
                    else { *err = xstrdup("oracle bare val"); return 0; }
                    bput(&oracle, ")");
                } else if (jget(res, "tag")) {
                    Jv *v = jget(res, "payload");
                    bputf(&oracle, "(tag %s", jstr(res, "tag"));
                    if (v) {
                        bput(&oracle, " ");
                        if (jget(v, "int")) bputf(&oracle, "(int %lld)", (long long)jget(v, "int")->num);
                        else if (jget(v, "str")) bputf(&oracle, "(str \"%s\")", jget(v, "str")->s);
                        else if (jget(v, "bool")) bputf(&oracle, "(bool %s)", jget(v, "bool")->b ? "true" : "false");
                        else { *err = xstrdup("oracle payload val"); return 0; }
                    }
                    bput(&oracle, ")");
                } else { *err = xstrdup("oracle result"); return 0; }
                bput(&oracle, ")");
            }
        }
    }
    bput(&oracle, ")");

    /* entry args from the case row */
    {
        Buf ea = {0,0,0};
        Jv *args = jget(cspec, "args");
        bputf(&ea, "(entry %s", entry);
        if (args && args->k == 5) {
            for (i = 0; i < args->nfs; i++) {
                Jv *v = args->fs[i].v;
                bputf(&ea, " (%s ", args->fs[i].k);
                if (jget(v, "int")) bputf(&ea, "(int %lld)", (long long)jget(v, "int")->num);
                else if (jget(v, "str")) bputf(&ea, "(str \"%s\")", jget(v, "str")->s);
                else if (jget(v, "bool")) bputf(&ea, "(bool %s)", jget(v, "bool")->b ? "true" : "false");
                else { *err = xstrdup("entry arg val"); return 0; }
                bput(&ea, ")");
            }
        }
        bput(&ea, ")");
        /* assemble the claim */
        bput(out, "[flow-eval] (");
        bput(out, ea.p ? ea.p : "");
        bputf(out, " (fuel %lld) ", (long long)fuel);
        expect = jget(cspec, "expect");
        bput(out, "(result ");
        if (jstr(expect, "refuse") || (expect && expect->k == 3 && !strcmp(expect->s, "refuse")))
            bput(out, "refuse");
        else if (jget(expect, "void"))
            bput(out, "(void)");
        else if (jget(expect, "bare")) {
            Jv *v = jget(expect, "bare");
            bput(out, "(bare ");
            if (jget(v, "int")) bputf(out, "(int %lld)", (long long)jget(v, "int")->num);
            else if (jget(v, "float")) {
                Jv *fl = jget(v, "float");
                bputf(out, "(float %lld %lld)",
                      (long long)fl->xs[0]->num, (long long)fl->xs[1]->num);
            }
            else if (jget(v, "str")) bputf(out, "(str \"%s\")", jget(v, "str")->s);
            else if (jget(v, "bool")) bputf(out, "(bool %s)", jget(v, "bool")->b ? "true" : "false");
            else { *err = xstrdup("expect bare val"); return 0; }
            bput(out, ")");
        } else if (jget(expect, "tag")) {
            Jv *v = jget(expect, "payload");
            bputf(out, "(tag %s", jstr(expect, "tag"));
            if (v) {
                bput(out, " ");
                if (jget(v, "int")) bputf(out, "(int %lld)", (long long)v->num);
                else if (jget(v, "str")) bputf(out, "(str \"%s\")", jget(v, "str")->s);
                else { *err = xstrdup("expect payload val"); return 0; }
            }
            bput(out, ")");
        } else { *err = xstrdup("expect row"); return 0; }
        bput(out, ") ");
        bput(out, graph.p); bput(out, " ");
        bput(out, oracle.p); bput(out, ")");
    }
    return 1;
}

/* ================= main ================= */

static char *file_read(const char *path) {
    FILE *f = fopen(path, "rb");
    long n; char *b;
    if (!f) return 0;
    fseek(f, 0, SEEK_END); n = ftell(f); fseek(f, 0, SEEK_SET);
    if (n < 0) { fclose(f); return 0; }
    b = xmalloc((size_t)n + 1);
    if (fread(b, 1, (size_t)n, f) != (size_t)n) { fclose(f); return 0; }
    fclose(f); b[n] = 0;
    return b;
}

static const char *base_name(const char *p) {
    const char *s = strrchr(p, '/');
    if (!s) s = strrchr(p, '\\');
    return s ? s + 1 : p;
}

int main(int argc, char **argv) {
    char *err = 0;
    if (argc == 2) {
        /* parse → ast.json */
        char *src = file_read(argv[1]);
        Tks *ts;
        Item *items;
        const char *mod;
        if (!src) { fprintf(stderr, "refuse: cannot read %s\n", argv[1]); return 2; }
        ts = lex_k(src, argv[1], &err);
        if (!ts) { fprintf(stderr, "refuse: %s\n", err); return 2; }
        items = parse_program(ts, &err);
        if (!items) { fprintf(stderr, "refuse: %s\n", err); return 2; }
        {
            const char *b = base_name(argv[1]);
            char *dot = strrchr(b, '.');
            mod = dot ? xstrndup(b, (size_t)(dot - b)) : b;
        }
        write_ast_json(items, mod, stdout);
        fputc('\n', stdout);
        return 0;
    }
    if (argc == 5 && !strcmp(argv[1], "--lower")) {
        /* ast.json + cases.json KEY → claim */
        char *asrc = file_read(argv[2]);
        char *csrc = file_read(argv[3]);
        Jv *ast, *cases, *cspec;
        Buf out = {0,0,0};
        if (!asrc || !csrc) { fputs("refuse: cannot read inputs\n", stderr); return 2; }
        jp = asrc; ast = jparse();
        jp = csrc; cases = jparse();
        if (!ast || !cases) { fputs("refuse: bad json\n", stderr); return 2; }
        {
            Jv *rows = jget(cases, "cases");
            cspec = rows ? jget(rows, argv[4]) : 0;
        }
        if (!cspec) {
            fprintf(stderr, "refuse: no case row '%s'\n", argv[4]);
            return 2;
        }
        if (!lower(ast, cspec, &out, &err)) {
            fprintf(stderr, "refuse: %s\n", err);
            return 2;
        }
        fputs(out.p ? out.p : "", stdout);
        fputc('\n', stdout);
        return 0;
    }
    fputs("usage: korufe FILE.k\n"
          "       korufe --lower FILE.ast.json CASES.json KEY\n",
          stderr);
    return 2;
}
