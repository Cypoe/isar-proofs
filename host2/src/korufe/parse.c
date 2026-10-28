/* host2 korufe — parse leg.  Contract in korufe.h. */
#include "korufe.h"

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

KExpr *parse_expr(Tks *s, char **err);
static int is_ident_tk(Tks *s);
static KExpr *parse_postfix(Tks *s, char **err);

/* koru puns: `f(x)` binds param `x` from a bare `x`; the pun name
   is the expr's trailing ident (var or field tail).  Defined with
   the lowering helpers; used at parse for PARSE005 parity. */
static char *pun_name(KExpr *e);

/* `name: expr` where expr puns to `name` is refused upstream
   (PARSE005 redundant explicit label); a repeated label in one call
   is likewise refused. */
static int check_arg_label(Tks *s, char *an, KExpr *ae,
                           NArg *prev, int nprev, char **err) {
    int k;
    if (!an) return 1;
    if (pun_name(ae) && !strcmp(pun_name(ae), an)) {
        fail_at(s, err, "redundant explicit label — the value "
                        "already puns to this param");
        return 0;
    }
    for (k = 0; k < nprev; k++)
        if (prev[k].n && !strcmp(prev[k].n, an)) {
            fail_at(s, err, "duplicate arg label in call");
            return 0;
        }
    return 1;
}

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
        if (!check_arg_label(s, an, ae, e->args, e->nargs, err))
            return 0;
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
    if (at(s, "@")) {
        /* `@name(args)` — koru's builtin-call spelling.  Builtins are
           admitted inside expressions where a bare `name(...)` is a
           tor call and refuses upstream (KORU104). */
        KExpr *e = ke_new(0);
        e->tag = 7;
        s->i++;
        if (!is_ident_tk(s)) { fail_at(s, err, "builtin name after '@'"); return 0; }
        e->s = xstrdup(next_tk(s)->text);
        if (!eat(s, "(")) { fail_at(s, err, "'(' after @builtin"); return 0; }
        return parse_call_args(s, err, e);
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

static KExpr *parse_unary(Tks *s, char **err) {
    KExpr *a;
    snl(s);
    if (at(s, "!")) {
        s->i++;
        a = parse_unary(s, err);
        if (!a) return 0;
        return ke_un(1, a);          /* not */
    }
    if (at(s, "-")) {
        s->i++;
        a = parse_unary(s, err);
        if (!a) return 0;
        /* koru parity: the operand binds at POSTFIX precedence
           (`-(7) / 2` is `(negate 7) / 2`, never `negate (7 / 2)`;
           koru's parsePrimary does the same), and `-` always builds
           the unary node — no literal fold (folding corrupts
           quotation for the emit leg). */
        return ke_un(0, a);          /* neg */
    }
    return parse_postfix(s, err);
}

static KExpr *parse_bin(Tks *s, char **err, int minprec) {
    KExpr *l = parse_unary(s, err);
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

KExpr *parse_expr(Tks *s, char **err) {
    snl(s);
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
                if (!check_arg_label(s, an, ae,
                                     v->args, v->nargs, err))
                    return 0;
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
    /* `inv: name` — koru's return_binding.  The wire expresses it as
       the following `|>` continuation arm's (bind name); whoever
       parses this inv threads it there and refuses if no `|>`
       follows. */
    if (at(s, ":")) {
        s->i++;
        if (!is_ident_tk(s)) { fail_at(s, err, "bind name after ':'"); return 0; }
        v->retbind = xstrdup(next_tk(s)->text);
    }
    return v;
}

/* append helper: grow an arms list */
static void arm_push(ArmD ***xs, int *n, int *cap, ArmD *a) {
    if (*n == *cap) {
        *cap *= 2;
        { ArmD **na = xmalloc(*cap * sizeof(ArmD *));
          memcpy(na, *xs, *n * sizeof(ArmD *));
          *xs = na; }
    }
    (*xs)[(*n)++] = a;
}

/* `|>` step already consumed — parse the invocation, return a fresh
   invoke/jump arm carrying it.  `branch` stays "" — koru's chain
   marker; the WIRE (whose cont arms dispatch, and refuse unnamed
   arms under a bare result) gets the decorative tag `_chain` at
   sx-emit time, matching koru's own golden convention of naming
   cont arms that ride a bare result.  A `|>` step after a tagged
   producer is not expressible on the wire and refuses at eval. */
static ArmD *parse_cont_step(Tks *s, char **err, char *bind) {
    ArmD *a = xmalloc(sizeof(ArmD));
    memset(a, 0, sizeof *a);
    a->kind = -1;
    a->branch = "";
    a->bind = bind;
    a->inv = parse_inv(s, err, 1);
    if (!a->inv) return 0;
    a->target = a->inv->name;
    a->kind = (a->inv->qual && a->inv->qual[0] == '@') ? 4 : 3;
    return a;
}

static ArmD *parse_arm(Tks *s, char **err) {
    /* consumed the leading '|' already — s->t[s->i-1] is it */
    long pipe_pos = s->i > 0 ? s->t[s->i - 1].pos : -1;
    ArmD *a = xmalloc(sizeof(ArmD));
    memset(a, 0, sizeof *a);
    a->kind = -1;
    a->branch = "";
    snl(s);
    if (at(s, "*")) {
        /* koru's residual arm is `|* Meta e |>` — it binds the
           residual RECORD through a metatype, a shape the wire
           catchall does not carry.  Spaced `| *` is the retired
           deref glyph upstream.  Both refuse here. */
        if (peek(s)->pos != pipe_pos + 1)
            fail_at(s, err, "'| *' is the retired deref spelling — "
                            "the residual arm is glued '|*'");
        else
            fail_at(s, err, "residual '|*' has no subset spelling — "
                            "koru binds it through a metatype "
                            "(`|* Meta e |>`)");
        return 0;
    } else if (is_ident_tk(s)) {
        a->branch = xstrdup(next_tk(s)->text);
    } else {
        fail_at(s, err, "arm branch or catchall");
        return 0;
    }
    if (is_ident_tk(s) && !at(s, "when"))     /* bind — `when` is
                                               the guard keyword */
        a->bind = xstrdup(next_tk(s)->text);
    if (at(s, "when")) {                      /* guard */
        /* bare `when <cond>` — koru reads the condition to the next
           `->`/`|>`/`=>` delimiter.  Glued `when(` is call-shaped
           upstream (an unguarded arm → SHAPE002), so refuse it. */
        long wpos = peek(s)->pos;
        s->i++;
        if (at(s, "(") && peek(s)->pos == wpos + 4) {
            fail_at(s, err, "'when(' reads as a call upstream — "
                            "spell 'when <cond>'");
            return 0;
        }
        a->cond = parse_expr(s, err);
        if (!a->cond) return 0;
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
        ArmD *tail;
        char *pend;
        s->i++;
        a->kind = 3;
        a->inv = parse_inv(s, err, 1);
        if (!a->inv) return 0;
        a->target = a->inv->name;
        if (a->inv->qual && a->inv->qual[0] == '@') a->kind = 4;
        /* chain: `|> a(): d |> b(d) |> c()` — each following `|>`
           nests as the previous step's sole continuation arm, bound
           by the step's `: bind`. */
        tail = a;
        pend = a->inv->retbind;
        for (;;) {
            ArmD *nx;
            snl(s);
            if (!at(s, "|>")) break;
            s->i++;
            nx = parse_cont_step(s, err, pend);
            if (!nx) return 0;
            pend = nx->inv->retbind;
            tail->conts = xmalloc(sizeof(ArmD *));
            tail->conts[0] = nx; tail->nconts = 1;
            tail = nx;
        }
        if (pend) {
            fail_at(s, err, "trailing 'inv: bind' has no continuation");
            return 0;
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
        char *pend = f->head->retbind;
        f->arms = xmalloc(cap * sizeof(ArmD *));
        f->narms = 0;
        for (;;) {
            ArmD *a;
            snl(s);
            if (at(s, "|>")) {
                /* `head(args): d |> next` — the `: bind` attaches to
                   the continuation arm; further `|>` steps continue
                   the chain as sibling arms at this level.  Koru
                   forbids a chain after branch rows at one level —
                   "no source spelling" — refuse likewise. */
                if (f->narms) {
                    fail_at(s, err, "'|>' chain after '|' arms has no "
                                    "koru spelling — order chains first");
                    return 0;
                }
                s->i++;
                a = parse_cont_step(s, err, pend);
                if (!a) return 0;
                pend = a->inv->retbind;
                arm_push(&f->arms, &f->narms, &cap, a);
                continue;
            }
            if (!at(s, "|")) break;
            {
                int k;
                for (k = 0; k < f->narms; k++)
                    if (f->arms[k]->branch == 0 || !*f->arms[k]->branch) {
                        /* a '|' row under a preceding '|>' chain would
                           nest by indentation in koru — column scoping
                           is a named gap; refuse rather than silently
                           dispatch it on the head result */
                        fail_at(s, err, "'|' dispatch under a '|>' chain "
                                        "needs indentation scoping — out "
                                        "of subset");
                        return 0;
                    }
            }
            if (s->i + 1 < s->n &&
                strcmp(s->t[s->i + 1].text, ">") == 0) break;  /* '|>' */
            if (pend) {
                fail_at(s, err, "'inv: bind' before a '|' dispatch arm "
                                "is out of subset (use '|>' to continue)");
                return 0;
            }
            s->i++;
            a = parse_arm(s, err);
            if (!a) return 0;
            arm_push(&f->arms, &f->narms, &cap, a);
        }
        if (pend) {
            fail_at(s, err, "trailing 'inv: bind' has no continuation");
            return 0;
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

Item *parse_program(Tks *s, char **err) {
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
                    /* type tokens: `[]const T` (koru's slice
                       spelling) or a bare ident — qualifiers and
                       trailing [phantom] brackets skipped */
                    {   int slice = 0;
                        if (at(s, "[")) {
                            slice = 1;
                            s->i++;
                            if (!eat(s, "]")) {
                                fail_at(s, err, "']' closing '[]'");
                                return 0;
                            }
                            if (!eat(s, "const")) {
                                fail_at(s, err, "'const' in '[]const T'");
                                return 0;
                            }
                        }
                        if (!is_ident_tk(s)) {
                            fail_at(s, err, "field type");
                            return 0;
                        }
                        it->fields[it->nfields].t =
                            xstrdup(next_tk(s)->text);
                        if (slice)
                            it->fields[it->nfields].t =
                                xasprintf("[]const ",
                                          it->fields[it->nfields].t);
                    }
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
                    {   /* identity payload `| go i64` — same-line type */
                        int bl = s->t[s->i - 1].line;
                        if (s->i < s->n && s->t[s->i].kind == 0 &&
                            s->t[s->i].line == bl) {
                            s->i++;
                            while (at(s, ".") || at(s, "/")) {
                                s->i++;
                                if (is_ident_tk(s)) s->i++;
                            }
                            if (at(s, "[")) {           /* type params */
                                int depth = 0;
                                do {
                                    if (at(s, "[")) depth++;
                                    if (at(s, "]")) depth--;
                                    s->i++;
                                } while (depth > 0 && !at_kind(s, 5));
                            }
                        }
                    }
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
                /* koruc refuses a one-variant tag union outright —
                   bare return or >=2 branches are the legal shapes */
                if (it->nbranches == 1) {
                    fail_at(s, err, "one-variant union — spell a bare "
                                    "return or add a second branch");
                    return 0;
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

