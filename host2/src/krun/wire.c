/* host2 krun — wire leg.  Contract in krun.h. */
#include "krun.h"

/* ================= values ================= */

static Val *v_new(int tag) { Val *v = xmalloc(sizeof(Val)); memset(v, 0, sizeof *v); v->tag = tag; return v; }
Val *v_int(int64_t i) { Val *v = v_new(0); v->i = i; return v; }
Val *v_float(int64_t n, int64_t d) { Val *v = v_new(1); v->i = n; v->d = d; return v; }
Val *v_bool(int b) { Val *v = v_new(2); v->b = b; return v; }
Val *v_str(char *s) { Val *v = v_new(3); v->s = s; return v; }
Val *v_arr(Val **xs, int n) { Val *v = v_new(4); v->xs = xs; v->nx = n; return v; }
Val *v_cell(char **ns, Val **vs, int n) { Val *v = v_new(5); v->ns = ns; v->vs = vs; v->nf = n; return v; }

int is_int(Val *v) { return v && v->tag == 0; }
int is_bool(Val *v) { return v && v->tag == 2; }
int is_str(Val *v) { return v && v->tag == 3; }
int is_arr(Val *v) { return v && v->tag == 4; }
int is_cell(Val *v) { return v && v->tag == 5; }
int is_float(Val *v) { return v && v->tag == 1; }

/* structural equality — kvalBEq twin: floats compare num/den
   pairwise (NOT rational equality), cells order-sensitively */
int val_eq(Val *a, Val *b) {
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
int sx_claim(Sx *x, Claim *out) {
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

