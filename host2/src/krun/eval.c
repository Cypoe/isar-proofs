/* host2 krun — eval leg.  Contract in krun.h. */
#include "krun.h"

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
    if (strcmp(name, "chars") == 0 && nargs == 1) {
        Val **xs; int i, n;
        va = eval_ke(env, nenv, args[0]);
        if (!is_str(va)) return 0;
        n = (int)strlen(va->s);
        xs = xmalloc((n ? n : 1) * sizeof *xs);
        for (i = 0; i < n; i++) xs[i] = v_int((unsigned char)va->s[i]);
        return v_arr(xs, n);
    }
    if (strcmp(name, "charsToString") == 0 && nargs == 1) {
        char *p; int i;
        va = eval_ke(env, nenv, args[0]);
        if (!is_arr(va)) return 0;
        p = xmalloc(va->nx + 1);
        for (i = 0; i < va->nx; i++) {
            if (!is_int(va->xs[i]) || va->xs[i]->i < 0 ||
                va->xs[i]->i > 255) return 0;
            p[i] = (char)va->xs[i]->i;
        }
        p[va->nx] = 0;
        return v_str(p);
    }
    if (strcmp(name, "charToString") == 0 && nargs == 1) {
        char *p;
        va = eval_ke(env, nenv, args[0]);
        if (!is_int(va) || va->i < 0 || va->i > 127) return 0;
        p = xmalloc(2);
        p[0] = (char)va->i; p[1] = 0;
        return v_str(p);
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
#ifdef KDBG
    fprintf(stderr, "K tag=%d name=%s head=%s branch=%s arm=%s tgt=%s\n",
            c.tag, c.name ? c.name : "-",
            c.fl && c.fl->hname ? c.fl->hname : "-",
            c.branch ? c.branch : "-",
            c.arm && c.arm->branch ? c.arm->branch : "-",
            c.arm && c.arm->ntarget ? c.arm->ntarget : "-");
#endif

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
int eval_prog(Decl *g, int ng, Leaf *o, int no, int64_t fuel,
                     char *entry, NV *args, int nargs, Result *out) {
    Call c = {0};
    Outc oc;
    c.tag = 0; c.name = entry; c.args = args; c.nargs = nargs;
    oc = run_k(g, ng, o, no, fuel, c);
    if (oc.t != 1) return 0;
    *out = oc.r;
    return 1;
}

