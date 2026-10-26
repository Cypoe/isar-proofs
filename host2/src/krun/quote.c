/* host2 krun — quote leg.  Contract in krun.h. */
#include "krun.h"

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
Val *quote_prog(Prog *p) {
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

