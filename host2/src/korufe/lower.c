/* host2 korufe — lower leg.  Contract in korufe.h. */
#include "korufe.h"

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
    case 14:
        sx_lit(e->a, b, err); break;   /* grouped is surface trivia */
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
    case 14:
        sx_expr(e->a, b, err); break;  /* grouped is surface trivia */
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
    case 7:
        if (!is_builtin(e->s)) {
            *err = xasprintf("unknown builtin '@", e->s);
            *err = xasprintf(*err, "'");
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
    case 8:
        *err = xasprintf("call '", e->s);
        *err = xasprintf(*err, "(...)' inside expression — calls are "
                       "not expressions (KORU104); builtins spell "
                       "@name(...), callables invoke through flow "
                       "nodes");
        return;
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
    else bput(b, " (tag _chain)");   /* koru `|>` chain — decorative
        name so a bare result dispatches it (unnamed cont arms refuse);
        over a tagged producer `_chain` never matches → the wire
        refuses, a named gap vs koru's unconditional chains */
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
    {
        char *rb = jstr(inv, "return_binding");
        if (rb && *rb) out->retbind = rb;
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

/* ---- declared-contract checks (koruc PARSE006 / KORU021 parity)
   The `tor` decl is the contract — but ONLY when one exists: impls
   and invocations without tors are legal koru (implicit events,
   unchecked).  A declared tor constrains invoke arg names ⊆ params
   (PARSE006) and arm branch names ⊆ declared branches — including
   "available: (none)" when the decl is bare (KORU021).  `=>` targets
   ⊆ the enclosing impl's branches; `@label` must name the flow's own
   `#label`.  Named arms on a branchless/undeclared producer keep the
   walker's decorative-names convention — admitted, arbitrated by the
   evaluator.  ----*/

typedef struct {
    char *n; int has_impl; int declared;
    char **params; int nparams;
    char **branches; int nbranches;
} DeclSeen;

static DeclSeen *decl_find(DeclSeen *ds, int n, const char *name) {
    int i;
    for (i = 0; i < n; i++) if (!strcmp(ds[i].n, name)) return &ds[i];
    return 0;
}
static int name_in(char **xs, int n, const char *s) {
    int i;
    for (i = 0; i < n; i++) if (xs[i] && !strcmp(xs[i], s)) return 1;
    return 0;
}
static char *errcat2(char *a, const char *b) { return xasprintf(a, b); }

/* koru arg naming: an unlabelled `x` puns to the param of the same
   name — the pun name is the expr's trailing ident (var or field
   tail: `f(p.x)` puns to `x`).  A non-pun positional binds the
   callee's param at its index (needs a decl); unnameable positional
   args refuse — the wire carries named args only. */
char *pun_name(KExpr *e) {
    if (e->tag == 1 || e->tag == 5) return e->s;
    return 0;
}

static int resolve_args(DeclSeen *d, Inv *v, char **err) {
    int i;
    for (i = 0; i < v->nargs; i++) {
        if (v->args[i].n) continue;
        char *pun = pun_name(v->args[i].e);
        if (pun && (!d || !d->declared ||
                    name_in(d->params, d->nparams, pun))) {
            v->args[i].n = pun;
        } else if (d && d->declared && i < d->nparams) {
            v->args[i].n = d->params[i];
        } else {
            *err = errcat2(xstrdup("cannot name positional arg on '"),
                           v->name);
            *err = errcat2(*err, "' — decl-less or out of range "
                                 "(spell `name: expr`)");
            return 0;
        }
    }
    return 1;
}

static int check_inv_args(DeclSeen *ds, int n, Inv *v, char **err) {
    DeclSeen *d;
    int i;
    if (!v->name) { *err = xstrdup("invoke without target"); return 0; }
    if (v->qual && v->qual[0] == '@') return 1;      /* jumps: flow check */
    d = decl_find(ds, n, v->name);
    if (!resolve_args(d, v, err)) return 0;
    if (!d || !d->declared) return 1;   /* implicit event — unchecked */
    for (i = 0; i < v->nargs; i++) {
        const char *an = v->args[i].n;
        if (!an) continue;
        if (!name_in(d->params, d->nparams, an)) {
            *err = errcat2(xstrdup("unknown parameter '"), an);
            *err = errcat2(*err, "' — '");
            *err = errcat2(*err, v->name);
            *err = errcat2(*err, "' has no parameter named '");
            *err = errcat2(*err, an);
            *err = errcat2(*err, "'");
            return 0;
        }
    }
    return 1;
}

static int check_arms(DeclSeen *ds, int n, ArmD **arms, int narms,
                      DeclSeen *producer, DeclSeen *own,
                      const char *pre, DeclSeen *head, char **err) {
    int i, j;
    for (i = 0; i < narms; i++) {
        ArmD *a = arms[i];
        /* KORU021 parity: arm branch names are checked against the
           producer's declared union — but only when the producer
           declares branches at all.  A declared-but-branchless tor
           (`-> program`) returns a bare-typed value; arm names over
           it are decorative dispatch labels koruc accepts (and
           FlowKernel ignores under bare dispatch). */
        if (producer && producer->declared && producer->nbranches > 0 &&
            !a->catchall && a->branch[0] &&
            !name_in(producer->branches, producer->nbranches, a->branch)) {
            *err = errcat2(xstrdup("tor '"), producer->n);
            *err = errcat2(*err, "' has no branch '");
            *err = errcat2(*err, a->branch);
            *err = errcat2(*err, "' (available: ");
            *err = errcat2(*err, producer->nbranches ? "" : "none");
            for (j = 0; j < producer->nbranches; j++) {
                if (j) *err = errcat2(*err, ", ");
                *err = errcat2(*err, producer->branches[j]);
            }
            *err = errcat2(*err, ")");
            return 0;
        }
        if (a->nconts && a->kind != 3) {
            *err = xstrdup("continuations after ->/=>/terminal arms "
                           "have no result to dispatch — invoke only");
            return 0;
        }
        if (a->kind == 2) {               /* => ctor on own decl */
            if (!own || !own->declared ||
                !name_in(own->branches, own->nbranches, a->target)) {
                *err = errcat2(xstrdup("=> '"), a->target);
                *err = errcat2(*err, "' but '");
                *err = errcat2(*err, own ? own->n : "?");
                *err = errcat2(*err, "' declares no such branch");
                return 0;
            }
        } else if (a->kind == 3) {        /* |> invoke */
            if (!check_inv_args(ds, n, a->inv, err)) return 0;
            if (a->nconts &&
                !check_arms(ds, n, a->conts, a->nconts,
                            decl_find(ds, n, a->target), own, pre,
                            head, err))
                return 0;
        } else if (a->kind == 4) {        /* |> @label jump */
            if (!pre || strcmp(a->target, pre)) {
                *err = errcat2(xstrdup("jump '@"), a->target);
                *err = errcat2(*err, "' does not name this flow's "
                                     "#label");
                return 0;
            }
            if (!resolve_args(head, a->inv, err)) return 0;
            if (head && head->declared) {
                for (j = 0; j < a->inv->nargs; j++) {
                    const char *an = a->inv->args[j].n;
                    if (an &&
                        !name_in(head->params, head->nparams, an)) {
                        *err = errcat2(xstrdup("jump arg '"), an);
                        *err = errcat2(*err, "' — head '");
                        *err = errcat2(*err, head->n);
                        *err = errcat2(*err, "' has no parameter '");
                        *err = errcat2(*err, an);
                        *err = errcat2(*err, "'");
                        return 0;
                    }
                }
            }
        }
    }
    return 1;
}

/* emit the claim for a program ast + case row */
/* wire-value printer for case-row JSON values — mirrors krun's
   print_val exactly: (int N) (float n d) (bool b) (str "s")
   (arr v*) (cell (n v)*).  Bare expects, tag payloads, oracle
   results and entry args all carry the same grammar. */
static int jval_sx(Jv *v, Buf *b, char **err) {
    int i;
    if (jget(v, "int"))
        bputf(b, "(int %lld)", (long long)jget(v, "int")->num);
    else if (jget(v, "float")) {
        Jv *fl = jget(v, "float");
        bputf(b, "(float %lld %lld)",
              (long long)fl->xs[0]->num, (long long)fl->xs[1]->num);
    }
    else if (jget(v, "bool"))
        bputf(b, "(bool %s)", jget(v, "bool")->b ? "true" : "false");
    else if (jget(v, "str"))
        bputf(b, "(str \"%s\")", jget(v, "str")->s);
    else if (jget(v, "arr")) {
        Jv *xs = jget(v, "arr");
        bput(b, "(arr");
        for (i = 0; i < xs->nxs; i++) {
            bput(b, " ");
            if (!jval_sx(xs->xs[i], b, err)) return 0;
        }
        bput(b, ")");
    }
    else if (jget(v, "cell")) {
        Jv *fs = jget(v, "cell");
        bput(b, "(cell");
        for (i = 0; i < fs->nfs; i++) {
            bputf(b, " (%s ", fs->fs[i].k);
            if (!jval_sx(fs->fs[i].v, b, err)) return 0;
            bput(b, ")");
        }
        bput(b, ")");
    }
    else { *err = xstrdup("wire val shape"); return 0; }
    return 1;
}

int lower(Jv *ast, Jv *cspec, Buf *out, char **err) {
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
        /* The `tor`-line contract table — collected in a first pass
           so impls may precede the decls they invoke. */
        DeclSeen *seen = xmalloc(items->nxs * sizeof(DeclSeen));
        int nseen = 0;
        memset(seen, 0, items->nxs * sizeof(DeclSeen));
        for (i = 0; i < items->nxs; i++) {
            Jv *it = items->xs[i];
            Jv *d = jget(it, "event_decl");
            Jv *flds, *brs;
            char *nm;
            int j, k;
            if (!d) continue;
            nm = jseg0(jget(d, "path"));
            if (!nm) { *err = xstrdup("event_decl: no name"); return 0; }
            for (j = 0; j < nseen; j++)
                if (!strcmp(seen[j].n, nm)) {
                    *err = xasprintf("duplicate tor '", nm);
                    *err = xasprintf(*err, "'");
                    return 0;
                }
            seen[nseen].n = nm;
            flds = jarr(jget(d, "input"), "fields");
            if (flds) {
                seen[nseen].nparams = flds->nxs;
                seen[nseen].params = flds->nxs
                    ? xmalloc(flds->nxs * sizeof(char *)) : 0;
                for (k = 0; k < flds->nxs; k++)
                    seen[nseen].params[k] = jstr(flds->xs[k], "name");
            }
            brs = jarr(d, "branches");
            if (brs) {
                seen[nseen].nbranches = brs->nxs;
                seen[nseen].branches = brs->nxs
                    ? xmalloc(brs->nxs * sizeof(char *)) : 0;
                for (k = 0; k < brs->nxs; k++)
                    seen[nseen].branches[k] = jstr(brs->xs[k], "name");
            }
            seen[nseen].declared = 1;
            nseen++;
        }
        for (i = 0; i < items->nxs; i++) {
            Jv *it = items->xs[i];
            if (jget(it, "immediate_impl")) {
                Jv *im = jget(it, "immediate_impl");
                char *nm = jseg0(jget(im, "event_path"));
                Jv *val = jget(im, "value");
                char *pv = jstr(val, "plain_value");
                char *bn = jstr(val, "branch_name");
                KExpr *e;
                int j, dup = 0;
                if (!nm) { *err = xstrdup("immediate_impl: no name"); return 0; }
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
                    /* declared-contract checks — koruc's static
                       walls, checked at the lower boundary where the
                       decl table is complete */
                    DeclSeen *ownd = decl_find(seen, nseen,
                                               impl->xs[0]->s);
                    DeclSeen *headd;
                    if (!check_inv_args(seen, nseen, fd.head, err))
                        return 0;
                    headd = decl_find(seen, nseen, fd.head->name);
                    if (!check_arms(seen, nseen, fd.arms, fd.narms,
                                    headd, ownd, fd.pre, headd, err))
                        return 0;
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

        /* entry args ⊆ the entry tor's declared params — but only
           when the decl exists: an absent entry is the wire's
           refusal row (claim lowers, eval refuses). */
        {
            DeclSeen *ed = decl_find(seen, nseen, entry);
            Jv *ea = jget(cspec, "args");
            if (ed && ed->declared && ea && ea->k == 5) {
                int k;
                for (k = 0; k < ea->nfs; k++) {
                    if (!name_in(ed->params, ed->nparams, ea->fs[k].k)) {
                        *err = errcat2(xstrdup("entry arg '"),
                                       ea->fs[k].k);
                        *err = errcat2(*err, "' — '");
                        *err = errcat2(*err, entry);
                        *err = errcat2(*err, "' has no parameter named '");
                        *err = errcat2(*err, ea->fs[k].k);
                        *err = errcat2(*err, "'");
                        return 0;
                    }
                }
            }
        }

        /* oracle leaves: name declared, args ⊆ params, tag ∈
           branches — the surface contract applies to leaf data */
        {
            Jv *ol = jarr(cspec, "oracle");
            int k;
            if (ol) {
                for (k = 0; k < ol->nxs; k++) {
                    Jv *leaf = ol->xs[k];
                    char *ln = jstr(leaf, "name");
                    Jv *largs = jget(leaf, "args");
                    Jv *lres = jget(leaf, "result");
                    DeclSeen *ld = decl_find(seen, nseen,
                                             ln ? ln : "");
                    char *lt;
                    int m;
                    if (!ld) {
                        *err = errcat2(xstrdup("oracle leaf '"),
                                       ln ? ln : "?");
                        *err = errcat2(*err, "' names no callable");
                        return 0;
                    }
                    if (ld->has_impl) {
                        *err = errcat2(xstrdup("oracle leaf '"), ln);
                        *err = errcat2(*err, "' names an impl — leaves "
                                       "cover thunks only");
                        return 0;
                    }
                    if (largs && largs->k == 5 && ld->declared) {
                        for (m = 0; m < largs->nfs; m++) {
                            if (!name_in(ld->params, ld->nparams,
                                         largs->fs[m].k)) {
                                *err = errcat2(
                                    xstrdup("oracle leaf arg '"),
                                    largs->fs[m].k);
                                *err = errcat2(*err, "' — '");
                                *err = errcat2(*err, ln);
                                *err = errcat2(*err,
                                    "' has no parameter '");
                                *err = errcat2(*err, largs->fs[m].k);
                                *err = errcat2(*err, "'");
                                return 0;
                            }
                        }
                    }
                    lt = lres ? jstr(lres, "tag") : 0;
                    if (ld->declared) {
                        if (lt) {
                            if (!name_in(ld->branches, ld->nbranches,
                                         lt)) {
                                *err = errcat2(xstrdup(
                                               "oracle leaf tag '"), lt);
                                *err = errcat2(*err, "' but '");
                                *err = errcat2(*err, ln);
                                *err = errcat2(*err,
                                           "' declares no such branch");
                                return 0;
                            }
                        } else if (ld->nbranches > 0) {
                            *err = errcat2(xstrdup("oracle leaf for '"),
                                           ln);
                            *err = errcat2(*err, "' is bare/void but the "
                                           "tor declares branches");
                            return 0;
                        }
                    }
                }
            }
        }
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
                        if (!jval_sx(args->fs[j].v, &oracle, err)) return 0;
                        bput(&oracle, ") ");
                    }
                }
                bput(&oracle, ") ");
                /* result: {"bare":v} {"tag":"b","payload":v} {"void":true} */
                if (jget(res, "void")) bput(&oracle, "(void)");
                else if (jget(res, "bare")) {
                    bput(&oracle, "(bare ");
                    if (!jval_sx(jget(res, "bare"), &oracle, err)) return 0;
                    bput(&oracle, ")");
                } else if (jget(res, "tag")) {
                    Jv *v = jget(res, "payload");
                    bputf(&oracle, "(tag %s", jstr(res, "tag"));
                    if (v) {
                        bput(&oracle, " ");
                        if (!jval_sx(v, &oracle, err)) return 0;
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
                bputf(&ea, " (%s ", args->fs[i].k);
                if (!jval_sx(args->fs[i].v, &ea, err)) return 0;
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
            bput(out, "(bare ");
            if (!jval_sx(jget(expect, "bare"), out, err)) return 0;
            bput(out, ")");
        } else if (jget(expect, "tag")) {
            Jv *v = jget(expect, "payload");
            bputf(out, "(tag %s", jstr(expect, "tag"));
            if (v) {
                bput(out, " ");
                if (!jval_sx(v, out, err)) return 0;
            }
            bput(out, ")");
        } else { *err = xstrdup("expect row"); return 0; }
        bput(out, ") ");
        bput(out, graph.p); bput(out, " ");
        bput(out, oracle.p); bput(out, ")");
    }
    return 1;
}

