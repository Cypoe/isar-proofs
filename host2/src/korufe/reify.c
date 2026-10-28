/* host2 korufe — reify leg.  Contract in korufe.h.
   The flat row wire (kast's `out` — `(kind off off …)` byte spans
   into the source) reified back into the same Item tree the C
   parser produces, emitted through write_ast_json so
     reify(kast(FILE.k), FILE.k)  ≡  korufe FILE.k
   is a document-level race, not just a claim-level one.  Nesting
   mirrors korufe's own parse exactly: `|` arms are flat siblings
   under the flow, `|>` links nest as anon conts (branch ""),
   `: bind` rides forward into the next link's binding. */
#include "korufe.h"

/* ---- row text → Row records ------------------------------------
   grammar: `(` atom [atom|int]… `)` — `(step expr 236 237)` carries
   a sub-atom; `(bad …)` is the wire's refusal row. */

typedef struct { char k[8]; char sub[8]; long v[4]; int nv; } Row;

static const char *rsrc;
static long rsrcn;

static Row *scan_rows(const char *t, int *nout, char **err) {
    int cap = 128, n = 0;
    Row *rs = xmalloc((size_t)cap * sizeof(Row));
    const char *p = t;
    while (*p) {
        Row r;
        int k = 0;
        memset(&r, 0, sizeof r);
        if (*p == ' ' || *p == '\n' || *p == '\t' || *p == '\r') {
            p++;
            continue;
        }
        if (*p != '(') goto bad;
        p++;
        while (*p && *p != ' ' && *p != ')') {
            if (k < 7) r.k[k++] = *p;
            p++;
        }
        r.k[k] = 0;
        for (;;) {
            char *e;
            if (*p == ')') { p++; break; }
            if (*p != ' ') goto bad;
            p++;
            if ((*p >= '0' && *p <= '9') || *p == '-') {
                if (r.nv >= 4) goto bad;
                r.v[r.nv++] = strtol(p, &e, 10);
                p = e;
            } else {
                k = 0;
                while (*p && *p != ' ' && *p != ')') {
                    if (k < 7) r.sub[k++] = *p;
                    p++;
                }
                r.sub[k] = 0;
            }
        }
        if (n == cap) {
            cap *= 2;
            {
                Row *nr = xmalloc((size_t)cap * sizeof(Row));
                memcpy(nr, rs, (size_t)n * sizeof(Row));
                rs = nr;
            }
        }
        rs[n++] = r;
    }
    *nout = n;
    return rs;
bad:
    *err = xstrdup("row wire is not `(kind off …)` text");
    return 0;
}

/* ---- source slicing ---- */

static char *span(long lo, long hi, char **err) {
    if (lo < 0 || hi > rsrcn || lo > hi) {
        *err = xstrdup("row span out of bounds");
        return 0;
    }
    return xstrndup(rsrc + lo, (size_t)(hi - lo));
}

static int line_of(long off) {
    int l = 1;
    long i;
    for (i = 0; i < off && i < rsrcn; i++)
        if (rsrc[i] == '\n') l++;
    return l;
}

/* to-EOL spans can carry a same-line `| arm`/`=>`/`->` tail — cut
   the expr at the first top-level delimiter (`|` that isn't `||`,
   `=>`, `->`) outside parens/strings */
static long expr_tail(long lo, long hi) {
    long i;
    int depth = 0, ins = 0;
    for (i = lo; i < hi; i++) {
        char c = rsrc[i];
        if (ins) { if (c == '"') ins = 0; continue; }
        if (c == '"') { ins = 1; continue; }
        if (c == '(' || c == '[' || c == '{') depth++;
        else if (c == ')' || c == ']' || c == '}') depth--;
        else if (depth == 0 && c == '|') {
            if (i + 1 < hi && rsrc[i + 1] == '|') { i++; continue; }
            if (i > lo && rsrc[i - 1] == '|') continue;
            return i;
        } else if (depth == 0 && i + 1 < hi &&
                   ((c == '=' || c == '-') && rsrc[i + 1] == '>')) {
            return i;
        }
    }
    return hi;
}

/* first-token slice (import paths / return types) — stops at
   whitespace or a `//` comment tail inside the to-EOL span */
static char *span_tok(long lo, long hi, char **err) {
    long i;
    while (hi > lo &&
           (rsrc[hi - 1] == ' ' || rsrc[hi - 1] == '\t' ||
            rsrc[hi - 1] == '\r' || rsrc[hi - 1] == '\n'))
        hi--;
    for (i = lo; i < hi; i++) {
        if (rsrc[i] == '/' && i + 1 < hi && rsrc[i + 1] == '/') {
            hi = i;
            break;
        }
        if (rsrc[i] == ' ' || rsrc[i] == '\t' ||
            rsrc[i] == '\r' || rsrc[i] == '\n') {
            hi = i;
            break;
        }
    }
    return span(lo, hi, err);
}

/* type slices (`[]const i64` carries a space) — trim, strip `//` */
static char *span_type(long lo, long hi, char **err) {
    long i;
    while (hi > lo &&
           (rsrc[hi - 1] == ' ' || rsrc[hi - 1] == '\t' ||
            rsrc[hi - 1] == '\r' || rsrc[hi - 1] == '\n'))
        hi--;
    for (i = lo; i + 1 < hi; i++)
        if (rsrc[i] == '/' && rsrc[i + 1] == '/') { hi = i; break; }
    while (hi > lo && (rsrc[hi - 1] == ' ' || rsrc[hi - 1] == '\t'))
        hi--;
    return span(lo, hi, err);
}

/* expr_from_src re-parses a *slice* — the KExpr spans it produces
   index into the slice, not the source.  Shift them back to
   absolute so jese/write_ast_json emit the right bytes. */
static void span_shift(KExpr *e, long base) {
    int i;
    e->lo += base;
    e->hi += base;
    if (e->a) span_shift(e->a, base);
    if (e->bb) span_shift(e->bb, base);
    if (e->c) span_shift(e->c, base);
    for (i = 0; i < e->nargs; i++) span_shift(e->args[i].e, base);
    for (i = 0; i < e->nxs; i++) span_shift(e->xs[i], base);
    for (i = 0; i < e->nfs; i++) span_shift(e->fs[i].e, base);
}

static KExpr *span_expr(long lo, long hi, char **err) {
    long alo = lo;
    KExpr *e;
    char *t;
    hi = expr_tail(lo, hi);
    while (alo < hi &&
           (rsrc[alo] == ' ' || rsrc[alo] == '\t' ||
            rsrc[alo] == '\r' || rsrc[alo] == '\n'))
        alo++;
    while (hi > alo &&
           (rsrc[hi - 1] == ' ' || rsrc[hi - 1] == '\t' ||
            rsrc[hi - 1] == '\r' || rsrc[hi - 1] == '\n'))
        hi--;
    t = span(alo, hi, err);
    if (!t || !*t) { *err = xstrdup("empty expression span"); return 0; }
    e = expr_from_src(t, err);
    if (e) span_shift(e, alo);
    return e;
}

static int pub_before(long j) {
    long ls = j, i;
    while (ls > 0 && rsrc[ls - 1] != '\n') ls--;
    for (i = ls; i + 4 <= j; i++)
        if (!memcmp(rsrc + i, "pub", 3) &&
            (rsrc[i + 3] == ' ' || rsrc[i + 3] == '\t') &&
            (i == ls || rsrc[i - 1] == ' ' || rsrc[i - 1] == '\t'))
            return 1;
    return 0;
}

/* `(step …)` arriving where an invocation chain can continue:
   cur==NULL → head-level anon arm (flow sibling);
   cur has no node → the arm's own node;
   cur is an invoke/jump chain → anon link under the tail. */
static ArmD *anon_link(Inv *v, int jump, char *bind, long pos) {
    ArmD *a = xmalloc(sizeof(ArmD));
    memset(a, 0, sizeof *a);
    a->kind = jump ? 4 : 3;
    a->branch = "";
    a->bind = bind;
    a->inv = v;
    a->target = v->name;
    a->line = line_of(pos);
    return a;
}

/* ---- the walk ---- */

Item *reify_rows(const char *rowtext, const char *source, char **err) {
    int nr = 0, ri;
    Row *rs;
    Item *head = 0, **tail = &head;
    Item *cur_ev = 0, *cur_it = 0;
    FlowD *cf = 0;
    ArmD *cur = 0, *chain_tail = 0;
    Inv *last_inv = 0;
    char *pend = 0;            /* `: bind` staged for the next link */
    char *pre = 0;             /* `(lbl)` staged for the next flow */
    long flw_p = -1;           /* current flow item's byte offset */
    int fldcap = 0, brcap = 0, armcap = 0, argcap = 0;

    rsrc = source;
    rsrcn = (long)strlen(source);
    rs = scan_rows(rowtext, &nr, err);
    if (!rs) return 0;

#define FAIL(msg) do { *err = xstrdup(msg); return 0; } while (0)

    for (ri = 0; ri < nr; ri++) {
        Row *r = &rs[ri];
        if (!strcmp(r->k, "bad")) {
            FAIL("row wire carries (bad …) — the koru parser refused");
        } else if (!strcmp(r->k, "imp")) {
            Item *it = xmalloc(sizeof(Item));
            memset(it, 0, sizeof *it);
            it->kind = 0;
            it->import_path = span_tok(r->v[0], r->v[1], err);
            it->name = it->import_path;
            if (!it->import_path) return 0;
            it->line = line_of(r->v[0]);
            *tail = it; tail = &it->next;
            cur_ev = 0; cur_it = 0; cf = 0; cur = 0; last_inv = 0;
        } else if (!strcmp(r->k, "ev")) {
            Item *it = xmalloc(sizeof(Item));
            memset(it, 0, sizeof *it);
            it->kind = 1;
            it->name = span(r->v[0], r->v[1], err);
            if (!it->name) return 0;
            it->is_pub = pub_before(r->v[0]);
            it->line = line_of(r->v[0]);
            fldcap = brcap = 0;
            *tail = it; tail = &it->next;
            cur_ev = it; cur_it = 0; cf = 0; cur = 0; last_inv = 0;
        } else if (!strcmp(r->k, "fld")) {
            if (!cur_ev) FAIL("(fld) outside event_decl");
            if (cur_ev->nfields == fldcap) {
                fldcap = fldcap ? fldcap * 2 : 4;
                {
                    void *nf = xmalloc((size_t)fldcap *
                                       sizeof(*cur_ev->fields));
                    memcpy(nf, cur_ev->fields,
                           (size_t)cur_ev->nfields *
                           sizeof(*cur_ev->fields));
                    cur_ev->fields = nf;
                }
            }
            cur_ev->fields[cur_ev->nfields].n =
                span(r->v[0], r->v[1], err);
            cur_ev->fields[cur_ev->nfields].t =
                span_type(r->v[2], r->v[3], err);
            if (!cur_ev->fields[cur_ev->nfields].n ||
                !cur_ev->fields[cur_ev->nfields].t) return 0;
            cur_ev->nfields++;
        } else if (!strcmp(r->k, "ret")) {
            if (!cur_ev) FAIL("(ret) outside event_decl");
            cur_ev->ret_type = span_tok(r->v[0], r->v[1], err);
            if (!cur_ev->ret_type) return 0;
        } else if (!strcmp(r->k, "brd")) {
            if (!cur_ev) FAIL("(brd) outside event_decl");
            if (cur_ev->nbranches == brcap) {
                brcap = brcap ? brcap * 2 : 4;
                {
                    char **nb = xmalloc((size_t)brcap * sizeof(char *));
                    char **nt = xmalloc((size_t)brcap * sizeof(char *));
                    memcpy(nb, cur_ev->branches,
                           (size_t)cur_ev->nbranches * sizeof(char *));
                    memcpy(nt, cur_ev->btypes,
                           (size_t)cur_ev->nbranches * sizeof(char *));
                    cur_ev->branches = nb;
                    cur_ev->btypes = nt;
                }
            }
            cur_ev->branches[cur_ev->nbranches] =
                span(r->v[0], r->v[1], err);
            cur_ev->btypes[cur_ev->nbranches] =
                r->v[2] < r->v[3] ? span_type(r->v[2], r->v[3], err) : 0;
            if (!cur_ev->branches[cur_ev->nbranches]) return 0;
            cur_ev->nbranches++;
        } else if (!strcmp(r->k, "impl")) {
            Item *it = xmalloc(sizeof(Item));
            memset(it, 0, sizeof *it);
            it->kind = 2;
            it->name = span(r->v[0], r->v[1], err);
            it->bare = span_expr(r->v[2], r->v[3], err);
            if (!it->name || !it->bare) return 0;
            it->line = line_of(r->v[0]);
            *tail = it; tail = &it->next;
            cur_ev = 0; cur_it = 0; cf = 0; cur = 0; last_inv = 0;
        } else if (!strcmp(r->k, "lbl")) {
            if (pre) FAIL("two (lbl) rows with no flow between");
            pre = span(r->v[0], r->v[1], err);
            if (!pre) return 0;
        } else if (!strcmp(r->k, "flw")) {
            Item *it;
            if (pend) FAIL("trailing 'inv: bind' has no continuation");
            it = xmalloc(sizeof(Item));
            memset(it, 0, sizeof *it);
            it->kind = -1;         /* settled by the (call) row */
            it->name = span(r->v[0], r->v[1], err);
            if (!it->name) return 0;
            it->line = line_of(r->v[0]);
            it->flow = xmalloc(sizeof(FlowD));
            memset(it->flow, 0, sizeof *it->flow);
            it->flow->pre = pre;
            pre = 0;
            *tail = it; tail = &it->next;
            armcap = 0;
            flw_p = r->v[0];
            cur_ev = 0; cur_it = it; cf = it->flow;
            cur = 0; last_inv = 0;
        } else if (!strcmp(r->k, "call")) {
            Inv *v;
            if (!cf || !cur_it) FAIL("(call) outside a flow");
            v = xmalloc(sizeof(Inv));
            memset(v, 0, sizeof *v);
            v->name = span(r->v[0], r->v[1], err);
            if (!v->name) return 0;
            /* kind 4 `name(args)` — call span == flw name span;
               kind 3 `name = call(…)` — impl_of is the flow's own
               declared tor */
            cur_it->kind = r->v[0] == flw_p ? 4 : 3;
            cf->head = v;
            last_inv = v;
            argcap = 0;
        } else if (!strcmp(r->k, "arg")) {
            NArg *a;
            if (!last_inv) FAIL("(arg) with no invocation");
            if (last_inv->nargs == argcap) {
                argcap = argcap ? argcap * 2 : 4;
                {
                    NArg *na = xmalloc((size_t)argcap * sizeof(NArg));
                    memcpy(na, last_inv->args,
                           (size_t)last_inv->nargs * sizeof(NArg));
                    last_inv->args = na;
                }
            }
            a = &last_inv->args[last_inv->nargs];
            a->n = r->v[0] ? span(r->v[0], r->v[1], err) : 0;
            a->e = span_expr(r->v[2], r->v[3], err);
            if ((r->v[0] && !a->n) || !a->e) return 0;
            last_inv->nargs++;
        } else if (!strcmp(r->k, "rbind")) {
            if (!last_inv) FAIL("(rbind) with no invocation");
            last_inv->retbind = span(r->v[0], r->v[1], err);
            pend = last_inv->retbind;
            if (!pend) return 0;
        } else if (!strcmp(r->k, "cont")) {
            ArmD *a;
            int k;
            if (!cf) FAIL("(cont) outside a flow");
            if (pend) FAIL("'inv: bind' before a '|' dispatch arm is "
                          "out of subset (use '|>' to continue)");
            for (k = 0; k < cf->narms; k++)
                if (!cf->arms[k]->branch || !*cf->arms[k]->branch)
                    FAIL("'|' dispatch under a '|>' chain needs "
                         "indentation scoping — out of subset");
            a = xmalloc(sizeof(ArmD));
            memset(a, 0, sizeof *a);
            a->kind = -1;
            a->branch = span(r->v[0], r->v[1], err);
            if (!a->branch) return 0;
            {
                long q = r->v[0];
                while (q > 0 &&
                       (rsrc[q - 1] == ' ' || rsrc[q - 1] == '\t'))
                    q--;
                a->line = line_of(q > 0 ? q - 1 : q);
            }
            if (cf->narms == armcap) {
                armcap = armcap ? armcap * 2 : 4;
                {
                    ArmD **na =
                        xmalloc((size_t)armcap * sizeof(ArmD *));
                    memcpy(na, cf->arms,
                           (size_t)cf->narms * sizeof(ArmD *));
                    cf->arms = na;
                }
            }
            cf->arms[cf->narms++] = a;
            cur = a; chain_tail = a;
            last_inv = 0;
        } else if (!strcmp(r->k, "bind")) {
            if (!cur) FAIL("(bind) outside an arm");
            cur->bind = span(r->v[0], r->v[1], err);
            if (!cur->bind) return 0;
        } else if (!strcmp(r->k, "cond")) {
            if (!cur) FAIL("(cond) outside an arm");
            cur->cond = span_expr(r->v[0], r->v[1], err);
            if (!cur->cond) return 0;
        } else if (!strcmp(r->k, "step")) {
            if (!strcmp(r->sub, "expr")) {
                if (!cur || cur->kind != -1)
                    FAIL("(step expr) with no open arm");
                cur->kind = 1;
                cur->produce = span_expr(r->v[0], r->v[1], err);
                if (!cur->produce) return 0;
            } else if (!strcmp(r->sub, "invoke") ||
                       !strcmp(r->sub, "jump")) {
                Inv *v = xmalloc(sizeof(Inv));
                int jump = !strcmp(r->sub, "jump");
                memset(v, 0, sizeof *v);
                if (jump) v->qual = xstrdup("@");
                v->name = span(r->v[0], r->v[1], err);
                if (!v->name) return 0;
                argcap = 0;
                last_inv = v;
                if (!cur) {
                    /* `head: b |> step` — head chains are flow-level
                       anon arms (korufe pushes them as siblings) */
                    ArmD *a = anon_link(v, jump, pend, r->v[0]);
                    pend = 0;
                    if (cf->narms == armcap) {
                        armcap = armcap ? armcap * 2 : 4;
                        {
                            ArmD **na = xmalloc(
                                (size_t)armcap * sizeof(ArmD *));
                            memcpy(na, cf->arms,
                                   (size_t)cf->narms * sizeof(ArmD *));
                            cf->arms = na;
                        }
                    }
                    cf->arms[cf->narms++] = a;
                    cur = a; chain_tail = a;
                } else if (cur->kind == -1) {
                    cur->kind = jump ? 4 : 3;
                    cur->inv = v;
                    cur->target = v->name;
                } else if (cur->kind == 3 || cur->kind == 4) {
                    /* `step : b |> step` — anon link, sole child
                       of the chain tail (korufe's tail->conts[0]) */
                    ArmD *nx = anon_link(v, jump, pend, r->v[0]);
                    pend = 0;
                    chain_tail->conts = xmalloc(sizeof(ArmD *));
                    chain_tail->conts[0] = nx;
                    chain_tail->nconts = 1;
                    chain_tail = nx;
                } else {
                    FAIL("chain link after a produce/ctor/terminal "
                         "step has no spelling");
                }
            } else {
                FAIL("unknown (step …) subkind");
            }
        } else if (!strcmp(r->k, "ctor")) {
            if (!cur || cur->kind != -1)
                FAIL("(ctor) with no open arm");
            cur->kind = 2;
            cur->target = span(r->v[0], r->v[1], err);
            if (!cur->target) return 0;
            if (r->v[2] < expr_tail(r->v[2], r->v[3])) {
                cur->produce = span_expr(r->v[2], r->v[3], err);
                if (!cur->produce) return 0;
            }
        } else {
            FAIL("unknown row kind");
        }
    }
    if (pend) FAIL("trailing 'inv: bind' has no continuation");
    return head;
#undef FAIL
}
