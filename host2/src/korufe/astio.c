/* host2 korufe — astio leg.  Contract in korufe.h. */
#include "korufe.h"

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
    case 7:
        bput(b, "@");   /* builtin_call spells @name(...) */
        /* fallthrough */
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

static void write_inv_json(Inv *v, int jump, FILE *f) {
    int j;
    fputs("{\"event\":[", f);
    if (jump) fprintf(f, "\"@%s\"", v->name); else jesc(f, v->name);
    fputs("],\"args\":[", f);
    for (j = 0; j < v->nargs; j++) {
        Buf ab = {0, 0, 0};
        if (j) fputc(',', f);
        fputs("{\"name\":", f);
        if (v->args[j].n) jesc(f, v->args[j].n); else jesc(f, "");
        fputs(",\"value\":", f);
        expr_src_b(v->args[j].e, &ab);
        jesc(f, ab.p ? ab.p : "");
        fputc('}', f);
    }
    fputs("],\"variant\":null,\"return_binding\":", f);
    if (v->retbind) jesc(f, v->retbind); else fputs("null", f);
    fputc('}', f);
}

static void write_arm_json(ArmD *a, const char *file, int line, FILE *f) {
    Buf cb = {0, 0, 0};
    int i;
    fputs("{\"branch\":", f); jesc(f, a->branch);
    fprintf(f, ",\"kind\":\"terminal\",\"is_catchall\":%s,\"binding\":",
            a->catchall ? "true" : "false");
    if (a->bind) jesc(f, a->bind); else fputs("null", f);
    fputs(",\"binding_type\":\"branch_payload\",\"condition\":", f);
    if (a->cond) { expr_src_b(a->cond, &cb); jesc(f, cb.p ? cb.p : ""); }
    else fputs("null", f);
    fputs(",\"step\":", f);
    if (a->kind == 1) {           /* produce */
        Buf pb = {0, 0, 0};
        expr_src_b(a->produce, &pb);
        fputs("{\"type\":\"produce\",\"plain_value\":", f);
        jesc(f, pb.p ? pb.p : "");
        fputs("}", f);
    } else if (a->kind == 2) {    /* ctor */
        fputs("{\"type\":\"branch_constructor\",\"branch_constructor\":{\"branch_name\":", f);
        jesc(f, a->target);
        fputs(",\"fields\":[],\"plain_value\":", f);
        if (a->produce) { Buf pb = {0,0,0}; expr_src_b(a->produce, &pb); jesc(f, pb.p?pb.p:""); }
        else fputs("null", f);
        fputs(",\"has_expressions\":", f);
        fputs(a->produce ? "true" : "false", f);
        fputs(",\"is_bare_return\":false}}", f);
    } else if (a->kind == 3 || a->kind == 4) { /* invoke / @jump */
        fputs("{\"type\":\"invocation\",\"invocation\":", f);
        write_inv_json(a->inv, a->kind == 4, f);
        fputs("}", f);
    } else {
        fputs("{\"type\":\"terminal\"}", f);
    }
    fputs(",\"continuations\":[", f);
    for (i = 0; i < a->nconts; i++) {
        if (i) fputc(',', f);
        write_arm_json(a->conts[i], file, line, f);
    }
    fprintf(f, "],\"location\":{\"file\":\"%s\",\"line\":%d,\"col\":0}}",
            file, line);
}

void write_ast_json(Item *items, const char *file, FILE *f) {
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
            fputs("{\"flow\":{\"invocation\":", f);
            write_inv_json(it->flow->head, 0, f);
            fputs(",\"continuations\":[", f);
            {
                int i;
                for (i = 0; i < it->flow->narms; i++) {
                    if (i) fputc(',', f);
                    write_arm_json(it->flow->arms[i], file, it->line, f);
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
            fputs("{\"flow\":{\"invocation\":", f);
            write_inv_json(it->flow->head, 0, f);
            fputs(",\"continuations\":[", f);
            {
                int i;
                for (i = 0; i < it->flow->narms; i++) {
                    if (i) fputc(',', f);
                    write_arm_json(it->flow->arms[i], file, it->line, f);
                }
            }
            fputs("],\"pre_label\":null,\"impl_of\":null,\"location\":{\"file\":\"", f);
            fputs(file, f);
            fprintf(f, "\",\"line\":%d,\"col\":0}}}", it->line);
            break;
        }
    }
    fprintf(f, "],\"main_module_name\":\"%s\",\"parts\":[]}", file);
}

/* ================= JSON reader (for --lower) ================= */


const char *jp;
static int jws(void) { while (*jp == ' ' || *jp == '\t' || *jp == '\n' || *jp == '\r') jp++; return *jp != 0; }
static Jv *jnew(int k) { Jv *v = xmalloc(sizeof(Jv)); memset(v, 0, sizeof *v); v->k = k; return v; }

Jv *jparse(void) {
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

Jv *jget(Jv *o, const char *k) {
    int i;
    if (!o || o->k != 5) return 0;
    for (i = 0; i < o->nfs; i++)
        if (!strcmp(o->fs[i].k, k)) return o->fs[i].v;
    return 0;
}
char *jstr(Jv *o, const char *k) {
    Jv *v = jget(o, k);
    return v && v->k == 3 ? v->s : 0;
}
Jv *jarr(Jv *o, const char *k) {
    Jv *v = jget(o, k);
    return v && v->k == 4 ? v : 0;
}
char *jseg0(Jv *path) {    /* event path segments[0] */
    Jv *seg = jarr(path, "segments");
    if (!seg || seg->nxs == 0 || seg->xs[0]->k != 3) return 0;
    return seg->xs[0]->s;
}

