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

const char *korufe_src;

/* the authority's value/condition/plain_value fields are RAW source
   slices (probe: `v>0 && v  <  9` keeps its double spaces) — emit the
   expr's byte span verbatim, not a re-print */
static void jesc_raw(FILE *f, const char *p, const char *end) {
    for (; p < end; p++) {
        unsigned char c = (unsigned char)*p;
        if (c == '"' || c == '\\') fprintf(f, "\\%c", c);
        else if (c == '\n') fputs("\\n", f);
        else if (c == '\r') fputs("\\r", f);
        else if (c == '\t') fputs("\\t", f);
        else if (c < 0x20) fprintf(f, "\\u%04x", c);
        else fputc(c, f);
    }
}

static void jespan(FILE *f, long lo, long hi) {
    fputc('"', f);
    if (korufe_src && hi > lo)
        jesc_raw(f, korufe_src + lo, korufe_src + hi);
    fputc('"', f);
}
static void jese(FILE *f, KExpr *e) {
    jespan(f, e ? e->lo : 0, e ? e->hi : 0);
}

/* expr back to source text — the canon AST keeps values as strings.
   Buffer-accumulating; used for plain_value fields. */

static void write_inv_json(Inv *v, int jump, FILE *f) {
    int j;
    fputs("{\"event\":[", f);
    if (jump) fprintf(f, "\"@%s\"", v->name); else jesc(f, v->name);
    fputs("],\"args\":[", f);
    for (j = 0; j < v->nargs; j++) {
        if (j) fputc(',', f);
        fputs("{\"name\":", f);
        if (v->args[j].n) jesc(f, v->args[j].n); else jesc(f, "");
        fputs(",\"value\":", f);
        jese(f, v->args[j].e);
        fputc('}', f);
    }
    fputs("],\"variant\":null,\"return_binding\":", f);
    if (v->retbind) jesc(f, v->retbind); else fputs("null", f);
    fputc('}', f);
}

static void write_arm_json(ArmD *a, const char *file, int line, FILE *f) {
    int i;
    fputs("{\"branch\":", f); jesc(f, a->branch);
    fprintf(f, ",\"kind\":\"terminal\",\"is_catchall\":%s,\"binding\":",
            a->catchall ? "true" : "false");
    if (a->bind) jesc(f, a->bind); else fputs("null", f);
    fputs(",\"binding_type\":\"branch_payload\",\"condition\":", f);
    if (a->cond) jese(f, a->cond); else fputs("null", f);
    fputs(",\"step\":", f);
    if (a->kind == 1) {           /* produce */
        fputs("{\"type\":\"produce\",\"plain_value\":", f);
        jese(f, a->produce);
        fputs("}", f);
    } else if (a->kind == 2) {    /* ctor */
        fputs("{\"type\":\"branch_constructor\",\"branch_constructor\":{\"branch_name\":", f);
        jesc(f, a->target);
        fputs(",\"fields\":[],\"plain_value\":", f);
        if (a->produce) jese(f, a->produce);
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
        case 2:
            fputs("{\"immediate_impl\":{\"event_path\":{\"module_qualifier\":null,\"segments\":[", f);
            jesc(f, it->name);
            fputs("]},\"value\":{\"branch_name\":\"\",\"fields\":[],\"plain_value\":", f);
            jese(f, it->bare);
            fprintf(f, ",\"has_expressions\":true,\"is_bare_return\":true},\"annotations\":[],\"module\":\"%s\",\"is_impl\":false}}", file);
            break;
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

/* ================= expression trees (--ast-canon) ================
   upstream's canon is a reflective dump of its post-parse AST —
   lossless (retbind, jump args, expression trees all survive).
   `parsed_expression` exists only where koru's own ExprNode can
   hold the shape — array/cell literals are outside that grammar
   and serialize as null with the raw span in `value`. */

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

static int kexpr_parseable(KExpr *e) {
    int i;
    switch (e->tag) {
    case 9: case 10: return 0;
    case 2: case 6:
        return kexpr_parseable(e->a) && kexpr_parseable(e->bb);
    case 3: case 5: case 14:
        return kexpr_parseable(e->a);
    case 4:
        return kexpr_parseable(e->a) && kexpr_parseable(e->bb) &&
               kexpr_parseable(e->c);
    case 7: case 8:
        for (i = 0; i < e->nargs; i++)
            if (!kexpr_parseable(e->args[i].e)) return 0;
        return 1;
    default: return 1;
    }
}

static void kexpr_node(KExpr *e, FILE *f) {
    static const char *bops[] = {
        "add","subtract","multiply","divide","modulo","equal",
        "not_equal","less","less_equal","greater","greater_equal",
        "and_op","or_op","string_concat"};
    int i;
    fputs("{\"node\":{", f);
    switch (e->tag) {
    case 0:
        fprintf(f, "\"literal\":{\"number\":\"%lld\"}", (long long)e->i);
        break;
    case 12: {
        Buf db = {0, 0, 0};
        rat_to_dec(e->i, e->d, &db);
        fputs("\"literal\":{\"number\":", f);
        jesc(f, db.p ? db.p : "");
        fputc('}', f);
        break;
    }
    case 13:
        fputs("\"literal\":{\"string\":", f);
        jesc(f, e->s);
        fputc('}', f);
        break;
    case 11:
        fprintf(f, "\"literal\":{\"boolean\":%s}",
                e->b ? "true" : "false");
        break;
    case 1:
        fputs("\"identifier\":", f);
        jesc(f, e->s);
        break;
    case 2:
        fprintf(f, "\"binary\":{\"op\":\"%s\",\"left\":", bops[e->op]);
        kexpr_node(e->a, f);
        fputs(",\"right\":", f);
        kexpr_node(e->bb, f);
        fputc('}', f);
        break;
    case 3:
        fprintf(f, "\"unary\":{\"op\":\"%s\",\"operand\":",
                e->op == 0 ? "negate" : "not");
        kexpr_node(e->a, f);
        fputc('}', f);
        break;
    case 4:
        fputs("\"conditional\":{\"condition\":", f);
        kexpr_node(e->a, f);
        fputs(",\"then_expr\":", f);
        kexpr_node(e->bb, f);
        fputs(",\"else_expr\":", f);
        kexpr_node(e->c, f);
        fputc('}', f);
        break;
    case 5:
        fputs("\"field_access\":{\"object\":", f);
        kexpr_node(e->a, f);
        fputs(",\"field\":", f);
        jesc(f, e->s);
        fputc('}', f);
        break;
    case 6:
        fputs("\"array_index\":{\"object\":", f);
        kexpr_node(e->a, f);
        fputs(",\"index\":", f);
        kexpr_node(e->bb, f);
        fputc('}', f);
        break;
    case 7:
        fputs("\"builtin_call\":{\"name\":", f);
        jesc(f, e->s);
        fputs(",\"args\":[", f);
        for (i = 0; i < e->nargs; i++) {
            if (i) fputc(',', f);
            kexpr_node(e->args[i].e, f);
        }
        fputs("]}", f);
        break;
    case 8:
        fputs("\"function_call\":{\"callee\":{\"node\":{\"identifier\":", f);
        jesc(f, e->s);
        fputs("}},\"args\":[", f);
        for (i = 0; i < e->nargs; i++) {
            if (i) fputc(',', f);
            kexpr_node(e->args[i].e, f);
        }
        fputs("]}", f);
        break;
    case 14:
        fputs("\"grouped\":", f);
        kexpr_node(e->a, f);
        break;
    default:
        /* unreachable — callers gate on kexpr_parseable */
        fputs("\"expression\":\"\"", f);
        break;
    }
    fputs("}}", f);
}

/* canon arg object — positional names echo the raw value span */
static void carg(KExpr *e, const char *name, FILE *f) {
    fputs("{\"name\":", f);
    if (name) jesc(f, name); else jese(f, e);
    fputs(",\"value\":", f);
    jese(f, e);
    fputs(",\"source_value\":null,\"expression_value\":null,"
          "\"parsed_expression\":", f);
    if (kexpr_parseable(e)) kexpr_node(e, f); else fputs("null", f);
    fputs(",\"phantom_type\":null,\"had_explicit_label\":", f);
    fputs(name ? "true" : "false", f);
    fputc('}', f);
}

static void cinv(Inv *v, FILE *f) {
    int j;
    fputs("{\"path\":{\"module_qualifier\":null,\"segments\":[", f);
    jesc(f, v->name);   /* qualified paths unexercised — one segment */
    fputs("]},\"args\":[", f);
    for (j = 0; j < v->nargs; j++) {
        if (j) fputc(',', f);
        carg(v->args[j].e, v->args[j].n, f);
    }
    fputs("],\"annotations\":[],\"marks\":[],\"inserted_by_tap\":false,"
          "\"from_opaque_tap\":false,\"source_module\":\"\","
          "\"variant\":null,\"return_binding\":", f);
    if (v->retbind) jesc(f, v->retbind); else fputs("null", f);
    fputs(",\"return_binding_annotations\":[],\"return_destructure\":[],"
          "\"inline_body\":null,\"preamble_code\":null}", f);
}

static void cstep(ArmD *a, FILE *f) {
    int j;
    if (a->kind == 1) {         /* produce */
        if (a->produce && a->produce->tag == 4) {
            fputs("{\"invocation\":{\"path\":{\"module_qualifier\":null,"
                  "\"segments\":[\"if\"]},\"args\":[", f);
            carg(a->produce->a, 0, f);
            fputs("],\"annotations\":[],\"marks\":[],"
                  "\"inserted_by_tap\":false,\"from_opaque_tap\":false,"
                  "\"source_module\":\"\",\"variant\":null,"
                  "\"return_binding\":null,"
                  "\"return_binding_annotations\":[],"
                  "\"return_destructure\":[],\"inline_body\":null,"
                  "\"preamble_code\":null}}", f);
        } else {
            fputs("{\"expression\":", f);
            jese(f, a->produce);
            fputc('}', f);
        }
    } else if (a->kind == 2) {  /* ctor */
        fputs("{\"branch_constructor\":{\"branch_name\":", f);
        jesc(f, a->target);
        fputs(",\"fields\":[],\"plain_value\":", f);
        if (a->produce) jese(f, a->produce); else fputs("null", f);
        fputs(",\"has_expressions\":", f);
        fputs(a->produce ? "true" : "false", f);
        fputs(",\"is_bare_return\":false}}", f);
    } else if (a->kind == 3) {  /* invoke */
        fputs("{\"invocation\":", f);
        cinv(a->inv, f);
        fputc('}', f);
    } else if (a->kind == 4) {  /* @jump — canon keeps its args */
        fputs("{\"label_jump\":{\"label\":", f);
        jesc(f, a->inv->name);
        fputs(",\"args\":[", f);
        for (j = 0; j < a->inv->nargs; j++) {
            if (j) fputc(',', f);
            carg(a->inv->args[j].e, a->inv->args[j].n, f);
        }
        fputs("]}}", f);
    }
}

static void ccont(ArmD *a, FILE *f) {
    int i;
    fputs("{\"branch\":", f); jesc(f, a->branch);
    fputs(",\"binding\":", f);
    /* the retbind name lives on the invocation's return_binding;
       an anonymous chain cont's own binding stays null */
    if (a->bind && a->branch[0]) jesc(f, a->bind); else fputs("null", f);
    fputs(",\"binding_annotations\":[],\"binding_marks\":[],"
          "\"destructure\":[],\"binding_type\":\"branch_payload\","
          "\"kind\":\"terminal\",\"is_catchall\":", f);
    fputs(a->catchall ? "true" : "false", f);
    fputs(",\"catchall_metatype\":null,\"condition\":", f);
    if (a->cond) jese(f, a->cond); else fputs("null", f);
    fputs(",\"condition_expr\":", f);
    if (a->cond && kexpr_parseable(a->cond)) kexpr_node(a->cond, f);
    else fputs("null", f);
    fputs(",\"node\":", f);
    if (a->kind <= 0) fputs("null", f); else cstep(a, f);
    fputs(",\"continuations\":[", f);
    for (i = 0; i < a->nconts; i++) {
        if (i) fputc(',', f);
        ccont(a->conts[i], f);
    }
    fputs("],\"is_transformed_subtree\":false}", f);
}

static void cfield(const char *n, const char *t, FILE *f) {
    fputs("{\"name\":", f); jesc(f, n);
    fputs(",\"type\":", f); jesc(f, t);
    fputs(",\"module_path\":null,\"phantom\":null,\"is_source\":false,"
          "\"is_file\":false,\"is_embed_file\":false,"
          "\"is_expression\":false,\"is_invocation_meta\":false,"
          "\"expression\":null,\"expression_str\":null,"
          "\"owns_expression\":false,\"default\":null}", f);
}

static void jesc_dotted(FILE *f, const char *p) {
    fputc('"', f);
    for (; *p; p++) fputc(*p == '/' ? '.' : *p, f);
    fputc('"', f);
}

void write_ast_canon(Item *items, const char *mod, FILE *f) {
    int first = 1;
    Item *it;
    fputs("{\"items\":[{\"import_decl\":{\"path\":\"std/compiler\","
          "\"local_name\":\"std.compiler\",\"module\":", f);
    jesc(f, mod);
    fputs("}}", f);
    for (it = items; it; it = it->next) {
        int i;
        fputc(',', f);
        switch (it->kind) {
        case 0:
            fputs("{\"import_decl\":{\"path\":", f);
            jesc(f, it->import_path);
            fputs(",\"local_name\":", f);
            jesc_dotted(f, it->import_path);
            fputs(",\"module\":", f); jesc(f, mod);
            fputs("}}", f);
            break;
        case 1:
            fputs("{\"event_decl\":{\"path\":{\"module_qualifier\":null,"
                  "\"segments\":[", f);
            jesc(f, it->name);
            fputs("]},\"input\":{\"fields\":[", f);
            for (i = 0; i < it->nfields; i++) {
                if (i) fputc(',', f);
                cfield(it->fields[i].n, it->fields[i].t, f);
            }
            fputs("],\"is_wildcard\":false},\"branches\":[", f);
            for (i = 0; i < it->nbranches; i++) {
                if (i) fputc(',', f);
                fputs("{\"name\":", f); jesc(f, it->branches[i]);
                fputs(",\"payload\":{\"fields\":[", f);
                if (it->btypes && it->btypes[i])
                    cfield("__type_ref", it->btypes[i], f);
                fputs("],\"is_wildcard\":false},\"is_optional\":false,"
                      "\"is_panic\":false,\"kind\":\"terminal\","
                      "\"resume_type\":null,\"resume_phantom\":null,"
                      "\"resume_arms\":null,\"annotations\":[]}", f);
            }
            fputs("],\"return_type\":", f);
            if (it->ret_type) jesc(f, it->ret_type); else fputs("null", f);
            fputs(",\"return_phantom\":null,\"is_public\":", f);
            fputs(it->is_pub ? "true" : "false", f);
            fputs(",\"is_implicit_flow\":false,\"is_pure\":false,"
                  "\"is_transitively_pure\":false,\"module\":", f);
            jesc(f, mod);
            fputs(",\"prose\":\"\",\"annotations\":[]}}", f);
            break;
        case 2:
            fputs("{\"immediate_impl\":{\"event_path\":"
                  "{\"module_qualifier\":null,\"segments\":[", f);
            jesc(f, it->name);
            fputs("]},\"value\":{\"branch_name\":\"\",\"fields\":[],"
                  "\"plain_value\":", f);
            jese(f, it->bare);
            fputs(",\"has_expressions\":true,\"is_bare_return\":true},"
                  "\"annotations\":[],\"module\":", f);
            jesc(f, mod);
            fputs(",\"is_impl\":false}}", f);
            break;
        case 3: case 4:
            fputs("{\"flow\":{\"body\":{\"branch\":\"\",\"binding\":null,"
                  "\"binding_annotations\":[],\"binding_marks\":[],"
                  "\"destructure\":[],\"binding_type\":\"branch_payload\","
                  "\"kind\":\"terminal\",\"is_catchall\":false,"
                  "\"catchall_metatype\":null,\"condition\":null,"
                  "\"condition_expr\":null,\"node\":{\"invocation\":", f);
            cinv(it->flow->head, f);
            fputs("},\"continuations\":[", f);
            for (i = 0; i < it->flow->narms; i++) {
                if (i) fputc(',', f);
                ccont(it->flow->arms[i], f);
            }
            fputs("],\"is_transformed_subtree\":false},"
                  "\"impl_of\":{\"module_qualifier\":null,\"segments\":[", f);
            jesc(f, it->name);
            fputs("]},\"impl_variant\":null,\"is_impl\":false,"
                  "\"pre_label\":", f);
            if (it->flow->pre) jesc(f, it->flow->pre); else fputs("null", f);
            fputs(",\"annotations\":[],\"module\":", f);
            jesc(f, mod);
            fputs(",\"is_pure\":true,\"is_transitively_pure\":false,"
                  "\"site_of\":null,\"super_shape\":null,"
                  "\"inline_body\":null,\"preamble_code\":null}}", f);
            break;
        }
        (void)first;
    }
    fputs("],\"main_module_name\":", f);
    jesc(f, mod);
    fputs(",\"module_annotations\":[],\"parts\":[]}", f);
}

/* ================= --ast-json view (the readable projection)
   The authority's --ast-json is the flat {type,name,location}
   schema — lossier than canon (no return_type, no return_binding,
   jump args dropped, `-> if(c) a else b` surfaces as an `["if"]`
   invocation whose only arg is the condition) — but it is the
   document every lane can emit, so it is the cross-verification
   wire.  Text fields are raw source spans via jespan. ========= */

/* invocation args — the authority writes a positional arg's name
   as the value text itself (probe: f(g()) → name "g()"), so named
   args keep their name and positionals echo their value. */
static void zinv(Inv *v, FILE *f) {
    int j;
    fputs("{\"event\":[", f);
    jesc(f, v->name);
    fputs("],\"args\":[", f);
    for (j = 0; j < v->nargs; j++) {
        if (j) fputc(',', f);
        fputs("{\"name\":", f);
        if (v->args[j].n) jesc(f, v->args[j].n);
        else jese(f, v->args[j].e);
        fputs(",\"value\":", f);
        jese(f, v->args[j].e);
        fputc('}', f);
    }
    fputs("],\"variant\":null}", f);
}

static void zstep(ArmD *a, FILE *f) {
    if (a->kind == 1) {         /* produce */
        if (a->produce && a->produce->tag == 4) {
            /* `-> if(c) t else e` — readable schema: an `["if"]`
               invocation, the else tail is not in args */
            fputs("{\"type\":\"invocation\",\"invocation\":{\"event\":[\"if\"],\"args\":[{\"name\":", f);
            jese(f, a->produce->a);
            fputs(",\"value\":", f);
            jese(f, a->produce->a);
            fputs("}],\"variant\":null}}", f);
        } else {
            fputs("{\"type\":\"expression\",\"expression\":", f);
            jese(f, a->produce);
            fputc('}', f);
        }
    } else if (a->kind == 2) {  /* ctor */
        fputs("{\"type\":\"branch_constructor\",\"branch_constructor\":{\"branch_name\":", f);
        jesc(f, a->target);
        fputs(",\"fields\":[],\"plain_value\":", f);
        if (a->produce) jese(f, a->produce); else fputs("null", f);
        fputs(",\"has_expressions\":", f);
        fputs(a->produce ? "true" : "false", f);
        fputs("}}", f);
    } else if (a->kind == 3) {  /* invoke */
        fputs("{\"type\":\"invocation\",\"invocation\":", f);
        zinv(a->inv, f);
        fputc('}', f);
    } else if (a->kind == 4) {  /* @jump — args dropped in the view */
        fputs("{\"type\":\"label_jump\",\"label\":", f);
        jesc(f, a->inv->name);
        fputc('}', f);
    }
}

static void zcont(ArmD *a, const char *file, FILE *f) {
    int i;
    fputs("{\"branch\":", f); jesc(f, a->branch);
    fprintf(f, ",\"kind\":\"terminal\",\"is_catchall\":%s,\"binding\":",
            a->catchall ? "true" : "false");
    /* the view drops the retbind name on anonymous chain conts —
       the canon keeps it in Inv.retbind */
    if (a->bind && a->branch[0]) jesc(f, a->bind); else fputs("null", f);
    fputs(",\"binding_type\":\"branch_payload\",\"condition\":", f);
    if (a->cond) jese(f, a->cond); else fputs("null", f);
    fprintf(f, ",\"location\":{\"file\":\"%s\",\"line\":%d,\"col\":0},\"step\":",
            file, a->line);
    if (a->kind <= 0) fputs("null", f); else zstep(a, f);
    fputs(",\"continuations\":[", f);
    for (i = 0; i < a->nconts; i++) {
        if (i) fputc(',', f);
        zcont(a->conts[i], file, f);
    }
    fputs("]}", f);
}

void write_ast_json_view(Item *items, const char *file, FILE *f) {
    fputs("{\"module_annotations\":[],\"items\":[", f);
    /* the real frontend injects `import std/compiler` first */
    fprintf(f, "{\"type\":\"import_decl\",\"path\":\"std/compiler\",\"location\":{\"file\":\"%s\",\"line\":1,\"col\":0}}",
            file);
    for (Item *it = items; it; it = it->next) {
        int i;
        fputc(',', f);
        switch (it->kind) {
        case 0:
            fputs("{\"type\":\"import_decl\",\"path\":", f);
            jesc(f, it->import_path);
            fprintf(f, ",\"location\":{\"file\":\"%s\",\"line\":%d,\"col\":0}}",
                    file, it->line);
            break;
        case 1:
            fputs("{\"type\":\"event_decl\",\"name\":", f);
            jesc(f, it->name);
            fputs(",\"path\":[", f); jesc(f, it->name);
            fprintf(f, "],\"module\":\"%s\",\"input\":{\"fields\":[", file);
            for (i = 0; i < it->nfields; i++) {
                if (i) fputc(',', f);
                fputs("{\"name\":", f); jesc(f, it->fields[i].n);
                fputs(",\"type\":", f); jesc(f, it->fields[i].t);
                fputs(",\"is_source\":false,\"is_file\":false,\"is_embed_file\":false,\"is_expression\":false,\"is_invocation_meta\":false,\"phantom\":null}", f);
            }
            fputs("]},\"branches\":[", f);
            for (i = 0; i < it->nbranches; i++) {
                if (i) fputc(',', f);
                fputs("{\"name\":", f); jesc(f, it->branches[i]);
                fputs(",\"kind\":\"terminal\",\"resume\":null,\"resume_phantom\":null,\"is_optional\":false,\"is_panic\":false,\"payload\":{\"fields\":[", f);
                if (it->btypes && it->btypes[i]) {
                    fputs("{\"name\":\"__type_ref\",\"type\":", f);
                    jesc(f, it->btypes[i]);
                    fputs(",\"is_source\":false,\"is_file\":false,\"is_embed_file\":false,\"is_expression\":false,\"is_invocation_meta\":false,\"phantom\":null}", f);
                }
                fputs("]}}", f);
            }
            fprintf(f, "],\"location\":{\"file\":\"%s\",\"line\":%d,\"col\":0}}",
                    file, it->line);
            break;
        case 2: {
            fputs("{\"type\":\"immediate_impl\",\"event_path\":[", f);
            jesc(f, it->name);
            fputs("],\"value\":{\"branch_name\":\"\",\"fields\":[],\"plain_value\":", f);
            jese(f, it->bare);
            fprintf(f, ",\"has_expressions\":true},\"annotations\":[],\"location\":{\"file\":\"%s\",\"line\":%d,\"col\":0},\"is_impl\":false}",
                    file, it->line);
            break;
        }
        case 3: case 4: {
            fputs("{\"type\":\"flow\",\"invocation\":", f);
            zinv(it->flow->head, f);
            fputs(",\"continuations\":[", f);
            for (i = 0; i < it->flow->narms; i++) {
                if (i) fputc(',', f);
                zcont(it->flow->arms[i], file, f);
            }
            fputs("],\"pre_label\":", f);
            if (it->flow->pre) jesc(f, it->flow->pre); else fputs("null", f);
            fputs(",\"impl_of\":", f);
            if (it->kind == 3) {
                fputc('[', f); jesc(f, it->name); fputc(']', f);
            } else fputs("null", f);
            fprintf(f, ",\"location\":{\"file\":\"%s\",\"line\":%d,\"col\":0}}",
                    file, it->line);
            break;
        }
        }
    }
    fputs("]}", f);
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

