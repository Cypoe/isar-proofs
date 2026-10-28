/* host2 korufe — main leg.  Contract in korufe.h. */
#include "korufe.h"

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
    if (argc == 2 || (argc == 3 &&
        (!strcmp(argv[1], "--ast-json") ||
         !strcmp(argv[1], "--ast-canon")))) {
        /* parse → ast.json (korufe's own shape, the --lower input)
           --ast-json  : the readable projection koruc --ast-json
                         emits — the cross-lane interop document
           --ast-canon : the reflective tree dump koruc --ast-canon
                         emits — lossless (retbind, jump args,
                         expression trees) */
        int mode = argc == 3 ? (!strcmp(argv[1], "--ast-canon") ? 2 : 1) : 0;
        const char *path = argv[argc - 1];
        char *src = file_read(path);
        Tks *ts;
        Item *items;
        const char *mod;
        if (!src) { fprintf(stderr, "refuse: cannot read %s\n", path); return 2; }
        korufe_src = src;      /* raw-span text fields slice this */
        ts = lex_k(src, path, &err);
        if (!ts) { fprintf(stderr, "refuse: %s\n", err); return 2; }
        items = parse_program(ts, &err);
        if (!items) { fprintf(stderr, "refuse: %s\n", err); return 2; }
        {
            const char *b = base_name(path);
            char *dot = strrchr(b, '.');
            mod = dot ? xstrndup(b, (size_t)(dot - b)) : b;
        }
        if (mode == 2) write_ast_canon(items, mod, stdout);
        else if (mode == 1) write_ast_json_view(items, mod, stdout);
        else write_ast_json(items, mod, stdout);
        fputc('\n', stdout);
        return 0;
    }
    if (argc == 4 && !strcmp(argv[1], "--reify")) {
        /* flat row wire + the source it indexes → the same
           ast.json `korufe FILE.k` emits — the koru-typed lane's
           lowerer half: input.k --kast--> rows --reify--> ast.json
           --lower--> claim.  `-` reads rows from stdin. */
        char *src = file_read(argv[3]);
        char *rows;
        Item *items;
        const char *b;
        char *dot;
        if (!src) { fprintf(stderr, "refuse: cannot read %s\n", argv[3]); return 2; }
        if (!strcmp(argv[2], "-")) {
            Buf rb = {0, 0, 0};
            char tmp[4096];
            size_t got;
            while ((got = fread(tmp, 1, sizeof tmp - 1, stdin)) > 0) {
                tmp[got] = 0;
                bput(&rb, tmp);
            }
            rows = rb.p ? rb.p : xstrdup("");
        } else {
            rows = file_read(argv[2]);
        }
        if (!rows) { fputs("refuse: cannot read rows\n", stderr); return 2; }
        korufe_src = src;   /* jese slices absolute spans */
        items = reify_rows(rows, src, &err);
        if (!items) { fprintf(stderr, "refuse: %s\n", err); return 2; }
        b = base_name(argv[3]);
        dot = strrchr(b, '.');
        write_ast_json(items, dot ? xstrndup(b, (size_t)(dot - b)) : b,
                       stdout);
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
          "       korufe --ast-json FILE.k\n"
          "       korufe --ast-canon FILE.k\n"
          "       korufe --reify ROWS.txt FILE.k  ('-' = rows on stdin)\n"
          "       korufe --lower FILE.ast.json CASES.json KEY\n",
          stderr);
    return 2;
}
