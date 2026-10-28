/* host2 krun — sx leg.  Contract in krun.h. */
#include "krun.h"

/* ================= allocation ================= */

void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fprintf(stderr, "krun: out of memory\n"); exit(4); }
    return p;
}
void *xrealloc(void *p, size_t n) {
    void *q = realloc(p, n ? n : 1);
    if (!q) { fprintf(stderr, "krun: out of memory\n"); exit(4); }
    return q;
}
char *xstrndup(const char *s, size_t n) {
    char *p = xmalloc(n + 1);
    memcpy(p, s, n);
    p[n] = 0;
    return p;
}
char *xstrdup(const char *s) { return xstrndup(s, strlen(s)); }

/* ================= s-expressions ================= */

static Sx *sx_atom(const char *s, size_t n) {
    Sx *x = xmalloc(sizeof(Sx));
    x->is_list = 0; x->atom = xstrndup(s, n); x->kids = 0; x->n = 0;
    return x;
}
static Sx *sx_list(Sx **kids, int n) {
    Sx *x = xmalloc(sizeof(Sx));
    x->is_list = 1; x->atom = 0; x->kids = kids; x->n = n;
    return x;
}
int sx_is_atom(Sx *x, const char *s) {
    return x && !x->is_list && strcmp(x->atom, s) == 0;
}

/* ---- tokenizer: spaces, parens, quoted atoms (kept with quotes,
   unterminated refuses), bare atoms stop at delimiters ---- */

static int tk_space(char c) {
    return c == ' ' || c == '\t' || c == '\n' || c == '\r';
}

char *file_read_all(const char *path) {
    FILE *f = fopen(path, "rb");
    long n;
    char *buf;
    if (!f) return 0;
    fseek(f, 0, SEEK_END); n = ftell(f); fseek(f, 0, SEEK_SET);
    if (n < 0) { fclose(f); return 0; }
    buf = xmalloc((size_t)n + 1);
    if (fread(buf, 1, (size_t)n, f) != (size_t)n) { fclose(f); free(buf); return 0; }
    fclose(f); buf[n] = 0;
    return buf;
}

static int tokenize(const char *src, char ***toks_out, int *ntoks) {
    char **v = 0; int n = 0, cap = 0;
    const char *p = src;
    while (*p) {
        const char *q;
        char *t;
        if (tk_space(*p)) { p++; continue; }
        if (*p == '#') {                     /* comment to end of line */
            while (*p && *p != '\n') p++;
            continue;
        }
        if (*p == '(' || *p == ')') {
            t = xstrndup(p, 1); p++;
        } else if (*p == '"') {
            q = p + 1;
            while (*q && *q != '"') {
                if (*q == '\\' && q[1]) { q += 2; continue; }
                q++;
            }
            if (!*q) return 0;      /* unterminated quote refuses */
            q++;
            t = xstrndup(p, (size_t)(q - p)); p = q;
        } else {
            q = p;
            while (*q && !tk_space(*q) && *q != '(' && *q != ')' && *q != '"')
                q++;
            t = xstrndup(p, (size_t)(q - p)); p = q;
        }
        if (n == cap) { cap = cap ? cap * 2 : 64; v = xrealloc(v, cap * sizeof(char *)); }
        v[n++] = t;
    }
    *toks_out = v; *ntoks = n;
    return 1;
}

/* ---- parser: one sexpr, trailing tokens must be exhausted ---- */

typedef struct { char **toks; int n; int i; } PState;

static Sx *parse_sx(PState *st) {
    char *t;
    if (st->i >= st->n) return 0;
    t = st->toks[st->i];
    if (strcmp(t, "(") == 0) {
        Sx **kids = 0; int n = 0, cap = 0;
        st->i++;
        for (;;) {
            Sx *k;
            if (st->i >= st->n) return 0;   /* unbalanced ( */
            if (strcmp(st->toks[st->i], ")") == 0) { st->i++; break; }
            k = parse_sx(st);
            if (!k) return 0;
            if (n == cap) { cap = cap ? cap * 2 : 8; kids = xrealloc(kids, cap * sizeof(Sx *)); }
            kids[n++] = k;
        }
        return sx_list(kids, n);
    }
    if (strcmp(t, ")") == 0) return 0;
    st->i++;
    return sx_atom(t, strlen(t));
}

Sx *parse_top(const char *line) {
    char **toks = 0; int n = 0;
    PState st; Sx *x;
    if (!tokenize(line, &toks, &n)) return 0;
    st.toks = toks; st.n = n; st.i = 0;
    /* optional [flow-eval] marker atom */
    if (st.i < st.n && strcmp(st.toks[st.i], "[flow-eval]") == 0) st.i++;
    x = parse_sx(&st);
    if (!x || st.i != st.n) return 0;
    if (!x->is_list) return 0;                 /* claim must be a list */
    return x;
}

