/* host2 korufe — util leg.  Contract in korufe.h. */
#include "korufe.h"

void *xmalloc(size_t n) {
    void *p = malloc(n ? n : 1);
    if (!p) { fputs("korufe: out of memory\n", stderr); exit(4); }
    return p;
}
char *xstrndup(const char *s, size_t n) {
    char *p = xmalloc(n + 1); memcpy(p, s, n); p[n] = 0; return p;
}
char *xstrdup(const char *s) { return xstrndup(s, strlen(s)); }
char *xasprintf(const char *a, const char *b) {
    size_t n = strlen(a) + strlen(b) + 1;
    char *p = xmalloc(n); snprintf(p, n, "%s%s", a, b); return p;
}

void bput(Buf *b, const char *s) {
    size_t n = strlen(s);
    while (b->n + n + 1 > b->cap) {
        b->cap = b->cap ? b->cap * 2 : 256;
        b->p = realloc(b->p, b->cap);
    }
    memcpy(b->p + b->n, s, n); b->n += n; b->p[b->n] = 0;
}
void bputf(Buf *b, const char *fmt, ...) {
    char tmp[128];
    va_list ap, ap2;
    int n;
    va_start(ap, fmt);
    va_copy(ap2, ap);
    n = vsnprintf(tmp, sizeof tmp, fmt, ap);
    va_end(ap);
    if (n < 0) { va_end(ap2); return; }
    if (n < (int)sizeof tmp) { bput(b, tmp); va_end(ap2); return; }
    {
        char *p = xmalloc((size_t)n + 1);
        vsnprintf(p, (size_t)n + 1, fmt, ap2);
        va_end(ap2);
        bput(b, p);
        free(p);
    }
}
