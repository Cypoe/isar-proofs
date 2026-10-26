/* host2 korufe — lex leg.  Contract in korufe.h. */
#include "korufe.h"

static int punct2(const char *s) {
    return !strcmp(s, "->") || !strcmp(s, "=>") || !strcmp(s, "|>") ||
           !strcmp(s, "==") || !strcmp(s, "!=") || !strcmp(s, "<=") ||
           !strcmp(s, ">=") || !strcmp(s, "&&") || !strcmp(s, "||") ||
           !strcmp(s, "++") || !strcmp(s, "..");
}
static int punct1(char c) {
    return strchr("(){}[],:|+-*/%<>=!#.@&", c) != 0;
}

static int isidc(char c) {
    return (c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') ||
           (c >= '0' && c <= '9') || c == '_';
}

#define GROW_TS \
    if (n == cap) { \
        cap *= 2; \
        { Tk *nt = xmalloc(cap * sizeof(Tk)); \
          memcpy(nt, ts->t, n * sizeof(Tk)); ts->t = nt; } \
    }

Tks *lex_k(const char *src, const char *file, char **err) {
    Tks *ts = xmalloc(sizeof(Tks));
    int cap = 64, n = 0, line = 1;
    const char *p = src;
    ts->t = xmalloc(cap * sizeof(Tk));
    while (*p) {
        char c = *p;
        if (c == '\n') {
            /* newline is a real token — koru is line-oriented; arm
               payloads and item boundaries are line-scoped */
            GROW_TS
            ts->t[n].kind = 6; ts->t[n].text = "nl"; ts->t[n].line = line;
            ts->t[n].pos = p - src;
            n++; line++; p++;
            continue;
        }
        if (c == ' ' || c == '\t' || c == '\r') { p++; continue; }
        if (c == '/' && p[1] == '/') {
            while (*p && *p != '\n') p++;
            continue;
        }
        GROW_TS
        if ((c >= 'a' && c <= 'z') || (c >= 'A' && c <= 'Z') || c == '_') {
            const char *b = p;
            /* `-` inside an ident is koru's word separation; it only
               continues when another ident char follows (`a->b` ends
               the ident at the `->` punct, `a - b` leaves `-` alone) */
            while (isidc(*p) || (*p == '-' && (isidc(p[1]) || p[1] == '-'))) p++;
            ts->t[n].kind = 0;
            ts->t[n].text = xstrndup(b, (size_t)(p - b));
            ts->t[n].line = line; ts->t[n].pos = b - src; n++;
            continue;
        }
        if (c >= '0' && c <= '9') {
            const char *b = p;
            int isf = 0;
            while (*p >= '0' && *p <= '9') p++;
            if (*p == '.' && p[1] >= '0' && p[1] <= '9') {
                isf = 1; p++;
                while (*p >= '0' && *p <= '9') p++;
            }
            ts->t[n].kind = isf ? 2 : 1;
            ts->t[n].text = xstrndup(b, (size_t)(p - b));
            ts->t[n].line = line; ts->t[n].pos = b - src; n++;
            continue;
        }
        if (c == '"') {
            const char *b = p;
            p++;
            while (*p && *p != '"') {
                if (*p == '{' && p[1] == '{') {  /* interpolation */
                    *err = xstrdup("str interpolation {{ }} out of subset");
                    return 0;
                }
                p++;
            }
            if (!*p) { *err = xstrdup("unterminated string"); return 0; }
            p++;
            ts->t[n].kind = 3;
            ts->t[n].text = xstrndup(b, (size_t)(p - b));
            ts->t[n].line = line; ts->t[n].pos = b - src; n++;
            continue;
        }
        if (punct1(c)) {
            if (p[1] && punct2((char[]){c, p[1], 0})) {
                ts->t[n].kind = 4;
                ts->t[n].text = xstrndup(p, 2);
                ts->t[n].line = line; ts->t[n].pos = p - src; n++; p += 2;
            } else {
                ts->t[n].kind = 4;
                ts->t[n].text = xstrndup(p, 1);
                ts->t[n].line = line; ts->t[n].pos = p - src; n++; p++;
            }
            continue;
        }
        {
            char m[64];
            snprintf(m, sizeof m, "unexpected character '%c' at line %d of %s",
                     c, line, file);
            *err = xstrdup(m);
            return 0;
        }
    }
    if (n == cap) {
        cap++;
        { Tk *nt = xmalloc(cap * sizeof(Tk));
          memcpy(nt, ts->t, n * sizeof(Tk)); ts->t = nt; }
    }
    ts->t[n].kind = 5; ts->t[n].text = "eof"; ts->t[n].line = line;
    ts->t[n].pos = p - src; n++;
    ts->n = n; ts->i = 0;
    return ts;
}

/* ---- token ops ---- */
Tk *peek(Tks *s) { return s->i < s->n ? &s->t[s->i] : &s->t[s->n - 1]; }
Tk *next_tk(Tks *s) { return s->i < s->n ? &s->t[s->i++] : &s->t[s->n - 1]; }
int at(Tks *s, const char *w) {
    return peek(s)->kind != 5 && strcmp(peek(s)->text, w) == 0;
}
int at_kind(Tks *s, int k) { return peek(s)->kind == k; }
int eat(Tks *s, const char *w) {
    if (at(s, w)) { s->i++; return 1; }
    return 0;
}
void snl(Tks *s) {                       /* skip newlines */
    while (peek(s)->kind == 6) s->i++;
}
int fail_at(Tks *s, char **err, const char *msg) {
    static char buf[256];
    snprintf(buf, sizeof buf, "parse: %s at line %d (near '%s')",
             msg, peek(s)->line, peek(s)->text);
    *err = xstrdup(buf);
    return 0;
}

