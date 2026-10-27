/* host2 krun — main leg.  Contract in krun.h. */
#include "krun.h"

/* ================= result compare + printers ================= */

static int result_eq(Result *a, Result *b) {
    if ((a->branch == 0) != (b->branch == 0)) return 0;
    if (a->branch && strcmp(a->branch, b->branch) != 0) return 0;
    if ((a->payload == 0) != (b->payload == 0)) return 0;
    if (a->payload && !val_eq(a->payload, b->payload)) return 0;
    return 1;
}

static void print_val(Val *v, FILE *f) {
    int i;
    if (!v) { fputs("refuse", f); return; }
    switch (v->tag) {
    case 0: fprintf(f, "(int %lld)", (long long)v->i); break;
    case 1: fprintf(f, "(float %lld %lld)", (long long)v->i, (long long)v->d); break;
    case 2: fprintf(f, "(bool %s)", v->b ? "true" : "false"); break;
    case 3: fprintf(f, "(str \"%s\")", v->s); break;
    case 4:
        fputs("(arr", f);
        for (i = 0; i < v->nx; i++) { fputc(' ', f); print_val(v->xs[i], f); }
        fputc(')', f);
        break;
    case 5:
        fputs("(cell", f);
        for (i = 0; i < v->nf; i++) {
            fprintf(f, " (%s ", v->ns[i]);
            print_val(v->vs[i], f);
            fputc(')', f);
        }
        fputc(')', f);
        break;
    }
}

static void print_result(Result *r, FILE *f) {
    if (!r->branch && !r->payload) { fputs("(void)", f); return; }
    if (!r->branch) { fputs("(bare ", f); print_val(r->payload, f); fputc(')', f); return; }
    fprintf(f, "(tag %s", r->branch);
    if (r->payload) { fputc(' ', f); print_val(r->payload, f); }
    fputc(')', f);
}

/* ================= claim check + main =================
   krun FILE.k            — parse the [flow-eval] claim, re-decide,
                            compare with asserted result.
   krun FILE.k --emit CLAIM
                          — take THIS file's program (a compiler such
                            as kemit.k), quote CLAIM's program, feed
                            it as `src` arg, print the str payload
                            (the emitted C). This is the host-side
                            fixpoint leg: the compiler is data, the C
                            binary only interprets.
   krun --quote CLAIM    — print CLAIM's program as the wire value
                            `(cell (src <quote>))` a compiled-program
                            binary (emitProgC) consumes on stdin. */

int main(int argc, char **argv) {
    char *buf;
    Sx *sx;
    Claim c;
    Result got;

    if (argc != 2 && argc != 3 && argc != 4) {
        fputs("usage: krun FILE.k | krun FILE.k --emit SRC.k"
              " | krun --quote CLAIM\n", stderr);
        return 2;
    }
    if (argc == 4 && strcmp(argv[2], "--emit") != 0) {
        fputs("usage: krun FILE.k | krun FILE.k --emit SRC.k"
              " | krun --quote CLAIM\n", stderr);
        return 2;
    }
    if (argc == 3 && strcmp(argv[1], "--quote") != 0) {
        fputs("usage: krun FILE.k | krun FILE.k --emit SRC.k"
              " | krun --quote CLAIM\n", stderr);
        return 2;
    }

    /* --quote CLAIM: print the entry args cell `(cell (src <quote>))`
       a compiled-program binary (ISAR.KoruProgEmit) consumes on
       stdin — the input wire for the H1 leg. */
    if (argc == 3) {
        char *qbuf; Sx *qsx; Claim qc;
        qbuf = file_read_all(argv[2]);
        qsx = qbuf ? parse_top(qbuf) : 0;
        if (!qsx || !sx_claim(qsx, &qc)) {
            fprintf(stderr, "refuse: %s not a [flow-eval] claim\n", argv[2]);
            return 2;
        }
        fputs("(cell (src ", stdout);
        print_val(quote_prog(&qc.prog), stdout);
        fputs("))\n", stdout);
        return 0;
    }

    buf = file_read_all(argv[1]);
    if (!buf) { fprintf(stderr, "refuse: cannot read %s\n", argv[1]); return 2; }
    sx = parse_top(buf);
    if (!sx) {
        fprintf(stderr, "refuse: %s not a [flow-eval] claim\n", argv[1]);
        return 2;
    }
    if (!sx_claim(sx, &c)) {
        fprintf(stderr, "refuse: %s malformed claim fields\n", argv[1]);
        return 2;
    }

    if (argc == 4) {
        /* emit mode: this file is the compiler; quote SRC's prog,
           invoke its `emit` entry with [("src", quoted)] */
        char *sbuf; Sx *ssx; Claim sc;
        sbuf = file_read_all(argv[3]);
        ssx = sbuf ? parse_top(sbuf) : 0;
        if (!ssx || !sx_claim(ssx, &sc)) {
            fprintf(stderr, "refuse: %s not a [flow-eval] claim\n", argv[3]);
            return 2;
        }
        {
            NV arg;
            arg.n = "src";
            arg.v = quote_prog(&sc.prog);
            if (!eval_prog(c.prog.graph, c.prog.ng, c.oracle, c.noracle,
                           c.fuel, "emit", &arg, 1, &got)) {
                fprintf(stderr, "refuse: %s did not decide emit\n", argv[1]);
                return 3;
            }
            if (!got.payload || !is_str(got.payload)) {
                fprintf(stderr, "refuse: emit payload not a str\n");
                return 3;
            }
            fputs(got.payload->s, stdout);
            fputc('\n', stdout);
            return 0;
        }
    }

    if (!eval_prog(c.prog.graph, c.prog.ng, c.oracle, c.noracle,
                   c.fuel, c.prog.entry, c.prog.args, c.prog.nargs, &got)) {
        if (c.has_expected) {
            fputs("drift: program refused but claim expected ", stderr);
            print_result(&c.expected, stderr);
            fputc('\n', stderr);
            return 4;
        }
        fputs("ok refuse\n", stdout);
        return 0;
    }
    if (!c.has_expected) {
        fputs("drift: program decided but claim expected refuse: ", stderr);
        print_result(&got, stderr);
        fputc('\n', stderr);
        return 4;
    }
    if (!result_eq(&got, &c.expected)) {
        fputs("drift: got ", stderr);
        print_result(&got, stderr);
        fputs(" expected ", stderr);
        print_result(&c.expected, stderr);
        fputc('\n', stderr);
        return 4;
    }
    fputs("ok ", stdout);
    print_result(&got, stdout);
    fputc('\n', stdout);
    return 0;
}
