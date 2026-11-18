// kchain.k — the composed lane as declared shape (generated)
// a-*=kast  l-*=klow  w-*=kwir  chain=wiring;  low-txt and
// emt-txt are arm-less stubs — refusal names the leg.
tor unrealized {} -> string
unrealized -> "unrealized"

tor low-txt {rows: []const i64, src: []const i64} -> string
low-txt = unrealized()

tor wir {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, strs: []const string, ssp: []const i64} -> string
wir = w-w-main(rows, src, names, nsp, strs, ssp)
| r r -> r

tor emt-txt {claim: string} -> string
emt-txt = unrealized()

tor chain {src: []const i64, rows: []const i64, names: []const string, nsp: []const i64, strs: []const string, ssp: []const i64} -> string
chain = a-main(chars: src)
| rows rt |> low-txt(rows: rt, src) : _ |> wir(rows, src, names, nsp, strs, ssp) : claim |> emt-txt(claim)

tor a-peek {chars: []const i64, i: i64, n: i64} -> i64
a-peek -> (if((i >= n)) (0 - 1) else chars[i])

tor a-ws {chars: []const i64, i: i64, n: i64} -> i64
a-ws = a-peek(chars, i, n)
| ws c when (c == 32) || ((c == 9) || ((c == 10) || (c == 13))) |> a-ws(chars, i: (i + 1), n)
| cm c when (c == 47) && (chars[(i + 1)] == 47) |> a-comment(chars, i, n)
| stop _ -> i

tor a-comment {chars: []const i64, i: i64, n: i64} -> i64
a-comment = a-peek(chars, i, n)
| more c when (c >= 0) && !((c == 10)) |> a-comment(chars, i: (i + 1), n)
| eol _ |> a-ws(chars, i, n)

tor a-word {chars: []const i64, i: i64, n: i64} -> i64
a-word = a-peek(chars, i, n)
| more c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i: (i + 1), n)
| stop _ -> i

tor a-toeol {chars: []const i64, i: i64, n: i64} -> i64
a-toeol = a-peek(chars, i, n)
| more c when (c >= 0) && !((c == 10)) |> a-toeol(chars, i: (i + 1), n)
| stop _ -> i

tor a-toarrow {chars: []const i64, i: i64, n: i64} -> i64
a-toarrow = a-peek(chars, i, n)
| arr c when (c == 45) && (chars[(i + 1)] == 62) -> i
| stp c when (c == 124) && (chars[(i + 1)] == 62) -> i
| ctr c when (c == 61) && (chars[(i + 1)] == 62) -> i
| more _ |> a-toarrow(chars, i: (i + 1), n)

tor a-toargend {chars: []const i64, i: i64, n: i64, d: i64, ins: i64} -> i64
a-toargend = a-peek(chars, i, n)
| fin c when c < 0 -> i
| str c when c == 34 |> a-toargend(chars, i: (i + 1), n, d, ins: if((ins == 1)) 0 else 1)
| bs c when (ins == 1) && (c == 92) |> a-toargend(chars, i: (i + 2), n, d, ins)
| deep c when (ins == 0) && (c == 40) |> a-toargend(chars, i: (i + 1), n, d: (d + 1), ins)
| end c when (ins == 0) && ((d == 0) && ((c == 44) || (c == 41))) -> i
| shal c when (ins == 0) && (c == 41) |> a-toargend(chars, i: (i + 1), n, d: (d - 1), ins)
| more _ |> a-toargend(chars, i: (i + 1), n, d, ins)

tor a-typend {chars: []const i64, i: i64, n: i64} -> i64
a-typend = a-peek(chars, i, n)
| stop c when (c == 44) || (c == 125) -> i
| fin c when c < 0 -> i
| more _ |> a-typend(chars, i: (i + 1), n)

tor a-kwtor {chars: []const i64, j: i64, e: i64, n: i64} -> i64
a-kwtor -> (if(((e == (j + 3)) && ((chars[j] == 116) && ((chars[(j + 1)] == 111) && (chars[(j + 2)] == 114))))) 1 else 0)

tor a-kwwhen {chars: []const i64, j: i64, e: i64, n: i64} -> i64
a-kwwhen -> (if(((e == (j + 4)) && ((chars[j] == 119) && ((chars[(j + 1)] == 104) && ((chars[(j + 2)] == 101) && (chars[(j + 3)] == 110)))))) 1 else 0)

tor a-kwimport {chars: []const i64, j: i64, e: i64, n: i64} -> i64
a-kwimport -> (if(((e == (j + 6)) && ((chars[j] == 105) && ((chars[(j + 1)] == 109) && ((chars[(j + 2)] == 112) && ((chars[(j + 3)] == 111) && ((chars[(j + 4)] == 114) && (chars[(j + 5)] == 116)))))))) 1 else 0)

tor a-hws {chars: []const i64, i: i64, n: i64} -> i64
a-hws = a-peek(chars, i, n)
| more c when (c == 32) || (c == 9) |> a-hws(chars, i: (i + 1), n)
| stop _ -> i

tor a-top {chars: []const i64, i: i64, n: i64, out: string} -> string
a-top = a-ws(chars, i, n)
| go j |> a-top-at(chars, i: j, n, out)

tor a-top-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-top-at = a-peek(chars, i, n)
| fin c when c < 0 -> out
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : e |> a-kwd(chars, i, n, out, e)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-kwd {chars: []const i64, i: i64, e: i64, n: i64, out: string} -> string
a-kwd = a-kwtor(chars, j: i, e, n)
| decl k when k == 1 |> a-decl(chars, i: e, n, out)
| item _ |> a-kwd2(chars, i, n, out, e)

tor a-kwd2 {chars: []const i64, i: i64, e: i64, n: i64, out: string} -> string
a-kwd2 = a-kwimport(chars, j: i, e, n)
| imp k when k == 1 |> a-imp-path(chars, i: e, n, out)
| item _ |> a-morf(chars, i: e, n, out, j: i, ne: e)

tor a-imp-path {chars: []const i64, i: i64, n: i64, out: string} -> string
a-imp-path = a-ws(chars, i, n)
| go p |> a-imp-path2(chars, i: p, n, out)

tor a-imp-path2 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-imp-path2 = a-toeol(chars, i, n)
| done p1 |> a-top(chars, i: p1, n, out: (out ++ ("(imp " ++ (@intToString(i) ++ (" " ++ (@intToString(p1) ++ ") "))))))

tor a-morf {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
a-morf = a-ws(chars, i, n)
| go s |> a-morf-at(chars, i: s, n, out, j, ne)

tor a-morf-at {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
a-morf-at = a-peek(chars, i, n)
| impl c when (c == 45) && (chars[(i + 1)] == 62) |> a-impl-body(chars, i: (i + 2), n, out, j, ne)
| flow c when (c == 61) && !((chars[(i + 1)] == 62)) |> a-flow-pre(chars, i: (i + 1), n, out, j, ne)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-impl-body {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
a-impl-body = a-ws(chars, i, n)
| go v0 |> a-impl-val(chars, i: v0, n, out, j, ne)

tor a-impl-val {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
a-impl-val = a-toeol(chars, i, n)
| done v1 |> a-top(chars, i: v1, n, out: (out ++ ("(impl " ++ (@intToString(j) ++ (" " ++ (@intToString(ne) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(v1) ++ ") "))))))))))

tor a-flow-pre {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
a-flow-pre = a-ws(chars, i, n)
| go p |> a-flow-pre0(chars, i: p, n, out, j, ne)

tor a-flow-pre0 {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
a-flow-pre0 = a-peek(chars, i, n)
| lbl c when c == 35 |> a-word(chars, i: (i + 1), n) : le |> a-flow-lbl(chars, i: le, n, j, ne, out: (out ++ ("(lbl " ++ (@intToString((i + 1)) ++ (" " ++ (@intToString(le) ++ ") "))))))
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : he |> a-call-open(chars, i: he, n, out: ((out ++ ("(flw " ++ (@intToString(j) ++ (" " ++ (@intToString(ne) ++ ") "))))) ++ ("(call " ++ (@intToString(i) ++ (" " ++ (@intToString(he) ++ ") "))))))
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-flow-lbl {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
a-flow-lbl = a-ws(chars, i, n)
| go h |> a-flow-pre2(chars, i: h, n, out, j, ne)

tor a-flow-pre2 {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
a-flow-pre2 = a-peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : he |> a-call-open(chars, i: he, n, out: ((out ++ ("(flw " ++ (@intToString(j) ++ (" " ++ (@intToString(ne) ++ ") "))))) ++ ("(call " ++ (@intToString(i) ++ (" " ++ (@intToString(he) ++ ") "))))))
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-call-open {chars: []const i64, i: i64, n: i64, out: string} -> string
a-call-open = a-ws(chars, i, n)
| go a |> a-call-at(chars, i: a, n, out)

tor a-call-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-call-at = a-peek(chars, i, n)
| open c when c == 40 |> a-args(chars, i: (i + 1), n, out)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-args {chars: []const i64, i: i64, n: i64, out: string} -> string
a-args = a-ws(chars, i, n)
| go a |> a-args-at(chars, i: a, n, out)

tor a-args-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-args-at = a-peek(chars, i, n)
| close c when c == 41 |> a-armloop(chars, i: (i + 1), n, out)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : we |> a-argname(chars, i, n, out, we)
| pos _ |> a-argval(chars, i, n, out)

tor a-argname {chars: []const i64, i: i64, we: i64, n: i64, out: string} -> string
a-argname = a-ws(chars, i: we, n)
| go d |> a-argname-at(chars, i: d, n, out, aj: i, ae: we)

tor a-argname-at {chars: []const i64, i: i64, n: i64, aj: i64, ae: i64, out: string} -> string
a-argname-at = a-peek(chars, i, n)
| named c when c == 58 |> a-ws(chars, i: (i + 1), n) : v0 |> a-argvaln(chars, i: v0, n, out, aj, ae)
| pos _ |> a-argval(chars, i: aj, n, out)

tor a-argvaln {chars: []const i64, i: i64, n: i64, aj: i64, ae: i64, out: string} -> string
a-argvaln = a-toargend(chars, i, n, d: 0, ins: 0)
| done v1 |> a-argnext(chars, i: v1, n, out: (out ++ ("(arg " ++ (@intToString(aj) ++ (" " ++ (@intToString(ae) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(v1) ++ ") "))))))))))

tor a-argval {chars: []const i64, i: i64, n: i64, out: string} -> string
a-argval = a-toargend(chars, i, n, d: 0, ins: 0)
| done v1 |> a-argnext(chars, i: v1, n, out: (out ++ ("(arg " ++ (@intToString(0) ++ (" " ++ (@intToString(0) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(v1) ++ ") "))))))))))

tor a-argnext {chars: []const i64, i: i64, n: i64, out: string} -> string
a-argnext = a-ws(chars, i, n)
| go d |> a-argnext-at(chars, i: d, n, out)

tor a-argnext-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-argnext-at = a-peek(chars, i, n)
| more c when c == 44 |> a-args(chars, i: (i + 1), n, out)
| close c when c == 41 |> a-postcall(chars, i: (i + 1), n, out)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-postcall {chars: []const i64, i: i64, n: i64, out: string} -> string
a-postcall = a-hws(chars, i, n)
| go p |> a-postcall-at(chars, i: p, n, out)

tor a-postcall-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-postcall-at = a-peek(chars, i, n)
| rb c when c == 58 |> a-rb-word(chars, i: (i + 1), n, out)
| done _ |> a-armloop(chars, i, n, out)

tor a-rb-word {chars: []const i64, i: i64, n: i64, out: string} -> string
a-rb-word = a-ws(chars, i, n)
| go w |> a-rb-word-at(chars, i: w, n, out)

tor a-rb-word-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-rb-word-at = a-peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : we |> a-rb-tail(chars, i: we, n, out: (out ++ ("(rbind " ++ (@intToString(i) ++ (" " ++ (@intToString(we) ++ ") "))))))
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-rb-tail {chars: []const i64, i: i64, n: i64, out: string} -> string
a-rb-tail = a-hws(chars, i, n)
| go t |> a-rb-tail-at(chars, i: t, n, out)

tor a-rb-tail-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-rb-tail-at = a-peek(chars, i, n)
| step c when (c == 124) && (chars[(i + 1)] == 62) |> a-arm-step(chars, i: (i + 2), n, out)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-armloop {chars: []const i64, i: i64, n: i64, out: string} -> string
a-armloop = a-ws(chars, i, n)
| go a |> a-armloop-at(chars, i: a, n, out)

tor a-armloop-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-armloop-at = a-peek(chars, i, n)
| bar c when (c == 124) && !((chars[(i + 1)] == 62)) |> a-arm(chars, i: (i + 1), n, out)
| item _ |> a-top-at(chars, i, n, out)

tor a-arm {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm = a-ws(chars, i, n)
| go b |> a-arm1(chars, i: b, n, out)

tor a-arm1 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm1 = a-peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : be |> a-arm-tail(chars, i: be, n, out: (out ++ ("(cont " ++ (@intToString(i) ++ (" " ++ (@intToString(be) ++ ") "))))))
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-arm-tail {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm-tail = a-hws(chars, i, n)
| go t |> a-arm-tok(chars, i: t, n, out)

tor a-arm-tok {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm-tok = a-peek(chars, i, n)
| prod c when (c == 45) && (chars[(i + 1)] == 62) |> a-arm-prod(chars, i: (i + 2), n, out)
| step c when (c == 124) && (chars[(i + 1)] == 62) |> a-arm-step(chars, i: (i + 2), n, out)
| ctor c when (c == 61) && (chars[(i + 1)] == 62) |> a-arm-ctor(chars, i: (i + 2), n, out)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : we |> a-arm-kw(chars, i, n, out, we)
| eol c when (c == 10) || (c < 0) |> a-armloop(chars, i, n, out)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-arm-kw {chars: []const i64, i: i64, we: i64, n: i64, out: string} -> string
a-arm-kw = a-kwwhen(chars, j: i, e: we, n)
| cond k when k == 1 |> a-arm-cond(chars, i: we, n, out)
| bind _ |> a-arm-tail(chars, i: we, n, out: (out ++ ("(bind " ++ (@intToString(i) ++ (" " ++ (@intToString(we) ++ ") "))))))

tor a-arm-cond {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm-cond = a-ws(chars, i, n)
| go c0 |> a-arm-cond2(chars, i: c0, n, out)

tor a-arm-cond2 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm-cond2 = a-toarrow(chars, i, n)
| done c1 |> a-arm-tok(chars, i: c1, n, out: (out ++ ("(cond " ++ (@intToString(i) ++ (" " ++ (@intToString(c1) ++ ") "))))))

tor a-arm-prod {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm-prod = a-ws(chars, i, n)
| go v0 |> a-arm-prod2(chars, i: v0, n, out)

tor a-arm-prod2 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm-prod2 = a-toeol(chars, i, n)
| done v1 |> a-armloop(chars, i: v1, n, out: (out ++ ("(step expr " ++ (@intToString(i) ++ (" " ++ (@intToString(v1) ++ ") "))))))

tor a-arm-step {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm-step = a-ws(chars, i, n)
| go s |> a-arm-step2(chars, i: s, n, out)

tor a-arm-step2 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm-step2 = a-peek(chars, i, n)
| jump c when c == 64 |> a-word(chars, i: (i + 1), n) : le |> a-call-open(chars, i: le, n, out: (out ++ ("(step jump " ++ (@intToString((i + 1)) ++ (" " ++ (@intToString(le) ++ ") "))))))
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : se |> a-call-open(chars, i: se, n, out: (out ++ ("(step invoke " ++ (@intToString(i) ++ (" " ++ (@intToString(se) ++ ") "))))))
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-arm-ctor {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm-ctor = a-ws(chars, i, n)
| go w |> a-arm-ctor1(chars, i: w, n, out)

tor a-arm-ctor1 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm-ctor1 = a-peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : ce |> a-arm-ctor2(chars, i: ce, n, out, cj: i, ce)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-arm-ctor2 {chars: []const i64, i: i64, n: i64, cj: i64, ce: i64, out: string} -> string
a-arm-ctor2 = a-ws(chars, i, n)
| go p |> a-arm-ctor3(chars, i: p, n, out, cj, ce)

tor a-arm-ctor3 {chars: []const i64, i: i64, n: i64, cj: i64, ce: i64, out: string} -> string
a-arm-ctor3 = a-toeol(chars, i, n)
| done t1 |> a-armloop(chars, i: t1, n, out: (out ++ ("(ctor " ++ (@intToString(cj) ++ (" " ++ (@intToString(ce) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(t1) ++ ") "))))))))))

tor a-decl {chars: []const i64, i: i64, n: i64, out: string} -> string
a-decl = a-ws(chars, i, n)
| go d |> a-decl1(chars, i: d, n, out)

tor a-decl1 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-decl1 = a-peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : de |> a-decl-brace(chars, i: de, n, out: (out ++ ("(ev " ++ (@intToString(i) ++ (" " ++ (@intToString(de) ++ ") "))))))
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-decl-brace {chars: []const i64, i: i64, n: i64, out: string} -> string
a-decl-brace = a-ws(chars, i, n)
| go b |> a-decl-brace2(chars, i: b, n, out)

tor a-decl-brace2 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-decl-brace2 = a-peek(chars, i, n)
| open c when c == 123 |> a-fields(chars, i: (i + 1), n, out)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-fields {chars: []const i64, i: i64, n: i64, out: string} -> string
a-fields = a-ws(chars, i, n)
| go f |> a-fields-at(chars, i: f, n, out)

tor a-fields-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-fields-at = a-peek(chars, i, n)
| close c when c == 125 |> a-decl-ret(chars, i: (i + 1), n, out)
| var c when c == 124 |> a-variant(chars, i: (i + 1), n, out)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : fe |> a-fld(chars, i, n, out, fe)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-fld {chars: []const i64, i: i64, fe: i64, n: i64, out: string} -> string
a-fld = a-ws(chars, i: fe, n)
| go c |> a-fld2(chars, i: c, n, out, fj: i, fe)

tor a-fld2 {chars: []const i64, i: i64, n: i64, fj: i64, fe: i64, out: string} -> string
a-fld2 = a-peek(chars, i, n)
| ty k when k == 58 |> a-ws(chars, i: (i + 1), n) : t0 |> a-fld3(chars, i: t0, n, out, fj, fe)
| bad k -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(k) ++ ") "))))))

tor a-fld3 {chars: []const i64, i: i64, n: i64, fj: i64, fe: i64, out: string} -> string
a-fld3 = a-typend(chars, i, n)
| done t1 |> a-fields2(chars, i: t1, n, out: (out ++ ("(fld " ++ (@intToString(fj) ++ (" " ++ (@intToString(fe) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(t1) ++ ") "))))))))))

tor a-fields2 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-fields2 = a-ws(chars, i, n)
| go d |> a-fields2-at(chars, i: d, n, out)

tor a-fields2-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-fields2-at = a-peek(chars, i, n)
| more c when c == 44 |> a-fields(chars, i: (i + 1), n, out)
| close c when c == 125 |> a-decl-ret(chars, i: (i + 1), n, out)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-variant {chars: []const i64, i: i64, n: i64, out: string} -> string
a-variant = a-ws(chars, i, n)
| go v |> a-variant1(chars, i: v, n, out)

tor a-variant1 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-variant1 = a-peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : ve |> a-variant2(chars, i, n, out, ve)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-variant2 {chars: []const i64, i: i64, ve: i64, n: i64, out: string} -> string
a-variant2 = a-ws(chars, i: ve, n)
| go t0 |> a-variant3(chars, i: t0, n, out, vj: i, ve)

tor a-variant3 {chars: []const i64, i: i64, n: i64, vj: i64, ve: i64, out: string} -> string
a-variant3 = a-toeol(chars, i, n)
| done t1 |> a-fields(chars, i: t1, n, out: (out ++ ("(brd " ++ (@intToString(vj) ++ (" " ++ (@intToString(ve) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(t1) ++ ") "))))))))))

tor a-decl-ret {chars: []const i64, i: i64, n: i64, out: string} -> string
a-decl-ret = a-ws(chars, i, n)
| go r |> a-decl-ret-at(chars, i: r, n, out)

tor a-decl-ret-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-decl-ret-at = a-peek(chars, i, n)
| ret c when (c == 45) && (chars[(i + 1)] == 62) |> a-ws(chars, i: (i + 2), n) : t0 |> a-decl-ret2(chars, i: t0, n, out)
| next _ |> a-branches(chars, i, n, out)

tor a-decl-ret2 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-decl-ret2 = a-toeol(chars, i, n)
| done t1 |> a-branches(chars, i: t1, n, out: (out ++ ("(ret " ++ (@intToString(i) ++ (" " ++ (@intToString(t1) ++ ") "))))))

tor a-branches {chars: []const i64, i: i64, n: i64, out: string} -> string
a-branches = a-ws(chars, i, n)
| go b |> a-branches-at(chars, i: b, n, out)

tor a-branches-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-branches-at = a-peek(chars, i, n)
| br c when (c == 124) && !((chars[(i + 1)] == 62)) |> a-branch(chars, i: (i + 1), n, out)
| next _ |> a-top-at(chars, i, n, out)

tor a-branch {chars: []const i64, i: i64, n: i64, out: string} -> string
a-branch = a-ws(chars, i, n)
| go w |> a-branch1(chars, i: w, n, out)

tor a-branch1 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-branch1 = a-peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : be |> a-branch-ty(chars, i: be, n, out, bj: i, be)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor a-branch-ty {chars: []const i64, i: i64, n: i64, bj: i64, be: i64, out: string} -> string
a-branch-ty = a-hws(chars, i, n)
| h h |> a-branch-ty2(chars, i: h, n, out, bj, be)

tor a-branch-ty2 {chars: []const i64, i: i64, n: i64, bj: i64, be: i64, out: string} -> string
a-branch-ty2 = a-peek(chars, i, n)
| eol c when (c == 10) || (c < 0) |> a-branches(chars, i, n, out: (out ++ ("(brd " ++ (@intToString(bj) ++ (" " ++ (@intToString(be) ++ (" " ++ (@intToString(0) ++ (" " ++ (@intToString(0) ++ ") "))))))))))
| ty _ |> a-toeol(chars, i, n) : t1 |> a-branches(chars, i: t1, n, out: (out ++ ("(brd " ++ (@intToString(bj) ++ (" " ++ (@intToString(be) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(t1) ++ ") "))))))))))

tor a-main {chars: []const i64} -> string
a-main = a-top(chars, i: 0, n: @len(chars), out: "")
| done s -> s

tor l-pkb {t: []const i64, i: i64, n: i64} -> i64
l-pkb -> (if(((i < 0) || (i >= n))) (0 - 1) else t[i])

tor l-lxt {src: []const i64, i: i64, hi: i64, d: i64, ins: i64} -> i64
l-lxt = l-pkb(t: src, i, n: hi)
| fin c when c < 0 -> hi
| ql c when (ins == 1) && (c == 34) |> l-lxt(src, i: (i + 1), hi, d, ins: 0)
| bs c when (ins == 1) && (c == 92) |> l-lxt(src, i: (i + 2), hi, d, ins)
| iq _ when ins == 1 |> l-lxt(src, i: (i + 1), hi, d, ins)
| qo c when c == 34 |> l-lxt(src, i: (i + 1), hi, d, ins: 1)
| dop c when (c == 40) || ((c == 91) || (c == 123)) |> l-lxt(src, i: (i + 1), hi, d: (d + 1), ins)
| dcl c when (c == 41) || ((c == 93) || (c == 125)) |> l-lxt(src, i: (i + 1), hi, d: (d - 1), ins)
| oo c when (d == 0) && ((c == 124) && (((i + 1) < hi) && (src[(i + 1)] == 124))) |> l-lxt(src, i: (i + 2), hi, d, ins)
| ob c when (d == 0) && ((c == 124) && ((i > 0) && (src[(i - 1)] == 124))) |> l-lxt(src, i: (i + 1), hi, d, ins)
| pp c when (d == 0) && (c == 124) -> i
| aw c when (d == 0) && (((c == 61) || (c == 45)) && (((i + 1) < hi) && (src[(i + 1)] == 62))) -> i
| cm c when (d == 0) && ((c == 47) && (((i + 1) < hi) && (src[(i + 1)] == 47))) -> i
| mo _ |> l-lxt(src, i: (i + 1), hi, d, ins)

tor l-ltma {src: []const i64, i: i64, hi: i64} -> i64
l-ltma = l-pkb(t: src, i, n: hi)
| ws c when (c == 32) || ((c == 9) || ((c == 10) || (c == 13))) |> l-ltma(src, i: (i + 1), hi)
| dn _ -> i

tor l-ltmb {src: []const i64, lo: i64, j: i64, n: i64} -> i64
l-ltmb = l-pkb(t: src, i: j, n)
| ws c when (j >= lo) && ((c == 32) || ((c == 9) || ((c == 10) || (c == 13)))) |> l-ltmb(src, lo, j: (j - 1), n)
| dn _ -> ((j + 1))

tor l-ltk1 {src: []const i64, i: i64, hi: i64} -> i64
l-ltk1 = l-pkb(t: src, i, n: hi)
| fin c when c < 0 -> hi
| ct c when (c == 47) && (((i + 1) < hi) && (src[(i + 1)] == 47)) -> i
| ws c when (c == 32) || ((c == 9) || ((c == 10) || (c == 13))) -> i
| mo _ |> l-ltk1(src, i: (i + 1), hi)

tor l-lty1 {src: []const i64, i: i64, hi: i64} -> i64
l-lty1 = l-pkb(t: src, i, n: hi)
| fin c when c < 0 -> hi
| ct c when (c == 47) && (((i + 1) < hi) && (src[(i + 1)] == 47)) -> i
| mo _ |> l-lty1(src, i: (i + 1), hi)

tor l-ltm2 {src: []const i64, lo: i64, j: i64, n: i64} -> i64
l-ltm2 = l-pkb(t: src, i: j, n)
| ws c when (j >= lo) && ((c == 32) || (c == 9)) |> l-ltm2(src, lo, j: (j - 1), n)
| dn _ -> ((j + 1))

tor l-lln {src: []const i64, i: i64, off: i64, n: i64, l: i64} -> i64
l-lln = l-pkb(t: src, i, n)
| fin c when (i >= off) || (c < 0) -> l
| nl c when c == 10 |> l-lln(src, i: (i + 1), off, n, l: (l + 1))
| ch _ |> l-lln(src, i: (i + 1), off, n, l)

tor l-lbs {src: []const i64, i: i64, n: i64} -> i64
l-lbs = l-pkb(t: src, i: (i - 1), n)
| nl c when (i <= 0) || (c == 10) -> i
| ch _ |> l-lbs(src, i: (i - 1), n)

tor l-lpb {src: []const i64, i: i64, ls: i64, j: i64, n: i64} -> i64
l-lpb = l-pkb(t: src, i, n)
| pb c when ((i + 4) <= j) && ((c == 112) && ((src[(i + 1)] == 117) && ((src[(i + 2)] == 98) && (((src[(i + 3)] == 32) || (src[(i + 3)] == 9)) && ((i == ls) || ((src[(i - 1)] == 32) || (src[(i - 1)] == 9))))))) -> 1
| nx _ when i < j |> l-lpb(src, i: (i + 1), ls, j, n)
| no _ -> 0

tor l-lpub {src: []const i64, j: i64, n: i64} -> i64
l-lpub = l-lbs(src, i: j, n)
| s ls |> l-lpb(src, i: ls, ls, j, n)

tor l-lhx {d: i64} -> string
l-lhx -> (if((d < 10)) @intToString(d) else if((d == 10)) "a" else if((d == 11)) "b" else if((d == 12)) "c" else if((d == 13)) "d" else if((d == 14)) "e" else "f")

tor l-escl {src: []const i64, i: i64, hi: i64, out: string} -> string
l-escl = l-pkb(t: src, i, n: hi)
| fin c when c < 0 -> out
| ch c when c <= 127 |> l-esca(src, i, hi, out, c)

tor l-esca {src: []const i64, i: i64, hi: i64, out: string, c: i64} -> string
l-esca = l-lhx(d: (c / 16))
| hd a |> l-escb(src, i, hi, out, c, a)

tor l-escb {src: []const i64, i: i64, hi: i64, out: string, c: i64, a: string} -> string
l-escb = l-lhx(d: (c % 16))
| hd b |> l-escl(src, i: (i + 1), hi, out: (out ++ ("\\u00" ++ (a ++ b))))

tor l-escx {src: []const i64, lo: i64, hi: i64, n: i64, out: string} -> string
l-escx = l-lxt(src, i: lo, hi, d: 0, ins: 0)
| cut c |> l-escx1(src, lo, xt: c, n, out)

tor l-escx1 {src: []const i64, lo: i64, xt: i64, n: i64, out: string} -> string
l-escx1 = l-ltma(src, i: lo, hi: xt)
| at a |> l-escx2(src, a, xt, n, out)

tor l-escx2 {src: []const i64, a: i64, xt: i64, n: i64, out: string} -> string
l-escx2 = l-ltmb(src, lo: a, j: (xt - 1), n)
| bt b |> l-escl(src, i: a, hi: b, out)

tor l-esct {src: []const i64, lo: i64, hi: i64, n: i64, out: string} -> string
l-esct = l-ltmb(src, lo, j: (hi - 1), n)
| tb b |> l-esct1(src, lo, b, n, out)

tor l-esct1 {src: []const i64, lo: i64, b: i64, n: i64, out: string} -> string
l-esct1 = l-ltk1(src, i: lo, hi: b)
| ct c |> l-escl(src, i: lo, hi: c, out)

tor l-escty {src: []const i64, lo: i64, hi: i64, n: i64, out: string} -> string
l-escty = l-ltmb(src, lo, j: (hi - 1), n)
| tb b |> l-escty1(src, lo, b, n, out)

tor l-escty1 {src: []const i64, lo: i64, b: i64, n: i64, out: string} -> string
l-escty1 = l-lty1(src, i: lo, hi: b)
| ct c |> l-escty2(src, lo, c, n, out)

tor l-escty2 {src: []const i64, lo: i64, c: i64, n: i64, out: string} -> string
l-escty2 = l-ltm2(src, lo, j: (c - 1), n)
| db d |> l-escl(src, i: lo, hi: d, out)

tor l-lcls {dp: i64, mod: []const i64, fln: i64, nmod: i64, out: string} -> string
l-lcls = l-pkb(t: mod, i: 0, n: nmod)
| done _ when dp == 0 -> out
| more _ |> l-lclsm(dp, mod, fln, nmod, out)

tor l-lclsm {dp: i64, mod: []const i64, fln: i64, nmod: i64, out: string} -> string
l-lclsm = l-escl(src: mod, i: 0, hi: nmod, out: (out ++ "],\"location\":{\"file\":\""))
| md e |> l-lclsn(dp, mod, fln, nmod, out: e)

tor l-lclsn {dp: i64, mod: []const i64, fln: i64, nmod: i64, out: string} -> string
l-lclsn = l-pkb(t: mod, i: 0, n: nmod)
| go _ |> l-lcls(dp: (dp - 1), mod, fln, nmod, out: (out ++ ("\",\"line\":" ++ (@intToString(fln) ++ ",\"col\":0}}"))))

tor l-ltail {mod: []const i64, nmod: i64, out: string} -> string
l-ltail = l-escl(src: mod, i: 0, hi: nmod, out: (out ++ "],\"main_module_name\":\""))
| done e -> ((e ++ "\",\"parts\":[]}"))

tor l-limp {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
l-limp = l-esct(src, lo: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], n: @len(src), out: (out ++ ",{\"import_decl\":{\"path\":\""))
| p e |> l-limp2(rows, i, n, src, mod, out: e, p0, p1)

tor l-limp2 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
l-limp2 = l-esct(src, lo: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], n: @len(src), out: (out ++ "\",\"local_name\":\""))
| p e |> l-limpm(rows, i, n, src, mod, out: e, p0, p1)

tor l-limpm {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
l-limpm = l-escl(src: mod, i: 0, hi: @len(mod), out: (out ++ "\",\"module\":\""))
| p e |> l-ltop(rows, i: (i + 1), n, src, mod, out: (e ++ "\"}}"), p0, p1, q0: (0 - 1))

tor l-limpl {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
l-limpl = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ ",{\"immediate_impl\":{\"event_path\":{\"module_qualifier\":null,\"segments\":[\""))
| p e |> l-limpl2(rows, i, n, src, mod, out: e, p0, p1)

tor l-limpl2 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
l-limpl2 = l-escx(src, lo: rows[((i * 6) + 4)], hi: rows[((i * 6) + 5)], n: @len(src), out: (out ++ "\"]},\"value\":{\"branch_name\":\"\",\"fields\":[],\"plain_value\":\""))
| p e |> l-limplm(rows, i, n, src, mod, out: e, p0, p1)

tor l-limplm {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
l-limplm = l-escl(src: mod, i: 0, hi: @len(mod), out: (out ++ "\",\"has_expressions\":true,\"is_bare_return\":true},\"annotations\":[],\"module\":\""))
| p e |> l-ltop(rows, i: (i + 1), n, src, mod, out: (e ++ "\",\"is_impl\":false}}"), p0, p1, q0: (0 - 1))

tor l-levo {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
l-levo = l-lpub(src, j: rows[((i * 6) + 2)], n: @len(src))
| pb evp |> l-levoe(rows, i, n, src, mod, out, evp, p0, p1)

tor l-levoe {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, evp: i64, p0: i64, p1: i64} -> string
l-levoe = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ ",{\"event_decl\":{\"path\":{\"module_qualifier\":null,\"segments\":[\""))
| p e |> l-levf(rows, i: (i + 1), n, src, mod, out: (e ++ "\"]},\"input\":{\"fields\":["), ff: 0, bf: 0, r0: (0 - 1), r1: (0 - 1), evp, p0, p1)

tor l-levf {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, ff: i64, bf: i64, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
l-levf = l-pkb(t: rows, i: (i * 6), n)
| fld k when (k == 2) && (((rows[((i * 6) + 2)] >= 0) && (rows[((i * 6) + 3)] >= rows[((i * 6) + 2)])) && (rows[((i * 6) + 3)] <= @len(src))) |> l-lfld(rows, i, n, src, mod, out, ff, r0, r1, evp, p0, p1)
| ret k when (k == 3) && (((rows[((i * 6) + 2)] >= 0) && (rows[((i * 6) + 3)] >= rows[((i * 6) + 2)])) && (rows[((i * 6) + 3)] <= @len(src))) |> l-levf(rows, i: (i + 1), n, src, mod, out, ff, bf, r0: rows[((i * 6) + 2)], r1: rows[((i * 6) + 3)], evp, p0, p1)
| brf k when (k == 4) && ((bf == 0) && (((rows[((i * 6) + 2)] >= 0) && (rows[((i * 6) + 3)] >= rows[((i * 6) + 2)])) && (rows[((i * 6) + 3)] <= @len(src)))) |> l-lbrdf(rows, i, n, src, mod, out, r0, r1, evp, p0, p1)
| brn k when (k == 4) && ((bf == 1) && (((rows[((i * 6) + 2)] >= 0) && (rows[((i * 6) + 3)] >= rows[((i * 6) + 2)])) && (rows[((i * 6) + 3)] <= @len(src)))) |> l-lbrdn(rows, i, n, src, mod, out, r0, r1, evp, p0, p1)
| clo _ when bf == 0 |> l-levcc(rows, i, n, src, mod, out, r0, r1, evp, p0, p1)
| clb _ when bf == 1 |> l-levcc2(rows, i, n, src, mod, out, r0, r1, evp, p0, p1)

tor l-lfld {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, ff: i64, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
l-lfld = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ ((if((ff == 1)) "," else "") ++ "{\"name\":\"")))
| p e |> l-lfldn(rows, i, n, src, mod, out: e, r0, r1, evp, p0, p1)

tor l-lfldn {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
l-lfldn = l-escty(src, lo: rows[((i * 6) + 4)], hi: rows[((i * 6) + 5)], n: @len(src), out: (out ++ "\",\"type\":\""))
| p e |> l-levf(rows, i: (i + 1), n, src, mod, out: (e ++ "\",\"module_path\":null,\"phantom\":null,\"is_source\":false,\"is_file\":false,\"is_embed_file\":false,\"is_expression\":false,\"is_invocation_meta\":false,\"expression\":null,\"expression_str\":null,\"owns_expression\":false,\"default\":null}"), ff: 1, bf: 0, r0, r1, evp, p0, p1)

tor l-lbrdf {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
l-lbrdf = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ "],\"is_wildcard\":false},\"branches\":[{\"name\":\""))
| p e |> l-levf(rows, i: (i + 1), n, src, mod, out: (e ++ "\",\"kind\":\"terminal\",\"resume\":null,\"resume_phantom\":null,\"is_optional\":false,\"is_panic\":false,\"payload\":{\"fields\":[]}}"), ff: 1, bf: 1, r0, r1, evp, p0, p1)

tor l-lbrdn {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
l-lbrdn = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ ",{\"name\":\""))
| p e |> l-levf(rows, i: (i + 1), n, src, mod, out: (e ++ "\",\"kind\":\"terminal\",\"resume\":null,\"resume_phantom\":null,\"is_optional\":false,\"is_panic\":false,\"payload\":{\"fields\":[]}}"), ff: 1, bf: 1, r0, r1, evp, p0, p1)

tor l-levcc {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
l-levcc = l-pkb(t: src, i: r0, n: @len(src))
| hasr _ when r0 >= 0 |> l-levc1(rows, i, n, src, mod, out: (out ++ "],\"is_wildcard\":false},\"branches\":[],\"return_type\":\""), r0, r1, evp, p0, p1)
| nor _ |> l-levcm(rows, i, n, src, mod, out: (out ++ "],\"is_wildcard\":false},\"branches\":[],\"return_type\":null"), evp, p0, p1)

tor l-levcc2 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
l-levcc2 = l-pkb(t: src, i: r0, n: @len(src))
| hasr _ when r0 >= 0 |> l-levc1(rows, i, n, src, mod, out: (out ++ "],\"return_type\":\""), r0, r1, evp, p0, p1)
| nor _ |> l-levcm(rows, i, n, src, mod, out: (out ++ "],\"return_type\":null"), evp, p0, p1)

tor l-levc1 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
l-levc1 = l-esct(src, lo: r0, hi: r1, n: @len(src), out)
| t e |> l-levcm(rows, i, n, src, mod, out: (e ++ "\""), evp, p0, p1)

tor l-levcm {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, evp: i64, p0: i64, p1: i64} -> string
l-levcm = l-escl(src: mod, i: 0, hi: @len(mod), out: (out ++ (",\"return_phantom\":null,\"is_public\":" ++ ((if((evp == 1)) "true" else "false") ++ ",\"is_implicit_flow\":false,\"annotations\":[],\"prose\":\"\",\"is_pure\":false,\"is_transitively_pure\":false,\"module\":\""))))
| m e |> l-ltop(rows, i, n, src, mod, out: (e ++ "\"}}"), p0, p1, q0: (0 - 1))

tor l-lflw {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
l-lflw = l-lln(src, i: 0, off: rows[((i * 6) + 2)], n: @len(src), l: 1)
| ln l |> l-lhead(rows, i: (i + 1), n, src, mod, out: (out ++ ",{\"flow\":{\"invocation\":"), f0: rows[((i * 6) + 2)], f1: rows[((i * 6) + 3)], fln: l, k4: 0, pr0: p0, pr1: p1, q0: (0 - 1), q1: (0 - 1), dp: 0, af: 0, cs: 0, hn: 0)

tor l-lhead {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lhead = l-pkb(t: rows, i: (i * 6), n)
| call k when (k == 8) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> l-lcall(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-lcall {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lcall = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ "{\"event\":[\""))
| e v |> l-linv(rows, i: (i + 1), n, src, mod, out: (v ++ "\"],\"args\":["), f0, f1, fln, k4: if((rows[((i * 6) + 2)] == f0)) 1 else 0, pr0, pr1, q0, q1, dp, af, cs, hn, wh: 0, as: 0)

tor l-linv {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, wh: i64, as: i64} -> string
l-linv = l-pkb(t: rows, i: (i * 6), n)
| arg k when (k == 9) && ((rows[((i * 6) + 4)] >= 0) && ((rows[((i * 6) + 4)] >= 0) && ((rows[((i * 6) + 5)] >= rows[((i * 6) + 4)]) && (rows[((i * 6) + 5)] <= @len(src))))) |> l-larg(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh, as)
| rb k when (k == 10) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> l-lrb(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh)
| oth _ |> l-lconts(rows, i, n, src, mod, out: (out ++ ("],\"variant\":null,\"return_binding\":null" ++ ((if((wh == 1)) "}}" else "}") ++ ",\"continuations\":["))), f0, f1, fln, k4, pr0, pr1, q0, q1, dp: (dp + 1), af: 0, cs: if((wh == 1)) 1 else 0, hn)

tor l-larg {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, wh: i64, as: i64} -> string
l-larg = l-pkb(t: src, i: rows[((i * 6) + 2)], n: @len(src))
| nm _ when rows[((i * 6) + 2)] > 0 |> l-largn(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh, as)
| ps _ |> l-largp(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh, as)

tor l-largn {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, wh: i64, as: i64} -> string
l-largn = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ ((if((as == 1)) "," else "") ++ "{\"name\":\"")))
| nm e |> l-largm(rows, i, n, src, mod, out: (e ++ "\",\"value\":\""), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh)

tor l-largp {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, wh: i64, as: i64} -> string
l-largp = l-escx(src, lo: rows[((i * 6) + 4)], hi: rows[((i * 6) + 5)], n: @len(src), out: (out ++ ((if((as == 1)) "," else "") ++ "{\"name\":\"\",\"value\":\"")))
| v e |> l-linv(rows, i: (i + 1), n, src, mod, out: (e ++ "\"}"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh, as: 1)

tor l-largm {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, wh: i64} -> string
l-largm = l-escx(src, lo: rows[((i * 6) + 4)], hi: rows[((i * 6) + 5)], n: @len(src), out)
| v e |> l-linv(rows, i: (i + 1), n, src, mod, out: (e ++ "\"}"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh, as: 1)

tor l-lrb {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, wh: i64} -> string
l-lrb = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ "],\"variant\":null,\"return_binding\":\""))
| e v |> l-lconts(rows, i: (i + 1), n, src, mod, out: (v ++ ("\"" ++ ((if((wh == 1)) "}}" else "}") ++ ",\"continuations\":["))), f0, f1, fln, k4, pr0, pr1, q0: rows[((i * 6) + 2)], q1: rows[((i * 6) + 3)], dp: (dp + 1), af: 0, cs: if((wh == 1)) 1 else 0, hn)

tor l-lbind {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lbind = l-pkb(t: rows, i: (i * 6), n)
| bd k when (k == 12) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> l-lbd(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| oth _ |> l-lcond(rows, i, n, src, mod, out: (out ++ "null,\"binding_type\":\"branch_payload\",\"condition\":"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-lbd {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lbd = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ "\""))
| e v |> l-lcond(rows, i: (i + 1), n, src, mod, out: (v ++ "\",\"binding_type\":\"branch_payload\",\"condition\":"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-lcond {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lcond = l-pkb(t: rows, i: (i * 6), n)
| cd k when (k == 13) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> l-lcd(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| oth _ |> l-lstep(rows, i, n, src, mod, out: (out ++ "null,\"step\":"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-lcd {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lcd = l-escx(src, lo: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], n: @len(src), out: (out ++ "\""))
| e v |> l-lstep(rows, i: (i + 1), n, src, mod, out: (v ++ "\",\"step\":"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-lstep {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lstep = l-pkb(t: rows, i: (i * 6), n)
| se k when (k == 14) && ((rows[((i * 6) + 1)] == 1) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src))))) |> l-lsxp(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| si k when (k == 14) && (((rows[((i * 6) + 1)] == 2) || (rows[((i * 6) + 1)] == 3)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src))))) |> l-lsiv(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| ct k when (k == 15) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> l-lctor(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| oth _ |> l-lconts(rows, i, n, src, mod, out: (out ++ "{\"type\":\"terminal\"},\"continuations\":["), f0, f1, fln, k4, pr0, pr1, q0, q1, dp: (dp + 1), af: 0, cs: 0, hn)

tor l-lsxp {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lsxp = l-escx(src, lo: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], n: @len(src), out: (out ++ "{\"type\":\"produce\",\"plain_value\":\""))
| e v |> l-lconts(rows, i: (i + 1), n, src, mod, out: (v ++ "\"},\"continuations\":["), f0, f1, fln, k4, pr0, pr1, q0, q1, dp: (dp + 1), af: 0, cs: 0, hn)

tor l-lsiv {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lsiv = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ ("{\"type\":\"invocation\",\"invocation\":{\"event\":[" ++ (if((rows[((i * 6) + 1)] == 3)) "\"@" else "\""))))
| e v |> l-linv(rows, i: (i + 1), n, src, mod, out: (v ++ "\"],\"args\":["), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh: 1, as: 0)

tor l-lctor {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lctor = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ "{\"type\":\"branch_constructor\",\"branch_constructor\":{\"branch_name\":\""))
| e v |> l-lctor1(rows, i, n, src, mod, out: (v ++ "\",\"fields\":[],\"plain_value\":"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-lctor1 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lctor1 = l-lxt(src, i: rows[((i * 6) + 4)], hi: rows[((i * 6) + 5)], d: 0, ins: 0)
| x xt |> l-lctor2(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, xt)

tor l-lctor2 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, xt: i64} -> string
l-lctor2 = l-ltma(src, i: rows[((i * 6) + 4)], hi: xt)
| a a |> l-lctor3(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, xt, a)

tor l-lctor3 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, xt: i64, a: i64} -> string
l-lctor3 = l-ltmb(src, lo: a, j: (xt - 1), n: @len(src))
| b b |> l-lctor4(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, xt, a, b)

tor l-lctor4 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, xt: i64, a: i64, b: i64} -> string
l-lctor4 = l-pkb(t: src, i: a, n: @len(src))
| has _ when a < b |> l-lctor5(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, a, b)
| non _ when (a >= b) && (rows[((i * 6) + 4)] >= xt) |> l-lconts(rows, i: (i + 1), n, src, mod, out: (out ++ "null,\"has_expressions\":false,\"is_bare_return\":false}},\"continuations\":["), f0, f1, fln, k4, pr0, pr1, q0, q1, dp: (dp + 1), af: 0, cs: 0, hn)

tor l-lctor5 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, a: i64, b: i64} -> string
l-lctor5 = l-escl(src, i: a, hi: b, out: (out ++ "\""))
| v e |> l-lconts(rows, i: (i + 1), n, src, mod, out: (e ++ "\",\"has_expressions\":true,\"is_bare_return\":false}},\"continuations\":["), f0, f1, fln, k4, pr0, pr1, q0, q1, dp: (dp + 1), af: 0, cs: 0, hn)

tor l-lconts {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lconts = l-pkb(t: rows, i: (i * 6), n)
| cn k when (k == 11) && (((q0 < 0) && (hn == 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src))))) |> l-larmc(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| st k when (k == 14) && (((rows[((i * 6) + 1)] == 2) || (rows[((i * 6) + 1)] == 3)) && ((cs == 1) || (((dp == 1) && (af == 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src))))))) |> l-llink(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| oth _ |> l-litemc(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-larmc {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-larmc = l-pkb(t: rows, i: (i * 6), n)
| deep _ when dp > 1 |> l-larmd(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| shal _ when dp == 1 |> l-lcarmp(rows, i, n, src, mod, out: (out ++ (if((af == 1)) "," else "")), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-larmd {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-larmd = l-lcls(dp: (dp - 1), mod, fln, nmod: @len(mod), out)
| e v |> l-lcarmp(rows, i, n, src, mod, out: (v ++ ","), f0, f1, fln, k4, pr0, pr1, q0, q1, dp: 1, af, cs, hn)

tor l-lcarmp {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-lcarmp = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ "{\"branch\":\""))
| e v |> l-lbind(rows, i: (i + 1), n, src, mod, out: (v ++ "\",\"kind\":\"terminal\",\"is_catchall\":false,\"binding\":"), f0, f1, fln, k4, pr0, pr1, q0: (0 - 1), q1: (0 - 1), dp, af, cs: 0, hn)

tor l-llink {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-llink = l-pkb(t: src, i: q0, n: @len(src))
| pb _ when q0 >= 0 |> l-llinkb(rows, i, n, src, mod, out: (out ++ ((if((af == 1)) "," else "") ++ "{\"branch\":\"\",\"kind\":\"terminal\",\"is_catchall\":false,\"binding\":\"")), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| nb _ when q0 < 0 |> l-llinkn(rows, i, n, src, mod, out: (out ++ ((if((af == 1)) "," else "") ++ "{\"branch\":\"\",\"kind\":\"terminal\",\"is_catchall\":false,\"binding\":null")), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-llinkb {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-llinkb = l-escl(src, i: q0, hi: q1, out)
| e v |> l-llinkn(rows, i, n, src, mod, out: (v ++ "\""), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-llinkn {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-llinkn = l-pkb(t: rows, i: (i * 6), n)
| go _ |> l-llinke(rows, i, n, src, mod, out: (out ++ (",\"binding_type\":\"branch_payload\",\"condition\":null,\"step\":{\"type\":\"invocation\",\"invocation\":{\"event\":[" ++ (if((rows[((i * 6) + 1)] == 3)) "\"@" else "\""))), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-llinke {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-llinke = l-escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out)
| e v |> l-linv(rows, i: (i + 1), n, src, mod, out: (v ++ "\"],\"args\":["), f0, f1, fln, k4, pr0, pr1, q0: (0 - 1), q1: (0 - 1), dp, af, cs, hn: if(((dp == 1) && (af == 0))) 1 else hn, wh: 1, as: 0)

tor l-litemc {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-litemc = l-pkb(t: rows, i: (i * 6), n)
| deep _ when dp > 1 |> l-litemd(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| shal _ when dp == 1 |> l-litemp(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-litemd {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-litemd = l-lcls(dp: (dp - 1), mod, fln, nmod: @len(mod), out)
| e v |> l-litemp(rows, i, n, src, mod, out: v, f0, f1, fln, k4, pr0, pr1, q0, q1, dp: 1, af, cs, hn)

tor l-litemp {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-litemp = l-pkb(t: src, i: pr0, n: @len(src))
| f4 _ when k4 == 1 |> l-liteml(rows, i, n, src, mod, out: (out ++ "],\"pre_label\":null,\"impl_of\":null"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| hp _ when (k4 == 0) && (pr0 >= 0) |> l-litem3p(rows, i, n, src, mod, out: (out ++ "],\"pre_label\":\""), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| np _ when (k4 == 0) && (pr0 < 0) |> l-litem3i(rows, i, n, src, mod, out: (out ++ "],\"pre_label\":null,\"impl_of\":[\""), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-litem3p {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-litem3p = l-escl(src, i: pr0, hi: pr1, out)
| e v |> l-litem3i(rows, i, n, src, mod, out: (v ++ "\",\"impl_of\":[\""), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-litem3i {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-litem3i = l-escl(src, i: f0, hi: f1, out)
| e v |> l-liteml(rows, i, n, src, mod, out: (v ++ "\"]"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor l-liteml {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
l-liteml = l-escl(src: mod, i: 0, hi: @len(mod), out: (out ++ ",\"location\":{\"file\":\""))
| e v |> l-ltop(rows, i, n, src, mod, out: (v ++ ("\",\"line\":" ++ (@intToString(fln) ++ ",\"col\":0}}}"))), p0: (0 - 1), p1: (0 - 1), q0)

tor l-ltop {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64, q0: i64} -> string
l-ltop = l-pkb(t: rows, i: (i * 6), n)
| fin _ when ((i * 6) >= n) && (q0 < 0) |> l-ltail(mod, nmod: @len(mod), out)
| ev k when ((k == 1) && (q0 < 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> l-levo(rows, i, n, src, mod, out, p0, p1)
| im k when (((k == 5) && (q0 < 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src))))) && ((rows[((i * 6) + 4)] >= 0) && ((rows[((i * 6) + 5)] >= rows[((i * 6) + 4)]) && (rows[((i * 6) + 5)] <= @len(src)))) |> l-limpl(rows, i, n, src, mod, out, p0, p1)
| lb k when (k == 6) && (((q0 < 0) && (p0 < 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src))))) |> l-ltop(rows, i: (i + 1), n, src, mod, out, p0: rows[((i * 6) + 2)], p1: rows[((i * 6) + 3)], q0)
| fw k when ((k == 7) && (q0 < 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> l-lflw(rows, i, n, src, mod, out, p0, p1)
| ip k when ((k == 16) && (q0 < 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> l-limp(rows, i, n, src, mod, out, p0, p1)

tor l-main {src: []const i64, rows: []const i64, mod: []const i64} -> string
l-main = l-escl(src: mod, i: 0, hi: @len(mod), out: "{\"module_annotations\":[],\"items\":[{\"import_decl\":{\"path\":\"std/compiler\",\"local_name\":\"std.compiler\",\"module\":\"")
| m e |> l-ltop(rows, i: 0, n: @len(rows), src, mod, out: (e ++ "\"}}"), p0: (0 - 1), p1: (0 - 1), q0: (0 - 1))

tor w-pkb {t: []const i64, i: i64, n: i64} -> i64
w-pkb -> (if(((i < 0) || (i >= n))) (0 - 1) else t[i])

tor w-wn0 {} -> i64
w-wn0 -> 0

tor w-wc2 {a: string, b: string} -> string
w-wc2 -> ((a ++ b))

tor w-wc3 {a: string, b: string, c: string} -> string
w-wc3 -> ((a ++ (b ++ c)))

tor w-wc5 {a: string, b: string, c: string, d: string, e: string} -> string
w-wc5 -> ((a ++ (b ++ (c ++ (d ++ e)))))

tor w-wc7 {a: string, b: string, c: string, d: string, e: string, f: string, g: string} -> string
w-wc7 -> ((a ++ (b ++ (c ++ (d ++ (e ++ (f ++ g)))))))

tor w-wsk {src: []const i64, i: i64, hi: i64} -> i64
w-wsk = w-pkb(t: src, i, n: hi)
| _ c when (c == 32) || ((c == 9) || ((c == 10) || (c == 13))) |> w-wsk(src, i: (i + 1), hi)
| _ _ -> i

tor w-wtb {src: []const i64, lo: i64, j: i64, n: i64} -> i64
w-wtb = w-pkb(t: src, i: j, n)
| _ c when (j >= lo) && ((c == 32) || ((c == 9) || ((c == 10) || (c == 13)))) |> w-wtb(src, lo, j: (j - 1), n)
| _ _ -> ((j + 1))

tor w-wid {c: i64} -> i64
w-wid -> (if(((((c >= 97) && (c <= 122)) || ((c >= 65) && (c <= 90))) || (((c >= 48) && (c <= 57)) || (c == 95)))) 1 else 0)

tor w-wpe {c: i64} -> i64
w-wpe = w-wid(c)
| _ r when r == 1 -> 1
| _ _ -> (if((((c == 41) || (c == 93)) || ((c == 125) || (c == 34)))) 1 else 0)

tor w-wnat {nsp: []const i64, nn: i64, i: i64, p: i64} -> i64
w-wnat = w-pkb(t: nsp, i: (2 * i), n: (2 * nn))
| _ v when (v == p) && (i < nn) -> i
| _ _ when i < nn |> w-wnat(nsp, nn, i: (i + 1), p)
| _ _ -> ((0 - 1))

tor w-wpix {nsp: []const i64, nn: i64, p: i64} -> i64
w-wpix = w-pkb(t: nsp, i: p, n: (@len(nsp) - (5 * nn)))
| _ k -> k

tor w-wnm {names: []const string, nsp: []const i64, nn: i64, p: i64} -> string
w-wnm = w-wpix(nsp, nn, p)
| _ k when k >= 0 -> (names[k])
| _ _ -> "(bad names)"

tor w-wne {nsp: []const i64, nn: i64, p: i64} -> i64
w-wne = w-wpix(nsp, nn, p)
| _ k when k >= 0 -> (nsp[(((@len(nsp) - (5 * nn)) + (2 * k)) + 1)])
| _ _ -> ((0 - 1))

tor w-wst {strs: []const string, ssp: []const i64, ns: i64, p: i64} -> string
w-wst = w-wnat(nsp: ssp, nn: ns, i: 0, p)
| _ k when k >= 0 -> (strs[k])
| _ _ -> "(bad strs)"

tor w-weq {src: []const i64, a: i64, b: i64, x: i64, y: i64} -> i64
w-weq = w-wn0()
| _ _ when (b - a) != (y - x) -> 0
| _ _ |> w-weql(src, a, b, x, y, i: 0)

tor w-weql {src: []const i64, a: i64, b: i64, x: i64, y: i64, i: i64} -> i64
w-weql = w-pkb(t: src, i: (a + i), n: b)
| _ c when c < 0 -> 1
| _ c when if(((x + i) < y)) (c != src[(x + i)]) else true -> 0
| _ _ |> w-weql(src, a, b, x, y, i: (i + 1))

tor w-wnv {src: []const i64, i: i64, hi: i64, v: i64} -> i64
w-wnv = w-pkb(t: src, i, n: hi)
| _ c when (c >= 48) && (c <= 57) |> w-wnv(src, i: (i + 1), hi, v: ((v * 10) + (c - 48)))
| _ _ -> v

tor w-wp10 {n: i64} -> i64
w-wp10 = w-wn0()
| _ _ when n <= 0 -> 1
| _ _ |> w-wp10m(n)

tor w-wp10m {n: i64} -> i64
w-wp10m = w-wp10(n: (n - 1))
| _ t -> ((t * 10))

tor w-wgcd {a: i64, b: i64} -> i64
w-wgcd = w-wn0()
| _ _ when b == 0 -> a
| _ _ |> w-wgcd(a: b, b: (a % b))

tor w-wpb {src: []const i64, lo: i64, i: i64} -> i64
w-wpb = w-pkb(t: src, i: (i - 1), n: i)
| _ _ when i <= lo -> 0
| _ c when (c == 32) || ((c == 9) || ((c == 10) || (c == 13))) |> w-wpb(src, lo, i: (i - 1))
| _ c -> c

tor w-wopa {src: []const i64, lo: i64, hi: i64, i: i64, d: i64, ins: i64} -> i64
w-wopa = w-wpb(src, lo, i)
| _ p when ((d == 0) && (ins == 0)) && (i < hi) |> w-wopb(src, i, hi, p)
| _ _ -> 0

tor w-wopb {src: []const i64, i: i64, hi: i64, p: i64} -> i64
w-wopb = w-pkb(t: src, i, n: hi)
| _ c when (c == 47) && if(((i + 1) < hi)) (src[(i + 1)] == 47) else false -> ((0 - 2))
| _ c when (c == 124) && if(((i + 1) < hi)) (src[(i + 1)] == 124) else false -> (((12 * 8) + 2))
| _ c when (c == 38) && if(((i + 1) < hi)) (src[(i + 1)] == 38) else false -> (((11 * 8) + 2))
| _ c when (c == 61) && if(((i + 1) < hi)) (src[(i + 1)] == 61) else false -> (((5 * 8) + 2))
| _ c when (c == 33) && if(((i + 1) < hi)) (src[(i + 1)] == 61) else false -> (((6 * 8) + 2))
| _ c when (c == 60) && if(((i + 1) < hi)) (src[(i + 1)] == 61) else false -> (((8 * 8) + 2))
| _ c when (c == 62) && if(((i + 1) < hi)) (src[(i + 1)] == 61) else false -> (((10 * 8) + 2))
| _ c when (c == 43) && if(((i + 1) < hi)) (src[(i + 1)] == 43) else false -> (((13 * 8) + 2))
| _ c when c == 60 -> (((7 * 8) + 1))
| _ c when c == 62 -> (((9 * 8) + 1))
| _ c when c == 42 -> (((2 * 8) + 1))
| _ c when c == 47 -> (((3 * 8) + 1))
| _ c when c == 37 -> (((4 * 8) + 1))
| _ c when c == 43 |> w-wope(src, i, hi, p, op: 0)
| _ c when c == 45 |> w-wops(src, i, hi, p)
| _ c when c == 111 |> w-wopo(src, i, hi, p)
| _ c when c == 97 |> w-wopd(src, i, hi, p)
| _ _ -> 0

tor w-wope {src: []const i64, i: i64, hi: i64, p: i64, op: i64} -> i64
w-wope = w-wpe(c: p)
| _ v when v == 1 -> (((op * 8) + 1))
| _ _ -> 0

tor w-wops {src: []const i64, i: i64, hi: i64, p: i64} -> i64
w-wops = w-pkb(t: src, i: (i + 1), n: hi)
| _ n when (((p >= 97) && (p <= 122)) || (((p >= 65) && (p <= 90)) || (((p >= 48) && (p <= 57)) || (p == 95)))) && ((((n >= 97) && (n <= 122)) || (((n >= 65) && (n <= 90)) || (((n >= 48) && (n <= 57)) || (n == 95)))) || (n == 45)) -> 0
| _ _ |> w-wope(src, i, hi, p, op: 1)

tor w-wopo {src: []const i64, i: i64, hi: i64, p: i64} -> i64
w-wopo = w-pkb(t: src, i: (i + 1), n: hi)
| _ n when n == 114 |> w-wopo2(src, i, hi, p)
| _ _ -> 0

tor w-wopo2 {src: []const i64, i: i64, hi: i64, p: i64} -> i64
w-wopo2 = w-wpe(c: p)
| _ v when v == 1 |> w-wopob(src, i, hi)
| _ _ -> 0

tor w-wopob {src: []const i64, i: i64, hi: i64} -> i64
w-wopob = w-pkb(t: src, i: (i + 2), n: hi)
| _ c when c < 0 -> (((12 * 8) + 2))
| _ c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || (((c >= 48) && (c <= 57)) || (c == 95))) -> 0
| _ c when (c == 45) && if(((i + 3) < hi)) (((src[(i + 3)] >= 97) && (src[(i + 3)] <= 122)) || (((src[(i + 3)] >= 65) && (src[(i + 3)] <= 90)) || (((src[(i + 3)] >= 48) && (src[(i + 3)] <= 57)) || ((src[(i + 3)] == 95) || (src[(i + 3)] == 45))))) else false -> 0
| _ _ -> (((12 * 8) + 2))

tor w-wopd {src: []const i64, i: i64, hi: i64, p: i64} -> i64
w-wopd = w-pkb(t: src, i: (i + 1), n: hi)
| _ n when (n == 110) && if(((i + 2) < hi)) (src[(i + 2)] == 100) else false |> w-wopd2(src, i, hi, p)
| _ _ -> 0

tor w-wopd2 {src: []const i64, i: i64, hi: i64, p: i64} -> i64
w-wopd2 = w-wpe(c: p)
| _ v when v == 1 |> w-wopdb(src, i, hi)
| _ _ -> 0

tor w-wopdb {src: []const i64, i: i64, hi: i64} -> i64
w-wopdb = w-pkb(t: src, i: (i + 3), n: hi)
| _ c when c < 0 -> (((11 * 8) + 3))
| _ c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || (((c >= 48) && (c <= 57)) || (c == 95))) -> 0
| _ c when (c == 45) && if(((i + 4) < hi)) (((src[(i + 4)] >= 97) && (src[(i + 4)] <= 122)) || (((src[(i + 4)] >= 65) && (src[(i + 4)] <= 90)) || (((src[(i + 4)] >= 48) && (src[(i + 4)] <= 57)) || ((src[(i + 4)] == 95) || (src[(i + 4)] == 45))))) else false -> 0
| _ _ -> (((11 * 8) + 3))

tor w-wprc {o: i64} -> i64
w-wprc -> (if((o == 12)) 1 else if((o == 11)) 2 else if(((o == 5) || (o == 6))) 3 else if(((o >= 7) && (o <= 10))) 4 else if((o == 13)) 5 else if(((o == 0) || (o == 1))) 6 else 7)

tor w-wopn {o: i64} -> string
w-wopn -> (if((o == 0)) "add" else if((o == 1)) "sub" else if((o == 2)) "mul" else if((o == 3)) "div" else if((o == 4)) "mod" else if((o == 5)) "eq" else if((o == 6)) "ne" else if((o == 7)) "lt" else if((o == 8)) "le" else if((o == 9)) "gt" else if((o == 10)) "ge" else if((o == 11)) "and" else if((o == 12)) "or" else "concat")

tor w-wfp {src: []const i64, lo: i64, hi: i64, i: i64, d: i64, ins: i64, last: i64, prec: i64} -> i64
w-wfp = w-wopa(src, lo, hi, i, d, ins)
| _ o when (i >= hi) || (o == (0 - 2)) -> last
| _ o when o != 0 |> w-wfp1(src, lo, hi, i, d, ins, last, prec, o)
| _ _ |> w-wfpn(src, lo, hi, i, d, ins, last, prec)

tor w-wfp1 {src: []const i64, lo: i64, hi: i64, i: i64, d: i64, ins: i64, last: i64, prec: i64, o: i64} -> i64
w-wfp1 = w-wprc(o: (o / 8))
| _ q when q == prec |> w-wfpn(src, lo, hi, i, d, ins, last: i, prec)
| _ _ |> w-wfpn(src, lo, hi, i, d, ins, last, prec)

tor w-wfpn {src: []const i64, lo: i64, hi: i64, i: i64, d: i64, ins: i64, last: i64, prec: i64} -> i64
w-wfpn = w-wfp(src, lo, hi, i: (i + (if(((ins == 1) && (src[i] == 92))) 2 else 1)), d: if(((ins == 0) && (((src[i] == 40) || (src[i] == 91)) || (src[i] == 123)))) (d + 1) else if(((ins == 0) && (((src[i] == 41) || (src[i] == 93)) || (src[i] == 125)))) (d - 1) else d, ins: if(((src[i] == 34) && (ins == 0))) 1 else if(((src[i] == 34) && (ins == 1))) 0 else ins, last, prec)
| _ r -> r

tor w-wmb {src: []const i64, i: i64, hi: i64} -> i64
w-wmb = w-pkb(t: src, i: (i + 1), n: hi)
| _ _ |> w-wmb1(src, i: (i + 1), hi, d: 1, ins: 0)

tor w-wmb1 {src: []const i64, i: i64, hi: i64, d: i64, ins: i64} -> i64
w-wmb1 = w-pkb(t: src, i, n: hi)
| _ c when c < 0 -> hi
| _ c when (ins == 0) && (c == 34) |> w-wmb1(src, i: (i + 1), hi, d, ins: 1)
| _ c when (ins == 1) && (c == 34) |> w-wmb1(src, i: (i + 1), hi, d, ins: 0)
| _ c when (ins == 1) && (c == 92) |> w-wmb1(src, i: (i + 2), hi, d, ins)
| _ c when (ins == 0) && (((c == 40) || (c == 91)) || (c == 123)) |> w-wmb1(src, i: (i + 1), hi, d: (d + 1), ins)
| _ c when (ins == 0) && (((c == 41) || (c == 93)) || (c == 125)) |> w-wmbx(src, i, hi, d)
| _ _ |> w-wmb1(src, i: (i + 1), hi, d, ins)

tor w-wmbx {src: []const i64, i: i64, hi: i64, d: i64} -> i64
w-wmbx = w-wn0()
| _ _ when (d - 1) == 0 -> i
| _ _ |> w-wmb1(src, i: (i + 1), hi, d: (d - 1), ins: 0)

tor w-wss {src: []const i64, i: i64, hi: i64} -> i64
w-wss = w-pkb(t: src, i: (i + 1), n: hi)
| _ c when c < 0 -> hi
| _ c when c == 34 -> ((i + 2))
| _ c when c == 92 |> w-wss(src, i: (i + 2), hi)
| _ _ |> w-wss(src, i: (i + 1), hi)

tor w-wen {src: []const i64, i: i64, hi: i64} -> i64
w-wen = w-pkb(t: src, i, n: hi)
| _ c when (c >= 48) && (c <= 57) |> w-wen(src, i: (i + 1), hi)
| _ c when (c == 46) && if(((i + 1) < hi)) ((src[(i + 1)] >= 48) && (src[(i + 1)] <= 57)) else false |> w-wen(src, i: (i + 1), hi)
| _ _ -> i

tor w-wcmx {src: []const i64, i: i64, hi: i64, d: i64, ins: i64, w: i64} -> i64
w-wcmx = w-pkb(t: src, i, n: hi)
| _ c when c < 0 -> i
| _ c when (d == 0) && ((ins == 0) && (c == w)) -> i
| _ c when (ins == 0) && (c == 34) |> w-wcmx(src, i: (i + 1), hi, d, ins: 1, w)
| _ c when (ins == 1) && (c == 34) |> w-wcmx(src, i: (i + 1), hi, d, ins: 0, w)
| _ c when (ins == 1) && (c == 92) |> w-wcmx(src, i: (i + 2), hi, d, ins, w)
| _ c when (ins == 0) && (((c == 40) || (c == 91)) || (c == 123)) |> w-wcmx(src, i: (i + 1), hi, d: (d + 1), ins, w)
| _ c when (ins == 0) && (((c == 41) || (c == 93)) || (c == 125)) |> w-wcmx(src, i: (i + 1), hi, d: (d - 1), ins, w)
| _ _ |> w-wcmx(src, i: (i + 1), hi, d, ins, w)

tor w-wfd {src: []const i64, i: i64, hi: i64, d: i64, ins: i64, last: i64} -> i64
w-wfd = w-pkb(t: src, i, n: hi)
| _ c when c < 0 -> last
| _ c when (d == 0) && ((ins == 0) && (c == 46)) |> w-wfd(src, i: (i + 1), hi, d, ins, last: i)
| _ c when (ins == 0) && (c == 34) |> w-wfd(src, i: (i + 1), hi, d, ins: 1, last)
| _ c when (ins == 1) && (c == 34) |> w-wfd(src, i: (i + 1), hi, d, ins: 0, last)
| _ c when (ins == 1) && (c == 92) |> w-wfd(src, i: (i + 2), hi, d, ins, last)
| _ c when (ins == 0) && (((c == 40) || (c == 91)) || (c == 123)) |> w-wfd(src, i: (i + 1), hi, d: (d + 1), ins, last)
| _ c when (ins == 0) && (((c == 41) || (c == 93)) || (c == 125)) |> w-wfd(src, i: (i + 1), hi, d: (d - 1), ins, last)
| _ _ |> w-wfd(src, i: (i + 1), hi, d, ins, last)

tor w-wty {nm: string} -> i64
w-wty -> (if(((((nm == "i64") || (nm == "i32")) || ((nm == "i16") || (nm == "i8"))) || ((((nm == "u64") || (nm == "u32")) || ((nm == "u16") || (nm == "u8"))) || (((nm == "f64") || (nm == "f32")) || ((nm == "bool") || (nm == "string")))))) 1 else if((((nm == "program") || (nm == "void")) || (nm == "unit"))) 1 else 0)

tor w-wbl {nm: string} -> i64
w-wbl -> (if(((((((nm == "as") || (nm == "intCast")) || ((nm == "truncate") || (nm == "divTrunc"))) || (((nm == "rem") || (nm == "mod")) || ((nm == "len") || (nm == "intToString")))) || ((((nm == "chars") || (nm == "charsToString")) || (nm == "charToString")) || (nm == "contains"))) || ((nm == "push") || (nm == "set")))) 1 else 0)

tor w-wev {lv: i64, src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wev = w-wfp(src, lo, hi, i: lo, d: 0, ins: 0, last: (0 - 1), prec: lv)
| _ t when t >= 0 |> w-wspl(lv, src, lo, hi, t, names, nsp, nn, strs, ssp, ns)
| _ _ |> w-wenx(lv, src, lo, hi, names, nsp, nn, strs, ssp, ns)

tor w-wenx {lv: i64, src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wenx = w-wn0()
| _ _ when lv < 7 |> w-wev(lv: (lv + 1), src, lo, hi, names, nsp, nn, strs, ssp, ns)
| _ _ |> w-weu(src, lo, hi, names, nsp, nn, strs, ssp, ns)

tor w-wspl {lv: i64, src: []const i64, lo: i64, hi: i64, t: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wspl = w-wopa(src, lo, hi, i: t, d: 0, ins: 0)
| _ o when o > 0 |> w-wev(lv, src, lo, hi: t, names, nsp, nn, strs, ssp, ns) : l |> w-wsplr(lv, src, lo: (t + (o - ((o / 8) * 8))), hi, op: (o / 8), l, names, nsp, nn, strs, ssp, ns)
| _ _ -> "(bad expr)"

tor w-wsplr {lv: i64, src: []const i64, lo: i64, hi: i64, op: i64, l: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wsplr = w-wev(lv, src, lo, hi, names, nsp, nn, strs, ssp, ns)
| _ r |> w-wc7(a: "(bin ", b: if((op == 0)) "add" else if((op == 1)) "sub" else if((op == 2)) "mul" else if((op == 3)) "div" else if((op == 4)) "mod" else if((op == 5)) "eq" else if((op == 6)) "ne" else if((op == 7)) "lt" else if((op == 8)) "le" else if((op == 9)) "gt" else if((op == 10)) "ge" else if((op == 11)) "and" else if((op == 12)) "or" else "concat", c: " ", d: l, e: " ", f: r, g: ")")

tor w-weu {src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-weu = w-wsk(src, i: lo, hi)
| _ i when if((i < hi)) (src[i] == 33) else false |> w-weu1(src, i, hi, op: 1, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 45) else false |> w-weu1(src, i, hi, op: 0, names, nsp, nn, strs, ssp, ns)
| _ _ |> w-wep(src, lo, hi, names, nsp, nn, strs, ssp, ns)

tor w-weu1 {src: []const i64, i: i64, hi: i64, op: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-weu1 = w-weu(src, lo: (i + 1), hi, names, nsp, nn, strs, ssp, ns)
| _ e -> (if((op == 1)) ("(un not " ++ (e ++ ")")) else ("(un neg " ++ (e ++ ")")))

tor w-wpm {src: []const i64, lo: i64, hi: i64, nsp: []const i64, nn: i64} -> i64
w-wpm = w-wsk(src, i: lo, hi)
| _ i when if((i < hi)) (src[i] == 40) else false |> w-wpmc(src, i, hi)
| _ i when if((i < hi)) (src[i] == 91) else false |> w-wpmc(src, i, hi)
| _ i when if((i < hi)) (src[i] == 123) else false |> w-wpmc(src, i, hi)
| _ i when if((i < hi)) (src[i] == 34) else false |> w-wss(src, i, hi)
| _ i when if((i < hi)) (src[i] == 64) else false -> hi
| _ i when if((i < hi)) ((src[i] >= 48) && (src[i] <= 57)) else false |> w-wen(src, i, hi)
| _ i when if((i < hi)) (((src[i] >= 97) && (src[i] <= 122)) || (((src[i] >= 65) && (src[i] <= 90)) || (src[i] == 95))) else false |> w-wpmv(src, i, hi, nsp, nn)
| _ _ -> hi

tor w-wpmc {src: []const i64, i: i64, hi: i64} -> i64
w-wpmc = w-wmb(src, i, hi)
| _ m -> (if((m < hi)) (m + 1) else hi)

tor w-wpmv {src: []const i64, i: i64, hi: i64, nsp: []const i64, nn: i64} -> i64
w-wpmv = w-wne(nsp, nn, p: i)
| _ e |> w-wpmv1(src, i, e, hi)

tor w-wpmv1 {src: []const i64, i: i64, e: i64, hi: i64} -> i64
w-wpmv1 = w-wn0()
| _ _ when (e == (i + 2)) && if(((i + 1) < hi)) ((src[i] == 105) && (src[(i + 1)] == 102)) else false -> hi
| _ _ |> w-wpmv2(src, e, hi)

tor w-wpmv2 {src: []const i64, e: i64, hi: i64} -> i64
w-wpmv2 = w-wsk(src, i: e, hi)
| _ j when if((j < hi)) (src[j] == 40) else false |> w-wpmc(src, i: j, hi)
| _ _ -> e

tor w-wep {src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wep = w-wpm(src, lo, hi, nsp, nn)
| _ p |> w-wem(src, lo, hi: p, names, nsp, nn, strs, ssp, ns) : a |> w-wep1(src, i: p, hi, acc: a, names, nsp, nn, strs, ssp, ns)

tor w-wep1 {src: []const i64, i: i64, hi: i64, acc: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wep1 = w-wsk(src, i, hi)
| _ j when if((j < hi)) (src[j] == 46) else false |> w-wep1f(src, j, hi, acc, names, nsp, nn, strs, ssp, ns)
| _ j when if((j < hi)) (src[j] == 91) else false |> w-wep1i(src, j, hi, acc, names, nsp, nn, strs, ssp, ns)
| _ j when if((j < hi)) (src[j] == 40) else false -> "(bad expr-call)"
| _ j when if((j < hi)) ((src[j] == 32) || ((src[j] == 9) || ((src[j] == 10) || (src[j] == 13)))) else false |> w-wep1(src, i: (j + 1), hi, acc, names, nsp, nn, strs, ssp, ns)
| _ _ -> acc

tor w-wep1f {src: []const i64, j: i64, hi: i64, acc: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wep1f = w-wne(nsp, nn, p: (j + 1))
| _ e when e > (j + 1) |> w-wnm(names, nsp, nn, p: (j + 1)) : nm |> w-wep1(src, i: e, hi, acc: ("(field " ++ (acc ++ (" " ++ (nm ++ ")")))), names, nsp, nn, strs, ssp, ns)
| _ _ -> "(bad expr)"

tor w-wep1i {src: []const i64, j: i64, hi: i64, acc: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wep1i = w-wsk(src, i: (j + 1), hi)
| _ k |> w-wep1t(src, j, k, hi, acc, names, nsp, nn, strs, ssp, ns)

tor w-wep1t {src: []const i64, j: i64, k: i64, hi: i64, acc: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wep1t = w-wnm(names, nsp, nn, p: k)
| _ nm |> w-wty(nm) : t |> w-wep1u(src, j, k, hi, acc, t, names, nsp, nn, strs, ssp, ns)

tor w-wep1u {src: []const i64, j: i64, k: i64, hi: i64, acc: string, t: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wep1u = w-wne(nsp, nn, p: k)
| _ e when (t == 1) && (e > k) |> w-wep1v(src, j, e, hi, acc, names, nsp, nn, strs, ssp, ns)
| _ _ |> w-wmb(src, i: j, hi) : m |> w-wev(lv: 1, src, lo: (j + 1), hi: m, names, nsp, nn, strs, ssp, ns) : x |> w-wep1w(src, m, hi, acc, x, names, nsp, nn, strs, ssp, ns)

tor w-wep1v {src: []const i64, j: i64, e: i64, hi: i64, acc: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wep1v = w-wsk(src, i: e, hi)
| _ q when if((q < hi)) (src[q] == 93) else false |> w-wep1(src, i: (q + 1), hi, acc, names, nsp, nn, strs, ssp, ns)
| _ _ |> w-wmb(src, i: j, hi) : m |> w-wev(lv: 1, src, lo: (j + 1), hi: m, names, nsp, nn, strs, ssp, ns) : x |> w-wep1w(src, m, hi, acc, x, names, nsp, nn, strs, ssp, ns)

tor w-wep1w {src: []const i64, m: i64, hi: i64, acc: string, x: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wep1w = w-wc5(a: "(index ", b: acc, c: " ", d: x, e: ")")
| _ a |> w-wep1(src, i: (m + 1), hi, acc: a, names, nsp, nn, strs, ssp, ns)

tor w-wem {src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wem = w-wsk(src, i: lo, hi)
| _ i when if((i < hi)) (src[i] == 40) else false |> w-wemg(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 91) else false |> w-wema(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 123) else false |> w-wemc(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 64) else false |> w-wemb(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 34) else false |> w-wems(src, i, strs, ssp, ns)
| _ i when if((i < hi)) ((src[i] >= 48) && (src[i] <= 57)) else false |> w-wnum(src, lo: i, hi, names, nsp, nn, strs, ssp, ns) : x |> w-wc3(a: "(lit ", b: x, c: ")")
| _ i when if((i < hi)) (((src[i] >= 97) && (src[i] <= 122)) || (((src[i] >= 65) && (src[i] <= 90)) || (src[i] == 95))) else false |> w-wemv(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ _ -> "(bad expr)"

tor w-wems {src: []const i64, i: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wems = w-wst(strs, ssp, ns, p: i)
| _ s |> w-wc5(a: "(lit (str ", b: "\"", c: s, d: "\"", e: "))")

tor w-wemg {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wemg = w-wmb(src, i, hi)
| _ m |> w-wev(lv: 1, src, lo: (i + 1), hi: m, names, nsp, nn, strs, ssp, ns)

tor w-wema {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wema = w-wmb(src, i, hi)
| _ m |> w-weal(src, i: (i + 1), hi: m, out: "(lit (arr", names, nsp, nn, strs, ssp, ns) : t |> w-wc3(a: t, b: ")", c: ")")

tor w-weal {src: []const i64, i: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-weal = w-wsk(src, i, hi)
| _ j when j >= hi -> out
| _ j |> w-wcmx(src, i: j, hi, d: 0, ins: 0, w: 44) : c |> w-weal1(src, j, c, hi, out, names, nsp, nn, strs, ssp, ns)

tor w-weal1 {src: []const i64, j: i64, c: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-weal1 = w-wel(src, lo: j, hi: c, names, nsp, nn, strs, ssp, ns)
| _ x |> w-wc3(a: out, b: " ", c: x) : o |> w-weal(src, i: (c + 1), hi, out: o, names, nsp, nn, strs, ssp, ns)

tor w-wemc {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wemc = w-wmb(src, i, hi)
| _ m |> w-wecl(src, i: (i + 1), hi: m, out: "(lit (cell", names, nsp, nn, strs, ssp, ns) : t |> w-wc3(a: t, b: ")", c: ")")

tor w-wecl {src: []const i64, i: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wecl = w-wsk(src, i, hi)
| _ j when j >= hi -> out
| _ j |> w-wcmx(src, i: j, hi, d: 0, ins: 0, w: 58) : c |> w-wecl1(src, j, c, hi, out, names, nsp, nn, strs, ssp, ns)

tor w-wecl1 {src: []const i64, j: i64, c: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wecl1 = w-wcmx(src, i: (c + 1), hi, d: 0, ins: 0, w: 44)
| _ m |> w-wecl2(src, j, c, m, hi, out, names, nsp, nn, strs, ssp, ns)

tor w-wecl2 {src: []const i64, j: i64, c: i64, m: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wecl2 = w-wnm(names, nsp, nn, p: j)
| _ nm |> w-wel(src, lo: (c + 1), hi: m, names, nsp, nn, strs, ssp, ns) : x |> w-wecl3(src, m, hi, out, nm, x, names, nsp, nn, strs, ssp, ns)

tor w-wecl3 {src: []const i64, m: i64, hi: i64, out: string, nm: string, x: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wecl3 = w-wc5(a: out, b: " (", c: nm, d: " ", e: x)
| _ o |> w-wc3(a: o, b: ")", c: "") : p |> w-wecl(src, i: (m + 1), hi, out: p, names, nsp, nn, strs, ssp, ns)

tor w-wemb {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wemb = w-wnm(names, nsp, nn, p: (i + 1))
| _ nm |> w-wbl(nm) : b |> w-wemb1(src, i, hi, nm, b, names, nsp, nn, strs, ssp, ns)

tor w-wemb1 {src: []const i64, i: i64, hi: i64, nm: string, b: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wemb1 = w-wn0()
| _ _ when b == 0 -> "(bad builtin)"
| _ _ |> w-wne(nsp, nn, p: (i + 1)) : e |> w-wemb2(src, e, hi, nm, names, nsp, nn, strs, ssp, ns)

tor w-wemb2 {src: []const i64, e: i64, hi: i64, nm: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wemb2 = w-wsk(src, i: e, hi)
| _ j when if((j < hi)) (src[j] == 40) else false |> w-wmb(src, i: j, hi) : m |> w-wc3(a: "(builtin ", b: nm, c: "") : p |> w-webal(src, i: (j + 1), hi: m, out: p, names, nsp, nn, strs, ssp, ns) : t |> w-wc2(a: t, b: ")")
| _ _ -> "(bad builtin)"

tor w-webal {src: []const i64, i: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-webal = w-wsk(src, i, hi)
| _ j when j >= hi -> out
| _ j |> w-wcmx(src, i: j, hi, d: 0, ins: 0, w: 44) : v |> w-webal1(src, j, v, hi, out, names, nsp, nn, strs, ssp, ns)

tor w-webal1 {src: []const i64, j: i64, v: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-webal1 = w-wcmx(src, i: j, hi, d: 0, ins: 0, w: 58)
| _ c when c < v |> w-wc3(a: out, b: " ", c: "(bad builtin-arg)") : o |> w-webal(src, i: (v + 1), hi, out: o, names, nsp, nn, strs, ssp, ns)
| _ _ |> w-wev(lv: 1, src, lo: j, hi: v, names, nsp, nn, strs, ssp, ns) : x |> w-wc3(a: out, b: " ", c: x) : o |> w-webal(src, i: (v + 1), hi, out: o, names, nsp, nn, strs, ssp, ns)

tor w-wemv {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wemv = w-wnm(names, nsp, nn, p: i)
| _ nm when nm == "if" |> w-wemi(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ nm when nm == "true" -> "(lit (bool true))"
| _ nm when nm == "false" -> "(lit (bool false))"
| _ nm when ((nm == "else") || (nm == "when")) || ((nm == "or") || (nm == "and")) -> "(bad expr)"
| _ nm |> w-wemvd(src, i, hi, nm, names, nsp, nn, strs, ssp, ns)

tor w-wemvd {src: []const i64, i: i64, hi: i64, nm: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wemvd = w-wne(nsp, nn, p: i)
| _ e |> w-wsk(src, i: e, hi) : j |> w-wemve(src, j, hi, nm)

tor w-wemve {src: []const i64, j: i64, hi: i64, nm: string} -> string
w-wemve = w-wn0()
| _ _ when if((j < hi)) (src[j] == 40) else false -> "(bad expr-call)"
| _ _ |> w-wc3(a: "(var ", b: nm, c: ")")

tor w-wemi {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wemi = w-wne(nsp, nn, p: i)
| _ e |> w-wsk(src, i: e, hi) : j |> w-wemi1(src, j, hi, names, nsp, nn, strs, ssp, ns)

tor w-wemi1 {src: []const i64, j: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wemi1 = w-pkb(t: src, i: j, n: hi)
| _ c when c == 40 |> w-wmb(src, i: j, hi) : m |> w-wemi2(src, j, m, hi, names, nsp, nn, strs, ssp, ns)
| _ _ -> "(bad if)"

tor w-wemi2 {src: []const i64, j: i64, m: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wemi2 = w-wev(lv: 1, src, lo: (j + 1), hi: m, names, nsp, nn, strs, ssp, ns)
| _ c |> w-wfel(src, i: (m + 1), hi, d: 0, ins: 0, ifd: 0) : el |> w-wemi3(src, m, el, c, hi, names, nsp, nn, strs, ssp, ns)

tor w-wemi3 {src: []const i64, m: i64, el: i64, c: string, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wemi3 = w-wev(lv: 1, src, lo: (m + 1), hi: el, names, nsp, nn, strs, ssp, ns)
| _ t |> w-wev(lv: 1, src, lo: (el + 4), hi, names, nsp, nn, strs, ssp, ns) : fv |> w-wc7(a: "(cond ", b: c, c: " ", d: t, e: " ", f: fv, g: ")")

tor w-wtek {src: []const i64, i: i64, hi: i64, d: i64, ins: i64} -> i64
w-wtek = w-pkb(t: src, i, n: hi)
| _ c when c < 0 -> ((0 - 1))
| _ _ when (d != 0) || (ins != 0) -> 0
| _ c when c == 101 |> w-wtek1(src, i, hi)
| _ c when c == 105 |> w-wtek2(src, i, hi)
| _ _ -> 0

tor w-wtek1 {src: []const i64, i: i64, hi: i64} -> i64
w-wtek1 = w-wbd(src, pv: (i - 1), nx: (i + 4), hi)
| _ b when b == 0 -> 0
| _ _ |> w-wtek1b(src, i, hi)

tor w-wtek1b {src: []const i64, i: i64, hi: i64} -> i64
w-wtek1b = w-pkb(t: src, i: (i + 1), n: hi)
| _ c when (c == 108) && if(((i + 3) < hi)) ((src[(i + 2)] == 115) && (src[(i + 3)] == 101)) else false -> 1
| _ _ -> 0

tor w-wtek2 {src: []const i64, i: i64, hi: i64} -> i64
w-wtek2 = w-wbd(src, pv: (i - 1), nx: (i + 2), hi)
| _ b when b == 0 -> 0
| _ _ |> w-wtek2b(src, i, hi)

tor w-wtek2b {src: []const i64, i: i64, hi: i64} -> i64
w-wtek2b = w-pkb(t: src, i: (i + 1), n: hi)
| _ c when c == 102 -> 2
| _ _ -> 0

tor w-wbd {src: []const i64, pv: i64, nx: i64, hi: i64} -> i64
w-wbd = w-pkb(t: src, i: pv, n: hi)
| _ c when (((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || (((c >= 48) && (c <= 57)) || (c == 95)))) || (c == 45) -> 0
| _ _ |> w-wbd1(src, nx, hi)

tor w-wbd1 {src: []const i64, nx: i64, hi: i64} -> i64
w-wbd1 = w-pkb(t: src, i: nx, n: hi)
| _ c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || (((c >= 48) && (c <= 57)) || (c == 95))) -> 0
| _ c when (c == 45) && if(((nx + 1) < hi)) (((src[(nx + 1)] >= 97) && (src[(nx + 1)] <= 122)) || (((src[(nx + 1)] >= 65) && (src[(nx + 1)] <= 90)) || (((src[(nx + 1)] >= 48) && (src[(nx + 1)] <= 57)) || ((src[(nx + 1)] == 95) || (src[(nx + 1)] == 45))))) else false -> 0
| _ _ -> 1

tor w-wfel {src: []const i64, i: i64, hi: i64, d: i64, ins: i64, ifd: i64} -> i64
w-wfel = w-wtek(src, i, hi, d, ins)
| _ r when r < 0 -> hi
| _ r when (r == 1) && (ifd == 0) -> i
| _ r when r == 1 |> w-wfel(src, i: (i + 4), hi, d, ins, ifd: (ifd - 1))
| _ r when r == 2 |> w-wfel(src, i: (i + 2), hi, d, ins, ifd: (ifd + 1))
| _ _ |> w-wfeln(src, i, hi, d, ins, ifd)

tor w-wfeln {src: []const i64, i: i64, hi: i64, d: i64, ins: i64, ifd: i64} -> i64
w-wfeln = w-wfel(src, i: (i + (if(((ins == 1) && (src[i] == 92))) 2 else 1)), hi, d: if(((ins == 0) && (((src[i] == 40) || (src[i] == 91)) || (src[i] == 123)))) (d + 1) else if(((ins == 0) && (((src[i] == 41) || (src[i] == 93)) || (src[i] == 125)))) (d - 1) else d, ins: if(((src[i] == 34) && (ins == 0))) 1 else if(((src[i] == 34) && (ins == 1))) 0 else ins, ifd)
| _ r -> r

tor w-wnum {src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wnum = w-wen(src, i: lo, hi)
| _ e |> w-wfd(src, i: lo, hi: e, d: 0, ins: 0, last: (0 - 1)) : d |> w-wnum1(src, lo, e, d)

tor w-wnum1 {src: []const i64, lo: i64, e: i64, d: i64} -> string
w-wnum1 = w-wnv(src, i: lo, hi: e, v: 0)
| _ v when d < 0 |> w-wc3(a: "(int ", b: @intToString(v), c: ")")
| _ v |> w-wnum2(src, e, d, w: v)

tor w-wnum2 {src: []const i64, e: i64, d: i64, w: i64} -> string
w-wnum2 = w-wnv(src, i: (d + 1), hi: e, v: 0)
| _ f |> w-wp10(n: (e - (d + 1))) : dn |> w-wnum3(e, d, w, f, dn)

tor w-wnum3 {e: i64, d: i64, w: i64, f: i64, dn: i64} -> string
w-wnum3 = w-wgcd(a: f, b: dn)
| _ g when g > 0 |> w-wc5(a: "(float ", b: @intToString(((w * (dn / g)) + (f / g))), c: " ", d: @intToString((dn / g)), e: ")")
| _ _ -> "(bad float)"

tor w-wel {src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wel = w-wsk(src, i: lo, hi)
| _ i when if((i < hi)) (src[i] == 40) else false |> w-welg(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 91) else false |> w-wela(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 123) else false |> w-welc(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 34) else false |> w-wst(strs, ssp, ns, p: i) : s |> w-wc5(a: "(str ", b: "\"", c: s, d: "\"", e: ")")
| _ i when if((i < hi)) ((src[i] >= 48) && (src[i] <= 57)) else false |> w-wnum(src, lo: i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 116) else false |> w-wel1(src, i, hi, nm: "true", names, nsp, nn)
| _ i when if((i < hi)) (src[i] == 102) else false |> w-wel1(src, i, hi, nm: "false", names, nsp, nn)
| _ _ -> "(bad lit)"

tor w-wel1 {src: []const i64, i: i64, hi: i64, nm: string, names: []const string, nsp: []const i64, nn: i64} -> string
w-wel1 = w-wnm(names, nsp, nn, p: i)
| _ v when v == nm |> w-wc3(a: "(bool ", b: nm, c: ")")
| _ _ -> "(bad lit)"

tor w-welg {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-welg = w-wmb(src, i, hi)
| _ m |> w-wel(src, lo: (i + 1), hi: m, names, nsp, nn, strs, ssp, ns)

tor w-wela {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wela = w-wmb(src, i, hi)
| _ m |> w-well(src, i: (i + 1), hi: m, out: "(arr", names, nsp, nn, strs, ssp, ns) : t |> w-wc2(a: t, b: ")")

tor w-well {src: []const i64, i: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-well = w-wsk(src, i, hi)
| _ j when j >= hi -> out
| _ j |> w-wcmx(src, i: j, hi, d: 0, ins: 0, w: 44) : c |> w-well1(src, j, c, hi, out, names, nsp, nn, strs, ssp, ns)

tor w-well1 {src: []const i64, j: i64, c: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-well1 = w-wel(src, lo: j, hi: c, names, nsp, nn, strs, ssp, ns)
| _ x |> w-wc3(a: out, b: " ", c: x) : o |> w-well(src, i: (c + 1), hi, out: o, names, nsp, nn, strs, ssp, ns)

tor w-welc {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-welc = w-wmb(src, i, hi)
| _ m |> w-welcl(src, i: (i + 1), hi: m, out: "(cell", names, nsp, nn, strs, ssp, ns) : t |> w-wc2(a: t, b: ")")

tor w-welcl {src: []const i64, i: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-welcl = w-wsk(src, i, hi)
| _ j when j >= hi -> out
| _ j |> w-wcmx(src, i: j, hi, d: 0, ins: 0, w: 58) : c |> w-welcl1(src, j, c, hi, out, names, nsp, nn, strs, ssp, ns)

tor w-welcl1 {src: []const i64, j: i64, c: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-welcl1 = w-wcmx(src, i: (c + 1), hi, d: 0, ins: 0, w: 44)
| _ m |> w-welcl2(src, j, c, m, hi, out, names, nsp, nn, strs, ssp, ns)

tor w-welcl2 {src: []const i64, j: i64, c: i64, m: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-welcl2 = w-wnm(names, nsp, nn, p: j)
| _ nm |> w-wel(src, lo: (c + 1), hi: m, names, nsp, nn, strs, ssp, ns) : x |> w-welcl3(src, m, hi, out, nm, x, names, nsp, nn, strs, ssp, ns)

tor w-welcl3 {src: []const i64, m: i64, hi: i64, out: string, nm: string, x: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-welcl3 = w-wc5(a: out, b: " (", c: nm, d: " ", e: x)
| _ o |> w-wc3(a: o, b: ")", c: "") : p |> w-welcl(src, i: (m + 1), hi, out: p, names, nsp, nn, strs, ssp, ns)

tor w-wrk {rows: []const i64, i: i64, nr: i64} -> i64
w-wrk = w-pkb(t: rows, i, n: (nr * 6))
| _ k -> k

tor w-wevf {nsp: []const i64, nn: i64, lo: i64} -> i64
w-wevf = w-wpix(nsp, nn, p: lo)
| _ k when k >= 0 -> (nsp[((@len(nsp) - (3 * nn)) + k)])
| _ _ -> ((0 - 1))

tor w-wdpe {nsp: []const i64, nn: i64, rows: []const i64, i: i64} -> i64
w-wdpe = w-wpix(nsp, nn, p: rows[(i + 2)])
| _ k when k >= 0 -> (if((nsp[((@len(nsp) - nn) + k)] > 1)) 1 else 0)
| _ _ -> 0

tor w-whi {nsp: []const i64, nn: i64, lo: i64} -> i64
w-whi = w-wpix(nsp, nn, p: lo)
| _ k when k >= 0 -> (nsp[((@len(nsp) - (2 * nn)) + k)])
| _ _ -> 0

tor w-wfdn {rows: []const i64, evi: i64, i: i64, nr: i64} -> i64
w-wfdn = w-pkb(t: rows, i: (evi + (i * 6)), n: (nr * 6))
| _ k when k != 2 -> i
| _ _ |> w-wfdn(rows, evi, i: (i + 1), nr)

tor w-wfdh {rows: []const i64, evi: i64, src: []const i64, lo: i64, hi: i64, i: i64, nr: i64} -> i64
w-wfdh = w-pkb(t: rows, i: (evi + (i * 6)), n: (nr * 6))
| _ k when k != 2 -> 0
| _ _ |> w-wfdh1(rows, evi, src, lo, hi, i, nr)

tor w-wfdh1 {rows: []const i64, evi: i64, src: []const i64, lo: i64, hi: i64, i: i64, nr: i64} -> i64
w-wfdh1 = w-weq(src, a: rows[((evi + (i * 6)) + 2)], b: rows[((evi + (i * 6)) + 3)], x: lo, y: hi)
| _ v when v == 1 -> 1
| _ _ |> w-wfdh(rows, evi, src, lo, hi, i: (i + 1), nr)

tor w-wbr0 {rows: []const i64, evi: i64, i: i64, nr: i64} -> i64
w-wbr0 = w-pkb(t: rows, i: (evi + (i * 6)), n: (nr * 6))
| _ k when (k == 2) || (k == 3) |> w-wbr0(rows, evi, i: (i + 1), nr)
| _ _ -> ((evi + (i * 6)))

tor w-wbrn {rows: []const i64, evi: i64, nr: i64} -> i64
w-wbrn = w-wbr0(rows, evi, i: 1, nr)
| _ b |> w-wbrn1(rows, b, i: 0, nr)

tor w-wbrn1 {rows: []const i64, b: i64, i: i64, nr: i64} -> i64
w-wbrn1 = w-pkb(t: rows, i: (b + (i * 6)), n: (nr * 6))
| _ k when k != 4 -> i
| _ _ |> w-wbrn1(rows, b, i: (i + 1), nr)

tor w-wbrh {rows: []const i64, evi: i64, src: []const i64, lo: i64, hi: i64, nr: i64} -> i64
w-wbrh = w-wbr0(rows, evi, i: 1, nr)
| _ b |> w-wbrh1(rows, b, src, lo, hi, i: 0, nr)

tor w-wbrh1 {rows: []const i64, b: i64, src: []const i64, lo: i64, hi: i64, i: i64, nr: i64} -> i64
w-wbrh1 = w-pkb(t: rows, i: (b + (i * 6)), n: (nr * 6))
| _ k when k != 4 -> 0
| _ _ |> w-wbrh2(rows, b, src, lo, hi, i, nr)

tor w-wbrh2 {rows: []const i64, b: i64, src: []const i64, lo: i64, hi: i64, i: i64, nr: i64} -> i64
w-wbrh2 = w-weq(src, a: rows[((b + (i * 6)) + 2)], b: rows[((b + (i * 6)) + 3)], x: lo, y: hi)
| _ v when v == 1 -> 1
| _ _ |> w-wbrh1(rows, b, src, lo, hi, i: (i + 1), nr)

tor w-wrp {k: i64} -> string
w-wrp = w-wn0()
| _ _ when k <= 0 -> ""
| _ _ |> w-wrp1(k)

tor w-wrp1 {k: i64} -> string
w-wrp1 = w-wrp(k: (k - 1))
| _ t |> w-wc2(a: ")", b: t)

tor w-wclo {inf: i64, iopen: i64, curk: i64, dep: i64} -> string
w-wclo = w-wn0()
| _ _ when inf == 0 -> ""
| _ _ |> w-wcloa(iopen, curk, dep)

tor w-wcloa {iopen: i64, curk: i64, dep: i64} -> string
w-wcloa = w-wrp(k: (iopen + (if((curk != 0)) (1 + (dep * 2)) else 0)))
| _ a |> w-wc3(a: if((curk == (0 - 1))) " (node terminal)" else "", b: a, c: "))")

tor w-wcls {iopen: i64, curk: i64, dep: i64} -> string
w-wcls = w-wn0()
| _ _ when curk == 0 |> w-wrp(k: iopen)
| _ _ when curk == (0 - 1) |> w-wrp(k: ((iopen + 1) + (dep * 2))) : p |> w-wc2(a: " (node terminal)", b: p)
| _ _ |> w-wrp(k: ((iopen + 1) + (dep * 2)))

tor w-wex {src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
w-wex = w-wtb(src, lo, j: (hi - 1), n: hi)
| _ b |> w-wsk(src, i: lo, hi: b) : a |> w-wev(lv: 1, src, lo: a, hi: b, names, nsp, nn, strs, ssp, ns)

tor w-wpun {src: []const i64, lo: i64, hi: i64, nsp: []const i64, nn: i64} -> i64
w-wpun = w-wtb(src, lo, j: (hi - 1), n: hi)
| _ b |> w-wsk(src, i: lo, hi: b) : a |> w-wpun1(src, a, b, nsp, nn)

tor w-wpun1 {src: []const i64, a: i64, b: i64, nsp: []const i64, nn: i64} -> i64
w-wpun1 = w-wne(nsp, nn, p: a)
| _ e when e == b -> a
| _ _ |> w-wfd(src, i: a, hi: b, d: 0, ins: 0, last: (0 - 1)) : f |> w-wpun2(src, b, f, nsp, nn)

tor w-wpun2 {src: []const i64, b: i64, f: i64, nsp: []const i64, nn: i64} -> i64
w-wpun2 = w-wne(nsp, nn, p: (f + 1))
| _ e when (f >= 0) && (e == b) |> w-wpun3(src, f)
| _ _ -> ((0 - 1))

tor w-wpun3 {src: []const i64, f: i64} -> i64
w-wpun3 = w-pkb(t: src, i: (f - 1), n: @len(src))
| _ c |> w-wpun3b(c, f)

tor w-wpun3b {c: i64, f: i64} -> i64
w-wpun3b = w-wpe(c)
| _ _ -> ((f + 1))

tor w-wdk {nsp: []const i64, nn: i64, ltk: i64, ltl: i64, lth: i64, htl: i64, hth: i64, fevi: i64} -> i64
w-wdk = w-wn0()
| _ _ when (ltk == 1) || (ltk == 2) |> w-wevf(nsp, nn, lo: ltl)
| _ _ when ltk == 3 |> w-wevf(nsp, nn, lo: htl)
| _ _ -> fevi

tor w-warg {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64, ltk: i64, ltl: i64, lth: i64, htl: i64, hth: i64, argi: i64, fevi: i64} -> string
w-warg = w-wex(src, lo: rows[(i + 4)], hi: rows[(i + 5)], names, nsp, nn, strs, ssp, ns)
| _ e |> w-wdk(nsp, nn, ltk, ltl, lth, htl, hth, fevi) : d |> w-warg1(rows, nr, src, names, nsp, nn, i, d, argi, e)

tor w-warg1 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, d: i64, argi: i64, e: string} -> string
w-warg1 = w-wn0()
| _ _ when rows[(i + 2)] > 0 |> w-warg2(rows, nr, src, names, nsp, nn, i, d, e)
| _ _ |> w-wpun(src, lo: rows[(i + 4)], hi: rows[(i + 5)], nsp, nn) : p |> w-warg3(rows, nr, src, names, nsp, nn, i, d, argi, e, p)

tor w-warg2 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, d: i64, e: string} -> string
w-warg2 = w-wfdh(rows, evi: d, src, lo: rows[(i + 2)], hi: rows[(i + 3)], i: 1, nr)
| _ h when (d < 0) || (h == 1) |> w-warg2a(rows, names, nsp, nn, i, e)
| _ _ -> "(bad decl-param)"

tor w-warg2a {rows: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, e: string} -> string
w-warg2a = w-wnm(names, nsp, nn, p: rows[(i + 2)])
| _ nm |> w-wc5(a: " (", b: nm, c: " ", d: e, e: ")")

tor w-warg3 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, d: i64, argi: i64, e: string, p: i64} -> string
w-warg3 = w-wne(nsp, nn, p)
| _ pe |> w-warg3a(rows, nr, src, names, nsp, nn, i, d, argi, e, p, pe)

tor w-warg3a {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, d: i64, argi: i64, e: string, p: i64, pe: i64} -> string
w-warg3a = w-wfdh(rows, evi: d, src, lo: p, hi: pe, i: 1, nr)
| _ h when (p >= 0) && ((d < 0) || (h == 1)) |> w-wnm(names, nsp, nn, p) : nm |> w-wc5(a: " (", b: nm, c: " ", d: e, e: ")")
| _ _ |> w-warg4(rows, nr, src, names, nsp, nn, d, argi, e)

tor w-warg4 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, d: i64, argi: i64, e: string} -> string
w-warg4 = w-wn0()
| _ _ when d >= 0 |> w-warg5(rows, nr, src, names, nsp, nn, d, argi, e)
| _ _ -> "(bad arg-name)"

tor w-warg5 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, d: i64, argi: i64, e: string} -> string
w-warg5 = w-wfdn(rows, evi: d, i: 1, nr)
| _ n when (argi + 1) < n |> w-wnm(names, nsp, nn, p: rows[((d + ((argi + 1) * 6)) + 2)]) : nm |> w-wc5(a: " (", b: nm, c: " ", d: e, e: ")")
| _ _ -> "(bad arg-name)"

tor w-whev {nsp: []const i64, nn: i64, rows: []const i64, i: i64} -> string
w-whev = w-wdpe(nsp, nn, rows, i)
| _ d -> (if((d == 1)) " (bad dup-tor)" else "")

tor w-whim {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64} -> string
w-whim = w-wex(src, lo: rows[(i + 4)], hi: rows[(i + 5)], names, nsp, nn, strs, ssp, ns)
| _ e |> w-wnm(names, nsp, nn, p: rows[(i + 2)]) : nm |> w-wc7(a: " (def ", b: nm, c: " (bare ", d: e, e: "))", f: "", g: "")

tor w-whfw {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, plbl: i64} -> string
w-whfw = w-wnm(names, nsp, nn, p: rows[(i + 2)])
| _ nm |> w-whfw1(names, nsp, nn, plbl, nm)

tor w-whfw1 {names: []const string, nsp: []const i64, nn: i64, plbl: i64, nm: string} -> string
w-whfw1 = w-wn0()
| _ _ when plbl >= 0 |> w-wnm(names, nsp, nn, p: plbl) : lb |> w-wc5(a: " (def ", b: nm, c: " (subflow", d: (" (label " ++ (lb ++ ")")), e: "")
| _ _ |> w-wc5(a: " (def ", b: nm, c: " (subflow", d: "", e: "")

tor w-whca {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64} -> string
w-whca = w-wnm(names, nsp, nn, p: rows[(i + 2)])
| _ nm |> w-wc3(a: " (head ", b: nm, c: "")

tor w-whco {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, fevi: i64} -> string
w-whco = w-wbrh(rows, evi: fevi, src, lo: rows[(i + 2)], hi: rows[(i + 3)], nr)
| _ b |> w-wbrn(rows, evi: fevi, nr) : n |> w-whco1(rows, names, nsp, nn, i, fevi, b, n)

tor w-whco1 {rows: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, fevi: i64, b: i64, n: i64} -> string
w-whco1 = w-wnm(names, nsp, nn, p: rows[(i + 2)])
| _ nm -> (if((((fevi >= 0) && (n > 0)) && (b == 0))) " (bad decl-branch)" else (" (arm (tag " ++ (nm ++ ")")))

tor w-whbi {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64} -> string
w-whbi = w-wnm(names, nsp, nn, p: rows[(i + 2)])
| _ nm |> w-wc3(a: " (bind ", b: nm, c: ")")

tor w-whcn {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64} -> string
w-whcn = w-wex(src, lo: rows[(i + 2)], hi: rows[(i + 3)], names, nsp, nn, strs, ssp, ns)
| _ e |> w-wc3(a: " (when ", b: e, c: ")")

tor w-whct {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64, fevi: i64, nr: i64} -> string
w-whct = w-wbrh(rows, evi: fevi, src, lo: rows[(i + 2)], hi: rows[(i + 3)], nr)
| _ b |> w-whct1(rows, src, names, nsp, nn, strs, ssp, ns, i, fevi, b)

tor w-whct1 {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64, fevi: i64, b: i64} -> string
w-whct1 = w-wnm(names, nsp, nn, p: rows[(i + 2)])
| _ _ when (fevi >= 0) && (b == 0) -> "(bad ctor-branch)"
| _ nm |> w-whct2(rows, src, names, nsp, nn, strs, ssp, ns, i, nm)

tor w-whct2 {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64, nm: string} -> string
w-whct2 = w-wtb(src, lo: rows[(i + 4)], j: (rows[(i + 5)] - 1), n: rows[(i + 5)])
| _ be when rows[(i + 4)] < be |> w-wex(src, lo: rows[(i + 4)], hi: be, names, nsp, nn, strs, ssp, ns) : x |> w-wc7(a: " (node (ctor ", b: nm, c: " ", d: x, e: "))", f: "", g: "")
| _ _ |> w-wc7(a: " (node (ctor ", b: nm, c: " ", d: "(lit (cell))", e: "))", f: "", g: "")

tor w-wsti {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, curk: i64, pend: i64, flbl: i64, flbh: i64, jump: i64} -> string
w-wsti = w-wnm(names, nsp, nn, p: rows[(i + 2)])
| _ nm |> w-wsti1(rows, src, names, nsp, nn, i, curk, pend, flbl, flbh, jump, nm)

tor w-wsti1 {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, curk: i64, pend: i64, flbl: i64, flbh: i64, jump: i64, nm: string} -> string
w-wsti1 = w-weq(src, a: flbl, b: flbh, x: rows[(i + 2)], y: rows[(i + 3)])
| _ j when (jump == 1) && (j == 0) -> "(bad jump-label)"
| _ _ |> w-wsti2(curk, pend, jump, nm, names, nsp, nn)

tor w-wsti2 {curk: i64, pend: i64, jump: i64, nm: string, names: []const string, nsp: []const i64, nn: i64} -> string
w-wsti2 = w-wn0()
| _ _ when pend >= 0 |> w-wnm(names, nsp, nn, p: pend) : b |> w-wsti3(curk, pend, jump, nm, b)
| _ _ |> w-wsti3(curk, pend, jump, nm, b: "")

tor w-wsti3 {curk: i64, pend: i64, jump: i64, nm: string, b: string} -> string
w-wsti3 = w-wn0()
| _ _ when (curk == 0) && (pend >= 0) -> ((" (arm (tag _chain) (bind " ++ (b ++ (") (node (" ++ ((if((jump == 1)) "jump " else "invoke ") ++ nm)))))
| _ _ when curk == 0 -> ((" (arm (tag _chain) (node (" ++ ((if((jump == 1)) "jump " else "invoke ") ++ nm)))
| _ _ when ((curk == 3) || (curk == 4)) && (pend >= 0) -> ((")) (conts (arm (tag _chain) (bind " ++ (b ++ (") (node (" ++ ((if((jump == 1)) "jump " else "invoke ") ++ nm)))))
| _ _ when (curk == 3) || (curk == 4) -> ((")) (conts (arm (tag _chain) (node (" ++ ((if((jump == 1)) "jump " else "invoke ") ++ nm)))
| _ _ -> ((" (node (" ++ ((if((jump == 1)) "jump " else "invoke ") ++ nm)))

tor w-wfin {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, out: string, inf: i64, iopen: i64, curk: i64, dep: i64, pend: i64} -> string
w-wfin = w-wn0()
| _ _ when pend >= 0 -> ((out ++ "(bad pend)"))
| _ _ |> w-wclo(inf, iopen, curk, dep) : c |> w-wfin1(rows, nr, src, names, nsp, nn, out, c)

tor w-wfin1 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, out: string, c: string} -> string
w-wfin1 = w-wth(rows, nr, src, names, nsp, nn, i: 0, out: (out ++ c))
| _ t |> w-wc2(a: t, b: ")")

tor w-wth {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, out: string} -> string
w-wth = w-wrk(rows, i, nr)
| _ _ when i >= (nr * 6) -> out
| _ k when k == 1 |> w-wthi(rows, nr, src, names, nsp, nn, i, out)
| _ _ |> w-wth(rows, nr, src, names, nsp, nn, i: (i + 6), out)

tor w-wthi {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, out: string} -> string
w-wthi = w-whi(nsp, nn, lo: rows[(i + 2)])
| _ h |> w-wnm(names, nsp, nn, p: rows[(i + 2)]) : nm |> w-wthi1(rows, nr, src, names, nsp, nn, i, out, h, nm)

tor w-wthi1 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, out: string, h: i64, nm: string} -> string
w-wthi1 = w-wc5(a: out, b: if((h == 1)) "" else " (def ", c: if((h == 1)) "" else nm, d: if((h == 1)) "" else " thunk)", e: "")
| _ o |> w-wth(rows, nr, src, names, nsp, nn, i: (i + 6), out: o)

tor w-w-wk {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64, out: string, dead: i64, inev: i64, inf: i64, iopen: i64, ltk: i64, ltl: i64, lth: i64, htl: i64, hth: i64, argi: i64, curk: i64, ctk: i64, dep: i64, pend: i64, plbl: i64, ple: i64, flbl: i64, flbh: i64, fevi: i64, ano: i64} -> string
w-w-wk = w-wrk(rows, i, nr)
| _ _ when i >= (nr * 6) |> w-wfin(rows, nr, src, names, nsp, nn, out, inf, iopen, curk, dep, pend)
| _ k when k == 17 |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad wire-bad)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 1) |> w-wclo(inf, iopen, curk, dep) : c |> w-whev(nsp, nn, rows, i) : t |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (c ++ t)), dead: if((t == " (bad dup-tor)")) 1 else dead, inev: 1, inf: 0, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: 0, ctk: 0, dep: 0, pend, plbl, ple, flbl, flbh, fevi: (0 - 1), ano: 0)
| _ k when (dead == 0) && (k == 2) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (if((inev == 0)) "(bad fld-out)" else "")), dead: if((inev == 0)) 1 else dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 3) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (if((inev == 0)) "(bad ret-out)" else "")), dead: if((inev == 0)) 1 else dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 4) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (if((inev == 0)) "(bad brd-out)" else "")), dead: if((inev == 0)) 1 else dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 5) |> w-wclo(inf, iopen, curk, dep) : c |> w-whim(rows, src, names, nsp, nn, strs, ssp, ns, i) : t |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (c ++ t)), dead, inev: 0, inf: 0, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: 0, ctk: 0, dep: 0, pend, plbl, ple, flbl, flbh, fevi: (0 - 1), ano: 0)
| _ k when (dead == 0) && (k == 6) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out, dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl: rows[(i + 2)], ple: rows[(i + 3)], flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 7)) && (pend >= 0) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad pend)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 7) |> w-wclo(inf, iopen, curk, dep) : c |> w-whfw(rows, src, names, nsp, nn, i, plbl) : t |> w-wevf(nsp, nn, lo: rows[(i + 2)]) : f |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (c ++ t)), dead, inev: 0, inf: 1, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: 0, ctk: 0, dep: 0, pend: (0 - 1), plbl: (0 - 1), ple: (0 - 1), flbl: plbl, flbh: ple, fevi: f, ano: 0)
| _ k when ((dead == 0) && (k == 8)) && ((inf == 0) || (ltk != 0)) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad head)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 8) |> w-whca(rows, src, names, nsp, nn, i) : t |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead, inev, inf, iopen: 1, ltk: 1, ltl: rows[(i + 2)], lth: rows[(i + 3)], htl: rows[(i + 2)], hth: rows[(i + 3)], argi: 0, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 9)) && (iopen == 0) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad arg)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 9) |> w-warg(rows, nr, src, names, nsp, nn, strs, ssp, ns, i, ltk, ltl, lth, htl, hth, argi, fevi) : t |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi: (argi + 1), curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 10)) && (ltk == 0) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad rbind)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 10) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out, dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend: rows[(i + 2)], plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 11)) && (inf == 0) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad cont)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 11)) && (pend >= 0) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad pend)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 11)) && (ano == 1) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad chain-scope)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 11) |> w-wcls(iopen, curk, dep) : c |> w-wevf(nsp, nn, lo: htl) : d |> w-whco(rows, nr, src, names, nsp, nn, i, fevi: d) : t |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (c ++ t)), dead: if((t == " (bad decl-branch)")) 1 else dead, inev, inf, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: (0 - 1), ctk: 0, dep: 0, pend: (0 - 1), plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 12)) && (curk == 0) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad bind)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 12) |> w-whbi(rows, src, names, nsp, nn, i) : t |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 13)) && (curk == 0) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad cond)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 13) |> w-whcn(rows, src, names, nsp, nn, strs, ssp, ns, i) : t |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (((dead == 0) && (k == 14)) && (rows[(i + 1)] == 1)) && ((curk != (0 - 1)) || (inf == 0)) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad step-expr)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 14)) && (rows[(i + 1)] == 1) |> w-wex(src, lo: rows[(i + 2)], hi: rows[(i + 3)], names, nsp, nn, strs, ssp, ns) : e |> w-wc5(a: " (node (produce ", b: e, c: ")", d: ")", e: "") : t |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead, inev, inf, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: 1, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (((dead == 0) && (k == 14)) && (rows[(i + 1)] == 2)) && (((curk == 1) || (curk == 2)) || (curk == 5)) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad chain-after)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 14)) && (rows[(i + 1)] == 2) |> w-wsti(rows, src, names, nsp, nn, i, curk, pend, flbl, flbh, jump: 0) : t |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead: if((t == "(bad jump-label)")) 1 else dead, inev, inf, iopen: 2, ltk: 2, ltl: rows[(i + 2)], lth: rows[(i + 3)], htl, hth, argi: 0, curk: if((curk == 0)) 3 else if((curk == (0 - 1))) 3 else curk, ctk: 3, dep: if(((curk == 3) || (curk == 4))) (dep + 1) else dep, pend: (0 - 1), plbl, ple, flbl, flbh, fevi, ano: if((curk == 0)) 1 else ano)
| _ k when (((dead == 0) && (k == 14)) && (rows[(i + 1)] == 3)) && (((curk == 1) || (curk == 2)) || (curk == 5)) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad chain-after)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 14)) && (rows[(i + 1)] == 3) |> w-wsti(rows, src, names, nsp, nn, i, curk, pend, flbl, flbh, jump: 1) : t |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead: if((t == "(bad jump-label)")) 1 else dead, inev, inf, iopen: 2, ltk: 3, ltl: rows[(i + 2)], lth: rows[(i + 3)], htl, hth, argi: 0, curk: if((curk == 0)) 4 else if((curk == (0 - 1))) 4 else curk, ctk: 4, dep: if(((curk == 3) || (curk == 4))) (dep + 1) else dep, pend: (0 - 1), plbl, ple, flbl, flbh, fevi, ano: if((curk == 0)) 1 else ano)
| _ k when ((dead == 0) && (k == 15)) && ((curk != (0 - 1)) || (inf == 0)) |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad ctor)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 15) |> w-whct(rows, src, names, nsp, nn, strs, ssp, ns, i, fevi, nr) : t |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead: if((t == "(bad ctor-branch)")) 1 else dead, inev, inf, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: 2, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 16) |> w-wclo(inf, iopen, curk, dep) : c |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ c), dead, inev: 0, inf: 0, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: 0, ctk: 0, dep: 0, pend: (0 - 1), plbl, ple, flbl, flbh, fevi: (0 - 1), ano: 0)
| _ _ when dead == 1 |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out, dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ _ |> w-w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out, dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)

tor w-w-main {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, strs: []const string, ssp: []const i64} -> string
w-w-main = w-w-wk(rows, nr: (@len(rows) / 6), src, names, nsp, nn: @len(names), strs, ssp, ns: @len(strs), i: 0, out: "(graph", dead: 0, inev: 0, inf: 0, iopen: 0, ltk: 0, ltl: 0, lth: 0, htl: 0, hth: 0, argi: 0, curk: 0, ctk: 0, dep: 0, pend: (0 - 1), plbl: (0 - 1), ple: (0 - 1), flbl: (0 - 1), flbh: (0 - 1), fevi: (0 - 1), ano: 0)
| _ g -> g

tor w-main {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, strs: []const string, ssp: []const i64} -> string
w-main = w-w-main(rows, src, names, nsp, strs, ssp)
| _ r -> r
