// kchain.k — the composed lane as declared shape (generated)
// a-*=kast  l-*=klow  chain=wiring;  low-txt / wir /
// emt-txt are arm-less stubs — refusal names the leg.
tor unrealized {} -> string
unrealized -> "unrealized"

tor low-txt {rows: []const i64, src: []const i64} -> string
low-txt = unrealized()

tor wir {rows: []const i64, src: []const i64} -> string
wir = unrealized()

tor emt-txt {claim: []const i64} -> string
emt-txt = unrealized()

tor chain {src: []const i64} -> string
chain = a-main(chars: src)
| rows rows |> low-txt(rows, src) : _ |> wir(rows, src) : claim |> emt-txt(claim)

tor a-peek {chars: []const i64, i: i64, n: i64} -> i64
a-peek -> if((i >= n)) (0 - 1) else chars[i]

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
a-kwtor -> if(((e == (j + 3)) && ((chars[j] == 116) && ((chars[(j + 1)] == 111) && (chars[(j + 2)] == 114))))) 1 else 0

tor a-kwwhen {chars: []const i64, j: i64, e: i64, n: i64} -> i64
a-kwwhen -> if(((e == (j + 4)) && ((chars[j] == 119) && ((chars[(j + 1)] == 104) && ((chars[(j + 2)] == 101) && (chars[(j + 3)] == 110)))))) 1 else 0

tor a-kwimport {chars: []const i64, j: i64, e: i64, n: i64} -> i64
a-kwimport -> if(((e == (j + 6)) && ((chars[j] == 105) && ((chars[(j + 1)] == 109) && ((chars[(j + 2)] == 112) && ((chars[(j + 3)] == 111) && ((chars[(j + 4)] == 114) && (chars[(j + 5)] == 116)))))))) 1 else 0

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
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

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
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

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
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor a-flow-lbl {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
a-flow-lbl = a-ws(chars, i, n)
| go h |> a-flow-pre2(chars, i: h, n, out, j, ne)

tor a-flow-pre2 {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
a-flow-pre2 = a-peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : he |> a-call-open(chars, i: he, n, out: ((out ++ ("(flw " ++ (@intToString(j) ++ (" " ++ (@intToString(ne) ++ ") "))))) ++ ("(call " ++ (@intToString(i) ++ (" " ++ (@intToString(he) ++ ") "))))))
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor a-call-open {chars: []const i64, i: i64, n: i64, out: string} -> string
a-call-open = a-ws(chars, i, n)
| go a |> a-call-at(chars, i: a, n, out)

tor a-call-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-call-at = a-peek(chars, i, n)
| open c when c == 40 |> a-args(chars, i: (i + 1), n, out)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

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
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

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
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor a-rb-tail {chars: []const i64, i: i64, n: i64, out: string} -> string
a-rb-tail = a-hws(chars, i, n)
| go t |> a-rb-tail-at(chars, i: t, n, out)

tor a-rb-tail-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-rb-tail-at = a-peek(chars, i, n)
| step c when (c == 124) && (chars[(i + 1)] == 62) |> a-arm-step(chars, i: (i + 2), n, out)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

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
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

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
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

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
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor a-arm-ctor {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm-ctor = a-ws(chars, i, n)
| go w |> a-arm-ctor1(chars, i: w, n, out)

tor a-arm-ctor1 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-arm-ctor1 = a-peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : ce |> a-arm-ctor2(chars, i: ce, n, out, cj: i, ce)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

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
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor a-decl-brace {chars: []const i64, i: i64, n: i64, out: string} -> string
a-decl-brace = a-ws(chars, i, n)
| go b |> a-decl-brace2(chars, i: b, n, out)

tor a-decl-brace2 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-decl-brace2 = a-peek(chars, i, n)
| open c when c == 123 |> a-fields(chars, i: (i + 1), n, out)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor a-fields {chars: []const i64, i: i64, n: i64, out: string} -> string
a-fields = a-ws(chars, i, n)
| go f |> a-fields-at(chars, i: f, n, out)

tor a-fields-at {chars: []const i64, i: i64, n: i64, out: string} -> string
a-fields-at = a-peek(chars, i, n)
| close c when c == 125 |> a-decl-ret(chars, i: (i + 1), n, out)
| var c when c == 124 |> a-variant(chars, i: (i + 1), n, out)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : fe |> a-fld(chars, i, n, out, fe)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor a-fld {chars: []const i64, i: i64, fe: i64, n: i64, out: string} -> string
a-fld = a-ws(chars, i: fe, n)
| go c |> a-fld2(chars, i: c, n, out, fj: i, fe)

tor a-fld2 {chars: []const i64, i: i64, n: i64, fj: i64, fe: i64, out: string} -> string
a-fld2 = a-peek(chars, i, n)
| ty k when k == 58 |> a-ws(chars, i: (i + 1), n) : t0 |> a-fld3(chars, i: t0, n, out, fj, fe)
| bad k -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(k) ++ ") ")))))

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
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor a-variant {chars: []const i64, i: i64, n: i64, out: string} -> string
a-variant = a-ws(chars, i, n)
| go v |> a-variant1(chars, i: v, n, out)

tor a-variant1 {chars: []const i64, i: i64, n: i64, out: string} -> string
a-variant1 = a-peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> a-word(chars, i, n) : ve |> a-variant2(chars, i, n, out, ve)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

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
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

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
l-pkb -> if(((i < 0) || (i >= n))) (0 - 1) else t[i]

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
| dn _ -> (j + 1)

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
| dn _ -> (j + 1)

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
l-lhx -> if((d < 10)) @intToString(d) else if((d == 10)) "a" else if((d == 11)) "b" else if((d == 12)) "c" else if((d == 13)) "d" else if((d == 14)) "e" else "f"

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
| done e -> (e ++ "\",\"parts\":[]}")

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
