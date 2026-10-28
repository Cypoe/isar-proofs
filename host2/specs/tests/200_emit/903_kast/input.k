// kast.k — a koru-spelled surface parser → flat AST rows (generated)
// item-level grammar: import/tor/impl/flow + arm bars;
// names, types, exprs ride source spans — the authority's
// own ast keeps them as text too.  arg-less invoke
// refuses: `chars` unbound.
tor peek {chars: []const i64, i: i64, n: i64} -> i64
peek -> if((i >= n)) (0 - 1) else chars[i]

tor ws {chars: []const i64, i: i64, n: i64} -> i64
ws = peek(chars, i, n)
| ws c when (c == 32) || ((c == 9) || ((c == 10) || (c == 13))) |> ws(chars, i: (i + 1), n)
| cm c when (c == 47) && (chars[(i + 1)] == 47) |> comment(chars, i, n)
| stop _ -> i

tor comment {chars: []const i64, i: i64, n: i64} -> i64
comment = peek(chars, i, n)
| more c when (c >= 0) && !((c == 10)) |> comment(chars, i: (i + 1), n)
| eol _ |> ws(chars, i, n)

tor word {chars: []const i64, i: i64, n: i64} -> i64
word = peek(chars, i, n)
| more c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i: (i + 1), n)
| stop _ -> i

tor toeol {chars: []const i64, i: i64, n: i64} -> i64
toeol = peek(chars, i, n)
| more c when (c >= 0) && !((c == 10)) |> toeol(chars, i: (i + 1), n)
| stop _ -> i

tor toarrow {chars: []const i64, i: i64, n: i64} -> i64
toarrow = peek(chars, i, n)
| arr c when (c == 45) && (chars[(i + 1)] == 62) -> i
| stp c when (c == 124) && (chars[(i + 1)] == 62) -> i
| ctr c when (c == 61) && (chars[(i + 1)] == 62) -> i
| more _ |> toarrow(chars, i: (i + 1), n)

tor toargend {chars: []const i64, i: i64, n: i64, d: i64, ins: i64} -> i64
toargend = peek(chars, i, n)
| fin c when c < 0 -> i
| str c when c == 34 |> toargend(chars, i: (i + 1), n, d, ins: if((ins == 1)) 0 else 1)
| deep c when (ins == 0) && (c == 40) |> toargend(chars, i: (i + 1), n, d: (d + 1), ins)
| end c when (ins == 0) && ((d == 0) && ((c == 44) || (c == 41))) -> i
| shal c when (ins == 0) && (c == 41) |> toargend(chars, i: (i + 1), n, d: (d - 1), ins)
| more _ |> toargend(chars, i: (i + 1), n, d, ins)

tor typend {chars: []const i64, i: i64, n: i64} -> i64
typend = peek(chars, i, n)
| stop c when (c == 44) || (c == 125) -> i
| fin c when c < 0 -> i
| more _ |> typend(chars, i: (i + 1), n)

tor kwtor {chars: []const i64, j: i64, e: i64, n: i64} -> i64
kwtor -> if(((e == (j + 3)) && ((chars[j] == 116) && ((chars[(j + 1)] == 111) && (chars[(j + 2)] == 114))))) 1 else 0

tor kwwhen {chars: []const i64, j: i64, e: i64, n: i64} -> i64
kwwhen -> if(((e == (j + 4)) && ((chars[j] == 119) && ((chars[(j + 1)] == 104) && ((chars[(j + 2)] == 101) && (chars[(j + 3)] == 110)))))) 1 else 0

tor kwimport {chars: []const i64, j: i64, e: i64, n: i64} -> i64
kwimport -> if(((e == (j + 6)) && ((chars[j] == 105) && ((chars[(j + 1)] == 109) && ((chars[(j + 2)] == 112) && ((chars[(j + 3)] == 111) && ((chars[(j + 4)] == 114) && (chars[(j + 5)] == 116)))))))) 1 else 0

tor hws {chars: []const i64, i: i64, n: i64} -> i64
hws = peek(chars, i, n)
| more c when (c == 32) || (c == 9) |> hws(chars, i: (i + 1), n)
| stop _ -> i

tor top {chars: []const i64, i: i64, n: i64, out: string} -> string
top = ws(chars, i, n)
| go j |> top-at(chars, i: j, n, out)

tor top-at {chars: []const i64, i: i64, n: i64, out: string} -> string
top-at = peek(chars, i, n)
| fin c when c < 0 -> out
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i, n) : e |> kwd(chars, i, n, out, e)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor kwd {chars: []const i64, i: i64, e: i64, n: i64, out: string} -> string
kwd = kwtor(chars, j: i, e, n)
| decl k when k == 1 |> decl(chars, i: e, n, out)
| item _ |> kwd2(chars, i, n, out, e)

tor kwd2 {chars: []const i64, i: i64, e: i64, n: i64, out: string} -> string
kwd2 = kwimport(chars, j: i, e, n)
| imp k when k == 1 |> imp-path(chars, i: e, n, out)
| item _ |> morf(chars, i: e, n, out, j: i, ne: e)

tor imp-path {chars: []const i64, i: i64, n: i64, out: string} -> string
imp-path = ws(chars, i, n)
| go p |> imp-path2(chars, i: p, n, out)

tor imp-path2 {chars: []const i64, i: i64, n: i64, out: string} -> string
imp-path2 = toeol(chars, i, n)
| done p1 |> top(chars, i: p1, n, out: (out ++ ("(imp " ++ (@intToString(i) ++ (" " ++ (@intToString(p1) ++ ") "))))))

tor morf {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
morf = ws(chars, i, n)
| go s |> morf-at(chars, i: s, n, out, j, ne)

tor morf-at {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
morf-at = peek(chars, i, n)
| impl c when (c == 45) && (chars[(i + 1)] == 62) |> impl-body(chars, i: (i + 2), n, out, j, ne)
| flow c when (c == 61) && !((chars[(i + 1)] == 62)) |> flow-pre(chars, i: (i + 1), n, out, j, ne)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor impl-body {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
impl-body = ws(chars, i, n)
| go v0 |> impl-val(chars, i: v0, n, out, j, ne)

tor impl-val {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
impl-val = toeol(chars, i, n)
| done v1 |> top(chars, i: v1, n, out: (out ++ ("(impl " ++ (@intToString(j) ++ (" " ++ (@intToString(ne) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(v1) ++ ") "))))))))))

tor flow-pre {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
flow-pre = ws(chars, i, n)
| go p |> flow-pre0(chars, i: p, n, out, j, ne)

tor flow-pre0 {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
flow-pre0 = peek(chars, i, n)
| lbl c when c == 35 |> word(chars, i: (i + 1), n) : le |> flow-lbl(chars, i: le, n, j, ne, out: (out ++ ("(lbl " ++ (@intToString((i + 1)) ++ (" " ++ (@intToString(le) ++ ") "))))))
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i, n) : he |> call-open(chars, i: he, n, out: ((out ++ ("(flw " ++ (@intToString(j) ++ (" " ++ (@intToString(ne) ++ ") "))))) ++ ("(call " ++ (@intToString(i) ++ (" " ++ (@intToString(he) ++ ") "))))))
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor flow-lbl {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
flow-lbl = ws(chars, i, n)
| go h |> flow-pre2(chars, i: h, n, out, j, ne)

tor flow-pre2 {chars: []const i64, i: i64, n: i64, j: i64, ne: i64, out: string} -> string
flow-pre2 = peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i, n) : he |> call-open(chars, i: he, n, out: ((out ++ ("(flw " ++ (@intToString(j) ++ (" " ++ (@intToString(ne) ++ ") "))))) ++ ("(call " ++ (@intToString(i) ++ (" " ++ (@intToString(he) ++ ") "))))))
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor call-open {chars: []const i64, i: i64, n: i64, out: string} -> string
call-open = ws(chars, i, n)
| go a |> call-at(chars, i: a, n, out)

tor call-at {chars: []const i64, i: i64, n: i64, out: string} -> string
call-at = peek(chars, i, n)
| open c when c == 40 |> args(chars, i: (i + 1), n, out)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor args {chars: []const i64, i: i64, n: i64, out: string} -> string
args = ws(chars, i, n)
| go a |> args-at(chars, i: a, n, out)

tor args-at {chars: []const i64, i: i64, n: i64, out: string} -> string
args-at = peek(chars, i, n)
| close c when c == 41 |> armloop(chars, i: (i + 1), n, out)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i, n) : we |> argname(chars, i, n, out, we)
| pos _ |> argval(chars, i, n, out)

tor argname {chars: []const i64, i: i64, we: i64, n: i64, out: string} -> string
argname = ws(chars, i: we, n)
| go d |> argname-at(chars, i: d, n, out, aj: i, ae: we)

tor argname-at {chars: []const i64, i: i64, n: i64, aj: i64, ae: i64, out: string} -> string
argname-at = peek(chars, i, n)
| named c when c == 58 |> ws(chars, i: (i + 1), n) : v0 |> argvaln(chars, i: v0, n, out, aj, ae)
| pos _ |> argval(chars, i: aj, n, out)

tor argvaln {chars: []const i64, i: i64, n: i64, aj: i64, ae: i64, out: string} -> string
argvaln = toargend(chars, i, n, d: 0, ins: 0)
| done v1 |> argnext(chars, i: v1, n, out: (out ++ ("(arg " ++ (@intToString(aj) ++ (" " ++ (@intToString(ae) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(v1) ++ ") "))))))))))

tor argval {chars: []const i64, i: i64, n: i64, out: string} -> string
argval = toargend(chars, i, n, d: 0, ins: 0)
| done v1 |> argnext(chars, i: v1, n, out: (out ++ ("(arg " ++ (@intToString(0) ++ (" " ++ (@intToString(0) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(v1) ++ ") "))))))))))

tor argnext {chars: []const i64, i: i64, n: i64, out: string} -> string
argnext = ws(chars, i, n)
| go d |> argnext-at(chars, i: d, n, out)

tor argnext-at {chars: []const i64, i: i64, n: i64, out: string} -> string
argnext-at = peek(chars, i, n)
| more c when c == 44 |> args(chars, i: (i + 1), n, out)
| close c when c == 41 |> armloop(chars, i: (i + 1), n, out)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor armloop {chars: []const i64, i: i64, n: i64, out: string} -> string
armloop = ws(chars, i, n)
| go a |> armloop-at(chars, i: a, n, out)

tor armloop-at {chars: []const i64, i: i64, n: i64, out: string} -> string
armloop-at = peek(chars, i, n)
| bar c when (c == 124) && !((chars[(i + 1)] == 62)) |> arm(chars, i: (i + 1), n, out)
| item _ |> top-at(chars, i, n, out)

tor arm {chars: []const i64, i: i64, n: i64, out: string} -> string
arm = ws(chars, i, n)
| go b |> arm1(chars, i: b, n, out)

tor arm1 {chars: []const i64, i: i64, n: i64, out: string} -> string
arm1 = peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i, n) : be |> arm-tail(chars, i: be, n, out: (out ++ ("(cont " ++ (@intToString(i) ++ (" " ++ (@intToString(be) ++ ") "))))))
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor arm-tail {chars: []const i64, i: i64, n: i64, out: string} -> string
arm-tail = hws(chars, i, n)
| go t |> arm-tok(chars, i: t, n, out)

tor arm-tok {chars: []const i64, i: i64, n: i64, out: string} -> string
arm-tok = peek(chars, i, n)
| prod c when (c == 45) && (chars[(i + 1)] == 62) |> arm-prod(chars, i: (i + 2), n, out)
| step c when (c == 124) && (chars[(i + 1)] == 62) |> arm-step(chars, i: (i + 2), n, out)
| ctor c when (c == 61) && (chars[(i + 1)] == 62) |> arm-ctor(chars, i: (i + 2), n, out)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i, n) : we |> arm-kw(chars, i, n, out, we)
| eol c when (c == 10) || (c < 0) |> armloop(chars, i, n, out)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor arm-kw {chars: []const i64, i: i64, we: i64, n: i64, out: string} -> string
arm-kw = kwwhen(chars, j: i, e: we, n)
| cond k when k == 1 |> arm-cond(chars, i: we, n, out)
| bind _ |> arm-tail(chars, i: we, n, out: (out ++ ("(bind " ++ (@intToString(i) ++ (" " ++ (@intToString(we) ++ ") "))))))

tor arm-cond {chars: []const i64, i: i64, n: i64, out: string} -> string
arm-cond = ws(chars, i, n)
| go c0 |> arm-cond2(chars, i: c0, n, out)

tor arm-cond2 {chars: []const i64, i: i64, n: i64, out: string} -> string
arm-cond2 = toarrow(chars, i, n)
| done c1 |> arm-tok(chars, i: c1, n, out: (out ++ ("(cond " ++ (@intToString(i) ++ (" " ++ (@intToString(c1) ++ ") "))))))

tor arm-prod {chars: []const i64, i: i64, n: i64, out: string} -> string
arm-prod = ws(chars, i, n)
| go v0 |> arm-prod2(chars, i: v0, n, out)

tor arm-prod2 {chars: []const i64, i: i64, n: i64, out: string} -> string
arm-prod2 = toeol(chars, i, n)
| done v1 |> armloop(chars, i: v1, n, out: (out ++ ("(step expr " ++ (@intToString(i) ++ (" " ++ (@intToString(v1) ++ ") "))))))

tor arm-step {chars: []const i64, i: i64, n: i64, out: string} -> string
arm-step = ws(chars, i, n)
| go s |> arm-step2(chars, i: s, n, out)

tor arm-step2 {chars: []const i64, i: i64, n: i64, out: string} -> string
arm-step2 = peek(chars, i, n)
| jump c when c == 64 |> word(chars, i: (i + 1), n) : le |> call-open(chars, i: le, n, out: (out ++ ("(step jump " ++ (@intToString((i + 1)) ++ (" " ++ (@intToString(le) ++ ") "))))))
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i, n) : se |> call-open(chars, i: se, n, out: (out ++ ("(step invoke " ++ (@intToString(i) ++ (" " ++ (@intToString(se) ++ ") "))))))
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor arm-ctor {chars: []const i64, i: i64, n: i64, out: string} -> string
arm-ctor = ws(chars, i, n)
| go w |> arm-ctor1(chars, i: w, n, out)

tor arm-ctor1 {chars: []const i64, i: i64, n: i64, out: string} -> string
arm-ctor1 = peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i, n) : ce |> arm-ctor2(chars, i: ce, n, out, cj: i, ce)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor arm-ctor2 {chars: []const i64, i: i64, n: i64, cj: i64, ce: i64, out: string} -> string
arm-ctor2 = ws(chars, i, n)
| go p |> arm-ctor3(chars, i: p, n, out, cj, ce)

tor arm-ctor3 {chars: []const i64, i: i64, n: i64, cj: i64, ce: i64, out: string} -> string
arm-ctor3 = toeol(chars, i, n)
| done t1 |> armloop(chars, i: t1, n, out: (out ++ ("(ctor " ++ (@intToString(cj) ++ (" " ++ (@intToString(ce) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(t1) ++ ") "))))))))))

tor decl {chars: []const i64, i: i64, n: i64, out: string} -> string
decl = ws(chars, i, n)
| go d |> decl1(chars, i: d, n, out)

tor decl1 {chars: []const i64, i: i64, n: i64, out: string} -> string
decl1 = peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i, n) : de |> decl-brace(chars, i: de, n, out: (out ++ ("(ev " ++ (@intToString(i) ++ (" " ++ (@intToString(de) ++ ") "))))))
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor decl-brace {chars: []const i64, i: i64, n: i64, out: string} -> string
decl-brace = ws(chars, i, n)
| go b |> decl-brace2(chars, i: b, n, out)

tor decl-brace2 {chars: []const i64, i: i64, n: i64, out: string} -> string
decl-brace2 = peek(chars, i, n)
| open c when c == 123 |> fields(chars, i: (i + 1), n, out)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor fields {chars: []const i64, i: i64, n: i64, out: string} -> string
fields = ws(chars, i, n)
| go f |> fields-at(chars, i: f, n, out)

tor fields-at {chars: []const i64, i: i64, n: i64, out: string} -> string
fields-at = peek(chars, i, n)
| close c when c == 125 |> decl-ret(chars, i: (i + 1), n, out)
| var c when c == 124 |> variant(chars, i: (i + 1), n, out)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i, n) : fe |> fld(chars, i, n, out, fe)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor fld {chars: []const i64, i: i64, fe: i64, n: i64, out: string} -> string
fld = ws(chars, i: fe, n)
| go c |> fld2(chars, i: c, n, out, fj: i, fe)

tor fld2 {chars: []const i64, i: i64, n: i64, fj: i64, fe: i64, out: string} -> string
fld2 = peek(chars, i, n)
| ty k when k == 58 |> ws(chars, i: (i + 1), n) : t0 |> fld3(chars, i: t0, n, out, fj, fe)
| bad k -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(k) ++ ") ")))))

tor fld3 {chars: []const i64, i: i64, n: i64, fj: i64, fe: i64, out: string} -> string
fld3 = typend(chars, i, n)
| done t1 |> fields2(chars, i: t1, n, out: (out ++ ("(fld " ++ (@intToString(fj) ++ (" " ++ (@intToString(fe) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(t1) ++ ") "))))))))))

tor fields2 {chars: []const i64, i: i64, n: i64, out: string} -> string
fields2 = ws(chars, i, n)
| go d |> fields2-at(chars, i: d, n, out)

tor fields2-at {chars: []const i64, i: i64, n: i64, out: string} -> string
fields2-at = peek(chars, i, n)
| more c when c == 44 |> fields(chars, i: (i + 1), n, out)
| close c when c == 125 |> decl-ret(chars, i: (i + 1), n, out)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor variant {chars: []const i64, i: i64, n: i64, out: string} -> string
variant = ws(chars, i, n)
| go v |> variant1(chars, i: v, n, out)

tor variant1 {chars: []const i64, i: i64, n: i64, out: string} -> string
variant1 = peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i, n) : ve |> variant2(chars, i, n, out, ve)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor variant2 {chars: []const i64, i: i64, ve: i64, n: i64, out: string} -> string
variant2 = ws(chars, i: ve, n)
| go t0 |> variant3(chars, i: t0, n, out, vj: i, ve)

tor variant3 {chars: []const i64, i: i64, n: i64, vj: i64, ve: i64, out: string} -> string
variant3 = toeol(chars, i, n)
| done t1 |> fields(chars, i: t1, n, out: (out ++ ("(brd " ++ (@intToString(vj) ++ (" " ++ (@intToString(ve) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(t1) ++ ") "))))))))))

tor decl-ret {chars: []const i64, i: i64, n: i64, out: string} -> string
decl-ret = ws(chars, i, n)
| go r |> decl-ret-at(chars, i: r, n, out)

tor decl-ret-at {chars: []const i64, i: i64, n: i64, out: string} -> string
decl-ret-at = peek(chars, i, n)
| ret c when (c == 45) && (chars[(i + 1)] == 62) |> ws(chars, i: (i + 2), n) : t0 |> decl-ret2(chars, i: t0, n, out)
| next _ |> branches(chars, i, n, out)

tor decl-ret2 {chars: []const i64, i: i64, n: i64, out: string} -> string
decl-ret2 = toeol(chars, i, n)
| done t1 |> branches(chars, i: t1, n, out: (out ++ ("(ret " ++ (@intToString(i) ++ (" " ++ (@intToString(t1) ++ ") "))))))

tor branches {chars: []const i64, i: i64, n: i64, out: string} -> string
branches = ws(chars, i, n)
| go b |> branches-at(chars, i: b, n, out)

tor branches-at {chars: []const i64, i: i64, n: i64, out: string} -> string
branches-at = peek(chars, i, n)
| br c when (c == 124) && !((chars[(i + 1)] == 62)) |> branch(chars, i: (i + 1), n, out)
| next _ |> top-at(chars, i, n, out)

tor branch {chars: []const i64, i: i64, n: i64, out: string} -> string
branch = ws(chars, i, n)
| go w |> branch1(chars, i: w, n, out)

tor branch1 {chars: []const i64, i: i64, n: i64, out: string} -> string
branch1 = peek(chars, i, n)
| id c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> word(chars, i, n) : be |> branch-ty(chars, i: be, n, out, bj: i, be)
| bad c -> (out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") ")))))

tor branch-ty {chars: []const i64, i: i64, n: i64, bj: i64, be: i64, out: string} -> string
branch-ty = hws(chars, i, n)
| h h |> branch-ty2(chars, i: h, n, out, bj, be)

tor branch-ty2 {chars: []const i64, i: i64, n: i64, bj: i64, be: i64, out: string} -> string
branch-ty2 = peek(chars, i, n)
| eol c when (c == 10) || (c < 0) |> branches(chars, i, n, out: (out ++ ("(brd " ++ (@intToString(bj) ++ (" " ++ (@intToString(be) ++ (" " ++ (@intToString(0) ++ (" " ++ (@intToString(0) ++ ") "))))))))))
| ty _ |> toeol(chars, i, n) : t1 |> branches(chars, i: t1, n, out: (out ++ ("(brd " ++ (@intToString(bj) ++ (" " ++ (@intToString(be) ++ (" " ++ (@intToString(i) ++ (" " ++ (@intToString(t1) ++ ") "))))))))))

tor main {chars: []const i64} -> string
main = top(chars, i: 0, n: @len(chars), out: "")
| done s -> s
