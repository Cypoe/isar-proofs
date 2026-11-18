// kwir.k — a koru-spelled lowerer → (graph …) claim text (generated)
// flat six-int rows + source bytes + names/nsp/strs/ssp
// tables in; claim S-expression text out.  arg-less invoke
// refuses: `rows`/`src`/`names`/`nsp`/`strs`/`ssp` unbound.
tor pkb {t: []const i64, i: i64, n: i64} -> i64
pkb -> (if(((i < 0) || (i >= n))) (0 - 1) else t[i])

tor wn0 {} -> i64
wn0 -> 0

tor wc2 {a: string, b: string} -> string
wc2 -> ((a ++ b))

tor wc3 {a: string, b: string, c: string} -> string
wc3 -> ((a ++ (b ++ c)))

tor wc5 {a: string, b: string, c: string, d: string, e: string} -> string
wc5 -> ((a ++ (b ++ (c ++ (d ++ e)))))

tor wc7 {a: string, b: string, c: string, d: string, e: string, f: string, g: string} -> string
wc7 -> ((a ++ (b ++ (c ++ (d ++ (e ++ (f ++ g)))))))

tor wsk {src: []const i64, i: i64, hi: i64} -> i64
wsk = pkb(t: src, i, n: hi)
| _ c when (c == 32) || ((c == 9) || ((c == 10) || (c == 13))) |> wsk(src, i: (i + 1), hi)
| _ _ -> i

tor wtb {src: []const i64, lo: i64, j: i64, n: i64} -> i64
wtb = pkb(t: src, i: j, n)
| _ c when (j >= lo) && ((c == 32) || ((c == 9) || ((c == 10) || (c == 13)))) |> wtb(src, lo, j: (j - 1), n)
| _ _ -> ((j + 1))

tor wid {c: i64} -> i64
wid -> (if(((((c >= 97) && (c <= 122)) || ((c >= 65) && (c <= 90))) || (((c >= 48) && (c <= 57)) || (c == 95)))) 1 else 0)

tor wpe {c: i64} -> i64
wpe = wid(c)
| _ r when r == 1 -> 1
| _ _ -> (if((((c == 41) || (c == 93)) || ((c == 125) || (c == 34)))) 1 else 0)

tor wnat {nsp: []const i64, nn: i64, i: i64, p: i64} -> i64
wnat = pkb(t: nsp, i: (2 * i), n: (2 * nn))
| _ v when (v == p) && (i < nn) -> i
| _ _ when i < nn |> wnat(nsp, nn, i: (i + 1), p)
| _ _ -> ((0 - 1))

tor wpix {nsp: []const i64, nn: i64, p: i64} -> i64
wpix = pkb(t: nsp, i: p, n: (@len(nsp) - (5 * nn)))
| _ k -> k

tor wnm {names: []const string, nsp: []const i64, nn: i64, p: i64} -> string
wnm = wpix(nsp, nn, p)
| _ k when k >= 0 -> (names[k])
| _ _ -> "(bad names)"

tor wne {nsp: []const i64, nn: i64, p: i64} -> i64
wne = wpix(nsp, nn, p)
| _ k when k >= 0 -> (nsp[(((@len(nsp) - (5 * nn)) + (2 * k)) + 1)])
| _ _ -> ((0 - 1))

tor wst {strs: []const string, ssp: []const i64, ns: i64, p: i64} -> string
wst = wnat(nsp: ssp, nn: ns, i: 0, p)
| _ k when k >= 0 -> (strs[k])
| _ _ -> "(bad strs)"

tor weq {src: []const i64, a: i64, b: i64, x: i64, y: i64} -> i64
weq = wn0()
| _ _ when (b - a) != (y - x) -> 0
| _ _ |> weql(src, a, b, x, y, i: 0)

tor weql {src: []const i64, a: i64, b: i64, x: i64, y: i64, i: i64} -> i64
weql = pkb(t: src, i: (a + i), n: b)
| _ c when c < 0 -> 1
| _ c when if(((x + i) < y)) (c != src[(x + i)]) else true -> 0
| _ _ |> weql(src, a, b, x, y, i: (i + 1))

tor wnv {src: []const i64, i: i64, hi: i64, v: i64} -> i64
wnv = pkb(t: src, i, n: hi)
| _ c when (c >= 48) && (c <= 57) |> wnv(src, i: (i + 1), hi, v: ((v * 10) + (c - 48)))
| _ _ -> v

tor wp10 {n: i64} -> i64
wp10 = wn0()
| _ _ when n <= 0 -> 1
| _ _ |> wp10m(n)

tor wp10m {n: i64} -> i64
wp10m = wp10(n: (n - 1))
| _ t -> ((t * 10))

tor wgcd {a: i64, b: i64} -> i64
wgcd = wn0()
| _ _ when b == 0 -> a
| _ _ |> wgcd(a: b, b: (a % b))

tor wpb {src: []const i64, lo: i64, i: i64} -> i64
wpb = pkb(t: src, i: (i - 1), n: i)
| _ _ when i <= lo -> 0
| _ c when (c == 32) || ((c == 9) || ((c == 10) || (c == 13))) |> wpb(src, lo, i: (i - 1))
| _ c -> c

tor wopa {src: []const i64, lo: i64, hi: i64, i: i64, d: i64, ins: i64} -> i64
wopa = wpb(src, lo, i)
| _ p when ((d == 0) && (ins == 0)) && (i < hi) |> wopb(src, i, hi, p)
| _ _ -> 0

tor wopb {src: []const i64, i: i64, hi: i64, p: i64} -> i64
wopb = pkb(t: src, i, n: hi)
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
| _ c when c == 43 |> wope(src, i, hi, p, op: 0)
| _ c when c == 45 |> wops(src, i, hi, p)
| _ c when c == 111 |> wopo(src, i, hi, p)
| _ c when c == 97 |> wopd(src, i, hi, p)
| _ _ -> 0

tor wope {src: []const i64, i: i64, hi: i64, p: i64, op: i64} -> i64
wope = wpe(c: p)
| _ v when v == 1 -> (((op * 8) + 1))
| _ _ -> 0

tor wops {src: []const i64, i: i64, hi: i64, p: i64} -> i64
wops = pkb(t: src, i: (i + 1), n: hi)
| _ n when (((p >= 97) && (p <= 122)) || (((p >= 65) && (p <= 90)) || (((p >= 48) && (p <= 57)) || (p == 95)))) && ((((n >= 97) && (n <= 122)) || (((n >= 65) && (n <= 90)) || (((n >= 48) && (n <= 57)) || (n == 95)))) || (n == 45)) -> 0
| _ _ |> wope(src, i, hi, p, op: 1)

tor wopo {src: []const i64, i: i64, hi: i64, p: i64} -> i64
wopo = pkb(t: src, i: (i + 1), n: hi)
| _ n when n == 114 |> wopo2(src, i, hi, p)
| _ _ -> 0

tor wopo2 {src: []const i64, i: i64, hi: i64, p: i64} -> i64
wopo2 = wpe(c: p)
| _ v when v == 1 |> wopob(src, i, hi)
| _ _ -> 0

tor wopob {src: []const i64, i: i64, hi: i64} -> i64
wopob = pkb(t: src, i: (i + 2), n: hi)
| _ c when c < 0 -> (((12 * 8) + 2))
| _ c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || (((c >= 48) && (c <= 57)) || (c == 95))) -> 0
| _ c when (c == 45) && if(((i + 3) < hi)) (((src[(i + 3)] >= 97) && (src[(i + 3)] <= 122)) || (((src[(i + 3)] >= 65) && (src[(i + 3)] <= 90)) || (((src[(i + 3)] >= 48) && (src[(i + 3)] <= 57)) || ((src[(i + 3)] == 95) || (src[(i + 3)] == 45))))) else false -> 0
| _ _ -> (((12 * 8) + 2))

tor wopd {src: []const i64, i: i64, hi: i64, p: i64} -> i64
wopd = pkb(t: src, i: (i + 1), n: hi)
| _ n when (n == 110) && if(((i + 2) < hi)) (src[(i + 2)] == 100) else false |> wopd2(src, i, hi, p)
| _ _ -> 0

tor wopd2 {src: []const i64, i: i64, hi: i64, p: i64} -> i64
wopd2 = wpe(c: p)
| _ v when v == 1 |> wopdb(src, i, hi)
| _ _ -> 0

tor wopdb {src: []const i64, i: i64, hi: i64} -> i64
wopdb = pkb(t: src, i: (i + 3), n: hi)
| _ c when c < 0 -> (((11 * 8) + 3))
| _ c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || (((c >= 48) && (c <= 57)) || (c == 95))) -> 0
| _ c when (c == 45) && if(((i + 4) < hi)) (((src[(i + 4)] >= 97) && (src[(i + 4)] <= 122)) || (((src[(i + 4)] >= 65) && (src[(i + 4)] <= 90)) || (((src[(i + 4)] >= 48) && (src[(i + 4)] <= 57)) || ((src[(i + 4)] == 95) || (src[(i + 4)] == 45))))) else false -> 0
| _ _ -> (((11 * 8) + 3))

tor wprc {o: i64} -> i64
wprc -> (if((o == 12)) 1 else if((o == 11)) 2 else if(((o == 5) || (o == 6))) 3 else if(((o >= 7) && (o <= 10))) 4 else if((o == 13)) 5 else if(((o == 0) || (o == 1))) 6 else 7)

tor wopn {o: i64} -> string
wopn -> (if((o == 0)) "add" else if((o == 1)) "sub" else if((o == 2)) "mul" else if((o == 3)) "div" else if((o == 4)) "mod" else if((o == 5)) "eq" else if((o == 6)) "ne" else if((o == 7)) "lt" else if((o == 8)) "le" else if((o == 9)) "gt" else if((o == 10)) "ge" else if((o == 11)) "and" else if((o == 12)) "or" else "concat")

tor wfp {src: []const i64, lo: i64, hi: i64, i: i64, d: i64, ins: i64, last: i64, prec: i64} -> i64
wfp = wopa(src, lo, hi, i, d, ins)
| _ o when (i >= hi) || (o == (0 - 2)) -> last
| _ o when o != 0 |> wfp1(src, lo, hi, i, d, ins, last, prec, o)
| _ _ |> wfpn(src, lo, hi, i, d, ins, last, prec)

tor wfp1 {src: []const i64, lo: i64, hi: i64, i: i64, d: i64, ins: i64, last: i64, prec: i64, o: i64} -> i64
wfp1 = wprc(o: (o / 8))
| _ q when q == prec |> wfpn(src, lo, hi, i, d, ins, last: i, prec)
| _ _ |> wfpn(src, lo, hi, i, d, ins, last, prec)

tor wfpn {src: []const i64, lo: i64, hi: i64, i: i64, d: i64, ins: i64, last: i64, prec: i64} -> i64
wfpn = wfp(src, lo, hi, i: (i + (if(((ins == 1) && (src[i] == 92))) 2 else 1)), d: if(((ins == 0) && (((src[i] == 40) || (src[i] == 91)) || (src[i] == 123)))) (d + 1) else if(((ins == 0) && (((src[i] == 41) || (src[i] == 93)) || (src[i] == 125)))) (d - 1) else d, ins: if(((src[i] == 34) && (ins == 0))) 1 else if(((src[i] == 34) && (ins == 1))) 0 else ins, last, prec)
| _ r -> r

tor wmb {src: []const i64, i: i64, hi: i64} -> i64
wmb = pkb(t: src, i: (i + 1), n: hi)
| _ _ |> wmb1(src, i: (i + 1), hi, d: 1, ins: 0)

tor wmb1 {src: []const i64, i: i64, hi: i64, d: i64, ins: i64} -> i64
wmb1 = pkb(t: src, i, n: hi)
| _ c when c < 0 -> hi
| _ c when (ins == 0) && (c == 34) |> wmb1(src, i: (i + 1), hi, d, ins: 1)
| _ c when (ins == 1) && (c == 34) |> wmb1(src, i: (i + 1), hi, d, ins: 0)
| _ c when (ins == 1) && (c == 92) |> wmb1(src, i: (i + 2), hi, d, ins)
| _ c when (ins == 0) && (((c == 40) || (c == 91)) || (c == 123)) |> wmb1(src, i: (i + 1), hi, d: (d + 1), ins)
| _ c when (ins == 0) && (((c == 41) || (c == 93)) || (c == 125)) |> wmbx(src, i, hi, d)
| _ _ |> wmb1(src, i: (i + 1), hi, d, ins)

tor wmbx {src: []const i64, i: i64, hi: i64, d: i64} -> i64
wmbx = wn0()
| _ _ when (d - 1) == 0 -> i
| _ _ |> wmb1(src, i: (i + 1), hi, d: (d - 1), ins: 0)

tor wss {src: []const i64, i: i64, hi: i64} -> i64
wss = pkb(t: src, i: (i + 1), n: hi)
| _ c when c < 0 -> hi
| _ c when c == 34 -> ((i + 2))
| _ c when c == 92 |> wss(src, i: (i + 2), hi)
| _ _ |> wss(src, i: (i + 1), hi)

tor wen {src: []const i64, i: i64, hi: i64} -> i64
wen = pkb(t: src, i, n: hi)
| _ c when (c >= 48) && (c <= 57) |> wen(src, i: (i + 1), hi)
| _ c when (c == 46) && if(((i + 1) < hi)) ((src[(i + 1)] >= 48) && (src[(i + 1)] <= 57)) else false |> wen(src, i: (i + 1), hi)
| _ _ -> i

tor wcmx {src: []const i64, i: i64, hi: i64, d: i64, ins: i64, w: i64} -> i64
wcmx = pkb(t: src, i, n: hi)
| _ c when c < 0 -> i
| _ c when (d == 0) && ((ins == 0) && (c == w)) -> i
| _ c when (ins == 0) && (c == 34) |> wcmx(src, i: (i + 1), hi, d, ins: 1, w)
| _ c when (ins == 1) && (c == 34) |> wcmx(src, i: (i + 1), hi, d, ins: 0, w)
| _ c when (ins == 1) && (c == 92) |> wcmx(src, i: (i + 2), hi, d, ins, w)
| _ c when (ins == 0) && (((c == 40) || (c == 91)) || (c == 123)) |> wcmx(src, i: (i + 1), hi, d: (d + 1), ins, w)
| _ c when (ins == 0) && (((c == 41) || (c == 93)) || (c == 125)) |> wcmx(src, i: (i + 1), hi, d: (d - 1), ins, w)
| _ _ |> wcmx(src, i: (i + 1), hi, d, ins, w)

tor wfd {src: []const i64, i: i64, hi: i64, d: i64, ins: i64, last: i64} -> i64
wfd = pkb(t: src, i, n: hi)
| _ c when c < 0 -> last
| _ c when (d == 0) && ((ins == 0) && (c == 46)) |> wfd(src, i: (i + 1), hi, d, ins, last: i)
| _ c when (ins == 0) && (c == 34) |> wfd(src, i: (i + 1), hi, d, ins: 1, last)
| _ c when (ins == 1) && (c == 34) |> wfd(src, i: (i + 1), hi, d, ins: 0, last)
| _ c when (ins == 1) && (c == 92) |> wfd(src, i: (i + 2), hi, d, ins, last)
| _ c when (ins == 0) && (((c == 40) || (c == 91)) || (c == 123)) |> wfd(src, i: (i + 1), hi, d: (d + 1), ins, last)
| _ c when (ins == 0) && (((c == 41) || (c == 93)) || (c == 125)) |> wfd(src, i: (i + 1), hi, d: (d - 1), ins, last)
| _ _ |> wfd(src, i: (i + 1), hi, d, ins, last)

tor wty {nm: string} -> i64
wty -> (if(((((nm == "i64") || (nm == "i32")) || ((nm == "i16") || (nm == "i8"))) || ((((nm == "u64") || (nm == "u32")) || ((nm == "u16") || (nm == "u8"))) || (((nm == "f64") || (nm == "f32")) || ((nm == "bool") || (nm == "string")))))) 1 else if((((nm == "program") || (nm == "void")) || (nm == "unit"))) 1 else 0)

tor wbl {nm: string} -> i64
wbl -> (if((((((nm == "as") || (nm == "intCast")) || ((nm == "truncate") || (nm == "divTrunc"))) || (((nm == "rem") || (nm == "mod")) || ((nm == "len") || (nm == "intToString")))) || ((((nm == "chars") || (nm == "charsToString")) || (nm == "charToString")) || (nm == "contains")))) 1 else 0)

tor wev {lv: i64, src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wev = wfp(src, lo, hi, i: lo, d: 0, ins: 0, last: (0 - 1), prec: lv)
| _ t when t >= 0 |> wspl(lv, src, lo, hi, t, names, nsp, nn, strs, ssp, ns)
| _ _ |> wenx(lv, src, lo, hi, names, nsp, nn, strs, ssp, ns)

tor wenx {lv: i64, src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wenx = wn0()
| _ _ when lv < 7 |> wev(lv: (lv + 1), src, lo, hi, names, nsp, nn, strs, ssp, ns)
| _ _ |> weu(src, lo, hi, names, nsp, nn, strs, ssp, ns)

tor wspl {lv: i64, src: []const i64, lo: i64, hi: i64, t: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wspl = wopa(src, lo, hi, i: t, d: 0, ins: 0)
| _ o when o > 0 |> wev(lv, src, lo, hi: t, names, nsp, nn, strs, ssp, ns) : l |> wsplr(lv, src, lo: (t + (o - ((o / 8) * 8))), hi, op: (o / 8), l, names, nsp, nn, strs, ssp, ns)
| _ _ -> "(bad expr)"

tor wsplr {lv: i64, src: []const i64, lo: i64, hi: i64, op: i64, l: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wsplr = wev(lv, src, lo, hi, names, nsp, nn, strs, ssp, ns)
| _ r |> wc7(a: "(bin ", b: if((op == 0)) "add" else if((op == 1)) "sub" else if((op == 2)) "mul" else if((op == 3)) "div" else if((op == 4)) "mod" else if((op == 5)) "eq" else if((op == 6)) "ne" else if((op == 7)) "lt" else if((op == 8)) "le" else if((op == 9)) "gt" else if((op == 10)) "ge" else if((op == 11)) "and" else if((op == 12)) "or" else "concat", c: " ", d: l, e: " ", f: r, g: ")")

tor weu {src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
weu = wsk(src, i: lo, hi)
| _ i when if((i < hi)) (src[i] == 33) else false |> weu1(src, i, hi, op: 1, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 45) else false |> weu1(src, i, hi, op: 0, names, nsp, nn, strs, ssp, ns)
| _ _ |> wep(src, lo, hi, names, nsp, nn, strs, ssp, ns)

tor weu1 {src: []const i64, i: i64, hi: i64, op: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
weu1 = weu(src, lo: (i + 1), hi, names, nsp, nn, strs, ssp, ns)
| _ e -> (if((op == 1)) ("(un not " ++ (e ++ ")")) else ("(un neg " ++ (e ++ ")")))

tor wpm {src: []const i64, lo: i64, hi: i64, nsp: []const i64, nn: i64} -> i64
wpm = wsk(src, i: lo, hi)
| _ i when if((i < hi)) (src[i] == 40) else false |> wpmc(src, i, hi)
| _ i when if((i < hi)) (src[i] == 91) else false |> wpmc(src, i, hi)
| _ i when if((i < hi)) (src[i] == 123) else false |> wpmc(src, i, hi)
| _ i when if((i < hi)) (src[i] == 34) else false |> wss(src, i, hi)
| _ i when if((i < hi)) (src[i] == 64) else false -> hi
| _ i when if((i < hi)) ((src[i] >= 48) && (src[i] <= 57)) else false |> wen(src, i, hi)
| _ i when if((i < hi)) (((src[i] >= 97) && (src[i] <= 122)) || (((src[i] >= 65) && (src[i] <= 90)) || (src[i] == 95))) else false |> wpmv(src, i, hi, nsp, nn)
| _ _ -> hi

tor wpmc {src: []const i64, i: i64, hi: i64} -> i64
wpmc = wmb(src, i, hi)
| _ m -> (if((m < hi)) (m + 1) else hi)

tor wpmv {src: []const i64, i: i64, hi: i64, nsp: []const i64, nn: i64} -> i64
wpmv = wne(nsp, nn, p: i)
| _ e |> wpmv1(src, i, e, hi)

tor wpmv1 {src: []const i64, i: i64, e: i64, hi: i64} -> i64
wpmv1 = wn0()
| _ _ when (e == (i + 2)) && if(((i + 1) < hi)) ((src[i] == 105) && (src[(i + 1)] == 102)) else false -> hi
| _ _ |> wpmv2(src, e, hi)

tor wpmv2 {src: []const i64, e: i64, hi: i64} -> i64
wpmv2 = wsk(src, i: e, hi)
| _ j when if((j < hi)) (src[j] == 40) else false |> wpmc(src, i: j, hi)
| _ _ -> e

tor wep {src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wep = wpm(src, lo, hi, nsp, nn)
| _ p |> wem(src, lo, hi: p, names, nsp, nn, strs, ssp, ns) : a |> wep1(src, i: p, hi, acc: a, names, nsp, nn, strs, ssp, ns)

tor wep1 {src: []const i64, i: i64, hi: i64, acc: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wep1 = wsk(src, i, hi)
| _ j when if((j < hi)) (src[j] == 46) else false |> wep1f(src, j, hi, acc, names, nsp, nn, strs, ssp, ns)
| _ j when if((j < hi)) (src[j] == 91) else false |> wep1i(src, j, hi, acc, names, nsp, nn, strs, ssp, ns)
| _ j when if((j < hi)) (src[j] == 40) else false -> "(bad expr-call)"
| _ j when if((j < hi)) ((src[j] == 32) || ((src[j] == 9) || ((src[j] == 10) || (src[j] == 13)))) else false |> wep1(src, i: (j + 1), hi, acc, names, nsp, nn, strs, ssp, ns)
| _ _ -> acc

tor wep1f {src: []const i64, j: i64, hi: i64, acc: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wep1f = wne(nsp, nn, p: (j + 1))
| _ e when e > (j + 1) |> wnm(names, nsp, nn, p: (j + 1)) : nm |> wep1(src, i: e, hi, acc: ("(field " ++ (acc ++ (" " ++ (nm ++ ")")))), names, nsp, nn, strs, ssp, ns)
| _ _ -> "(bad expr)"

tor wep1i {src: []const i64, j: i64, hi: i64, acc: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wep1i = wsk(src, i: (j + 1), hi)
| _ k |> wep1t(src, j, k, hi, acc, names, nsp, nn, strs, ssp, ns)

tor wep1t {src: []const i64, j: i64, k: i64, hi: i64, acc: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wep1t = wnm(names, nsp, nn, p: k)
| _ nm |> wty(nm) : t |> wep1u(src, j, k, hi, acc, t, names, nsp, nn, strs, ssp, ns)

tor wep1u {src: []const i64, j: i64, k: i64, hi: i64, acc: string, t: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wep1u = wne(nsp, nn, p: k)
| _ e when (t == 1) && (e > k) |> wep1v(src, j, e, hi, acc, names, nsp, nn, strs, ssp, ns)
| _ _ |> wmb(src, i: j, hi) : m |> wev(lv: 1, src, lo: (j + 1), hi: m, names, nsp, nn, strs, ssp, ns) : x |> wep1w(src, m, hi, acc, x, names, nsp, nn, strs, ssp, ns)

tor wep1v {src: []const i64, j: i64, e: i64, hi: i64, acc: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wep1v = wsk(src, i: e, hi)
| _ q when if((q < hi)) (src[q] == 93) else false |> wep1(src, i: (q + 1), hi, acc, names, nsp, nn, strs, ssp, ns)
| _ _ |> wmb(src, i: j, hi) : m |> wev(lv: 1, src, lo: (j + 1), hi: m, names, nsp, nn, strs, ssp, ns) : x |> wep1w(src, m, hi, acc, x, names, nsp, nn, strs, ssp, ns)

tor wep1w {src: []const i64, m: i64, hi: i64, acc: string, x: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wep1w = wc5(a: "(index ", b: acc, c: " ", d: x, e: ")")
| _ a |> wep1(src, i: (m + 1), hi, acc: a, names, nsp, nn, strs, ssp, ns)

tor wem {src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wem = wsk(src, i: lo, hi)
| _ i when if((i < hi)) (src[i] == 40) else false |> wemg(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 91) else false |> wema(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 123) else false |> wemc(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 64) else false |> wemb(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 34) else false |> wems(src, i, strs, ssp, ns)
| _ i when if((i < hi)) ((src[i] >= 48) && (src[i] <= 57)) else false |> wnum(src, lo: i, hi, names, nsp, nn, strs, ssp, ns) : x |> wc3(a: "(lit ", b: x, c: ")")
| _ i when if((i < hi)) (((src[i] >= 97) && (src[i] <= 122)) || (((src[i] >= 65) && (src[i] <= 90)) || (src[i] == 95))) else false |> wemv(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ _ -> "(bad expr)"

tor wems {src: []const i64, i: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wems = wst(strs, ssp, ns, p: i)
| _ s |> wc5(a: "(lit (str ", b: "\"", c: s, d: "\"", e: "))")

tor wemg {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wemg = wmb(src, i, hi)
| _ m |> wev(lv: 1, src, lo: (i + 1), hi: m, names, nsp, nn, strs, ssp, ns)

tor wema {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wema = wmb(src, i, hi)
| _ m |> weal(src, i: (i + 1), hi: m, out: "(lit (arr", names, nsp, nn, strs, ssp, ns) : t |> wc3(a: t, b: ")", c: ")")

tor weal {src: []const i64, i: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
weal = wsk(src, i, hi)
| _ j when j >= hi -> out
| _ j |> wcmx(src, i: j, hi, d: 0, ins: 0, w: 44) : c |> weal1(src, j, c, hi, out, names, nsp, nn, strs, ssp, ns)

tor weal1 {src: []const i64, j: i64, c: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
weal1 = wel(src, lo: j, hi: c, names, nsp, nn, strs, ssp, ns)
| _ x |> wc3(a: out, b: " ", c: x) : o |> weal(src, i: (c + 1), hi, out: o, names, nsp, nn, strs, ssp, ns)

tor wemc {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wemc = wmb(src, i, hi)
| _ m |> wecl(src, i: (i + 1), hi: m, out: "(lit (cell", names, nsp, nn, strs, ssp, ns) : t |> wc3(a: t, b: ")", c: ")")

tor wecl {src: []const i64, i: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wecl = wsk(src, i, hi)
| _ j when j >= hi -> out
| _ j |> wcmx(src, i: j, hi, d: 0, ins: 0, w: 58) : c |> wecl1(src, j, c, hi, out, names, nsp, nn, strs, ssp, ns)

tor wecl1 {src: []const i64, j: i64, c: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wecl1 = wcmx(src, i: (c + 1), hi, d: 0, ins: 0, w: 44)
| _ m |> wecl2(src, j, c, m, hi, out, names, nsp, nn, strs, ssp, ns)

tor wecl2 {src: []const i64, j: i64, c: i64, m: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wecl2 = wnm(names, nsp, nn, p: j)
| _ nm |> wel(src, lo: (c + 1), hi: m, names, nsp, nn, strs, ssp, ns) : x |> wecl3(src, m, hi, out, nm, x, names, nsp, nn, strs, ssp, ns)

tor wecl3 {src: []const i64, m: i64, hi: i64, out: string, nm: string, x: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wecl3 = wc5(a: out, b: " (", c: nm, d: " ", e: x)
| _ o |> wc3(a: o, b: ")", c: "") : p |> wecl(src, i: (m + 1), hi, out: p, names, nsp, nn, strs, ssp, ns)

tor wemb {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wemb = wnm(names, nsp, nn, p: (i + 1))
| _ nm |> wbl(nm) : b |> wemb1(src, i, hi, nm, b, names, nsp, nn, strs, ssp, ns)

tor wemb1 {src: []const i64, i: i64, hi: i64, nm: string, b: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wemb1 = wn0()
| _ _ when b == 0 -> "(bad builtin)"
| _ _ |> wne(nsp, nn, p: (i + 1)) : e |> wemb2(src, e, hi, nm, names, nsp, nn, strs, ssp, ns)

tor wemb2 {src: []const i64, e: i64, hi: i64, nm: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wemb2 = wsk(src, i: e, hi)
| _ j when if((j < hi)) (src[j] == 40) else false |> wmb(src, i: j, hi) : m |> wc3(a: "(builtin ", b: nm, c: "") : p |> webal(src, i: (j + 1), hi: m, out: p, names, nsp, nn, strs, ssp, ns) : t |> wc2(a: t, b: ")")
| _ _ -> "(bad builtin)"

tor webal {src: []const i64, i: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
webal = wsk(src, i, hi)
| _ j when j >= hi -> out
| _ j |> wcmx(src, i: j, hi, d: 0, ins: 0, w: 44) : v |> webal1(src, j, v, hi, out, names, nsp, nn, strs, ssp, ns)

tor webal1 {src: []const i64, j: i64, v: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
webal1 = wcmx(src, i: j, hi, d: 0, ins: 0, w: 58)
| _ c when c < v |> wc3(a: out, b: " ", c: "(bad builtin-arg)") : o |> webal(src, i: (v + 1), hi, out: o, names, nsp, nn, strs, ssp, ns)
| _ _ |> wev(lv: 1, src, lo: j, hi: v, names, nsp, nn, strs, ssp, ns) : x |> wc3(a: out, b: " ", c: x) : o |> webal(src, i: (v + 1), hi, out: o, names, nsp, nn, strs, ssp, ns)

tor wemv {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wemv = wnm(names, nsp, nn, p: i)
| _ nm when nm == "if" |> wemi(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ nm when nm == "true" -> "(lit (bool true))"
| _ nm when nm == "false" -> "(lit (bool false))"
| _ nm when ((nm == "else") || (nm == "when")) || ((nm == "or") || (nm == "and")) -> "(bad expr)"
| _ nm |> wemvd(src, i, hi, nm, names, nsp, nn, strs, ssp, ns)

tor wemvd {src: []const i64, i: i64, hi: i64, nm: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wemvd = wne(nsp, nn, p: i)
| _ e |> wsk(src, i: e, hi) : j |> wemve(src, j, hi, nm)

tor wemve {src: []const i64, j: i64, hi: i64, nm: string} -> string
wemve = wn0()
| _ _ when if((j < hi)) (src[j] == 40) else false -> "(bad expr-call)"
| _ _ |> wc3(a: "(var ", b: nm, c: ")")

tor wemi {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wemi = wne(nsp, nn, p: i)
| _ e |> wsk(src, i: e, hi) : j |> wemi1(src, j, hi, names, nsp, nn, strs, ssp, ns)

tor wemi1 {src: []const i64, j: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wemi1 = pkb(t: src, i: j, n: hi)
| _ c when c == 40 |> wmb(src, i: j, hi) : m |> wemi2(src, j, m, hi, names, nsp, nn, strs, ssp, ns)
| _ _ -> "(bad if)"

tor wemi2 {src: []const i64, j: i64, m: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wemi2 = wev(lv: 1, src, lo: (j + 1), hi: m, names, nsp, nn, strs, ssp, ns)
| _ c |> wfel(src, i: (m + 1), hi, d: 0, ins: 0, ifd: 0) : el |> wemi3(src, m, el, c, hi, names, nsp, nn, strs, ssp, ns)

tor wemi3 {src: []const i64, m: i64, el: i64, c: string, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wemi3 = wev(lv: 1, src, lo: (m + 1), hi: el, names, nsp, nn, strs, ssp, ns)
| _ t |> wev(lv: 1, src, lo: (el + 4), hi, names, nsp, nn, strs, ssp, ns) : fv |> wc7(a: "(cond ", b: c, c: " ", d: t, e: " ", f: fv, g: ")")

tor wtek {src: []const i64, i: i64, hi: i64, d: i64, ins: i64} -> i64
wtek = pkb(t: src, i, n: hi)
| _ c when c < 0 -> ((0 - 1))
| _ _ when (d != 0) || (ins != 0) -> 0
| _ c when c == 101 |> wtek1(src, i, hi)
| _ c when c == 105 |> wtek2(src, i, hi)
| _ _ -> 0

tor wtek1 {src: []const i64, i: i64, hi: i64} -> i64
wtek1 = wbd(src, pv: (i - 1), nx: (i + 4), hi)
| _ b when b == 0 -> 0
| _ _ |> wtek1b(src, i, hi)

tor wtek1b {src: []const i64, i: i64, hi: i64} -> i64
wtek1b = pkb(t: src, i: (i + 1), n: hi)
| _ c when (c == 108) && if(((i + 3) < hi)) ((src[(i + 2)] == 115) && (src[(i + 3)] == 101)) else false -> 1
| _ _ -> 0

tor wtek2 {src: []const i64, i: i64, hi: i64} -> i64
wtek2 = wbd(src, pv: (i - 1), nx: (i + 2), hi)
| _ b when b == 0 -> 0
| _ _ |> wtek2b(src, i, hi)

tor wtek2b {src: []const i64, i: i64, hi: i64} -> i64
wtek2b = pkb(t: src, i: (i + 1), n: hi)
| _ c when c == 102 -> 2
| _ _ -> 0

tor wbd {src: []const i64, pv: i64, nx: i64, hi: i64} -> i64
wbd = pkb(t: src, i: pv, n: hi)
| _ c when (((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || (((c >= 48) && (c <= 57)) || (c == 95)))) || (c == 45) -> 0
| _ _ |> wbd1(src, nx, hi)

tor wbd1 {src: []const i64, nx: i64, hi: i64} -> i64
wbd1 = pkb(t: src, i: nx, n: hi)
| _ c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || (((c >= 48) && (c <= 57)) || (c == 95))) -> 0
| _ c when (c == 45) && if(((nx + 1) < hi)) (((src[(nx + 1)] >= 97) && (src[(nx + 1)] <= 122)) || (((src[(nx + 1)] >= 65) && (src[(nx + 1)] <= 90)) || (((src[(nx + 1)] >= 48) && (src[(nx + 1)] <= 57)) || ((src[(nx + 1)] == 95) || (src[(nx + 1)] == 45))))) else false -> 0
| _ _ -> 1

tor wfel {src: []const i64, i: i64, hi: i64, d: i64, ins: i64, ifd: i64} -> i64
wfel = wtek(src, i, hi, d, ins)
| _ r when r < 0 -> hi
| _ r when (r == 1) && (ifd == 0) -> i
| _ r when r == 1 |> wfel(src, i: (i + 4), hi, d, ins, ifd: (ifd - 1))
| _ r when r == 2 |> wfel(src, i: (i + 2), hi, d, ins, ifd: (ifd + 1))
| _ _ |> wfeln(src, i, hi, d, ins, ifd)

tor wfeln {src: []const i64, i: i64, hi: i64, d: i64, ins: i64, ifd: i64} -> i64
wfeln = wfel(src, i: (i + (if(((ins == 1) && (src[i] == 92))) 2 else 1)), hi, d: if(((ins == 0) && (((src[i] == 40) || (src[i] == 91)) || (src[i] == 123)))) (d + 1) else if(((ins == 0) && (((src[i] == 41) || (src[i] == 93)) || (src[i] == 125)))) (d - 1) else d, ins: if(((src[i] == 34) && (ins == 0))) 1 else if(((src[i] == 34) && (ins == 1))) 0 else ins, ifd)
| _ r -> r

tor wnum {src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wnum = wen(src, i: lo, hi)
| _ e |> wfd(src, i: lo, hi: e, d: 0, ins: 0, last: (0 - 1)) : d |> wnum1(src, lo, e, d)

tor wnum1 {src: []const i64, lo: i64, e: i64, d: i64} -> string
wnum1 = wnv(src, i: lo, hi: e, v: 0)
| _ v when d < 0 |> wc3(a: "(int ", b: @intToString(v), c: ")")
| _ v |> wnum2(src, e, d, w: v)

tor wnum2 {src: []const i64, e: i64, d: i64, w: i64} -> string
wnum2 = wnv(src, i: (d + 1), hi: e, v: 0)
| _ f |> wp10(n: (e - (d + 1))) : dn |> wnum3(e, d, w, f, dn)

tor wnum3 {e: i64, d: i64, w: i64, f: i64, dn: i64} -> string
wnum3 = wgcd(a: f, b: dn)
| _ g when g > 0 |> wc5(a: "(float ", b: @intToString(((w * (dn / g)) + (f / g))), c: " ", d: @intToString((dn / g)), e: ")")
| _ _ -> "(bad float)"

tor wel {src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wel = wsk(src, i: lo, hi)
| _ i when if((i < hi)) (src[i] == 40) else false |> welg(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 91) else false |> wela(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 123) else false |> welc(src, i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 34) else false |> wst(strs, ssp, ns, p: i) : s |> wc5(a: "(str ", b: "\"", c: s, d: "\"", e: ")")
| _ i when if((i < hi)) ((src[i] >= 48) && (src[i] <= 57)) else false |> wnum(src, lo: i, hi, names, nsp, nn, strs, ssp, ns)
| _ i when if((i < hi)) (src[i] == 116) else false |> wel1(src, i, hi, nm: "true", names, nsp, nn)
| _ i when if((i < hi)) (src[i] == 102) else false |> wel1(src, i, hi, nm: "false", names, nsp, nn)
| _ _ -> "(bad lit)"

tor wel1 {src: []const i64, i: i64, hi: i64, nm: string, names: []const string, nsp: []const i64, nn: i64} -> string
wel1 = wnm(names, nsp, nn, p: i)
| _ v when v == nm |> wc3(a: "(bool ", b: nm, c: ")")
| _ _ -> "(bad lit)"

tor welg {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
welg = wmb(src, i, hi)
| _ m |> wel(src, lo: (i + 1), hi: m, names, nsp, nn, strs, ssp, ns)

tor wela {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wela = wmb(src, i, hi)
| _ m |> well(src, i: (i + 1), hi: m, out: "(arr", names, nsp, nn, strs, ssp, ns) : t |> wc2(a: t, b: ")")

tor well {src: []const i64, i: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
well = wsk(src, i, hi)
| _ j when j >= hi -> out
| _ j |> wcmx(src, i: j, hi, d: 0, ins: 0, w: 44) : c |> well1(src, j, c, hi, out, names, nsp, nn, strs, ssp, ns)

tor well1 {src: []const i64, j: i64, c: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
well1 = wel(src, lo: j, hi: c, names, nsp, nn, strs, ssp, ns)
| _ x |> wc3(a: out, b: " ", c: x) : o |> well(src, i: (c + 1), hi, out: o, names, nsp, nn, strs, ssp, ns)

tor welc {src: []const i64, i: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
welc = wmb(src, i, hi)
| _ m |> welcl(src, i: (i + 1), hi: m, out: "(cell", names, nsp, nn, strs, ssp, ns) : t |> wc2(a: t, b: ")")

tor welcl {src: []const i64, i: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
welcl = wsk(src, i, hi)
| _ j when j >= hi -> out
| _ j |> wcmx(src, i: j, hi, d: 0, ins: 0, w: 58) : c |> welcl1(src, j, c, hi, out, names, nsp, nn, strs, ssp, ns)

tor welcl1 {src: []const i64, j: i64, c: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
welcl1 = wcmx(src, i: (c + 1), hi, d: 0, ins: 0, w: 44)
| _ m |> welcl2(src, j, c, m, hi, out, names, nsp, nn, strs, ssp, ns)

tor welcl2 {src: []const i64, j: i64, c: i64, m: i64, hi: i64, out: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
welcl2 = wnm(names, nsp, nn, p: j)
| _ nm |> wel(src, lo: (c + 1), hi: m, names, nsp, nn, strs, ssp, ns) : x |> welcl3(src, m, hi, out, nm, x, names, nsp, nn, strs, ssp, ns)

tor welcl3 {src: []const i64, m: i64, hi: i64, out: string, nm: string, x: string, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
welcl3 = wc5(a: out, b: " (", c: nm, d: " ", e: x)
| _ o |> wc3(a: o, b: ")", c: "") : p |> welcl(src, i: (m + 1), hi, out: p, names, nsp, nn, strs, ssp, ns)

tor wrk {rows: []const i64, i: i64, nr: i64} -> i64
wrk = pkb(t: rows, i, n: (nr * 6))
| _ k -> k

tor wevf {nsp: []const i64, nn: i64, lo: i64} -> i64
wevf = wpix(nsp, nn, p: lo)
| _ k when k >= 0 -> (nsp[((@len(nsp) - (3 * nn)) + k)])
| _ _ -> ((0 - 1))

tor wdpe {nsp: []const i64, nn: i64, rows: []const i64, i: i64} -> i64
wdpe = wpix(nsp, nn, p: rows[(i + 2)])
| _ k when k >= 0 -> (if((nsp[((@len(nsp) - nn) + k)] > 1)) 1 else 0)
| _ _ -> 0

tor whi {nsp: []const i64, nn: i64, lo: i64} -> i64
whi = wpix(nsp, nn, p: lo)
| _ k when k >= 0 -> (nsp[((@len(nsp) - (2 * nn)) + k)])
| _ _ -> 0

tor wfdn {rows: []const i64, evi: i64, i: i64, nr: i64} -> i64
wfdn = pkb(t: rows, i: (evi + (i * 6)), n: (nr * 6))
| _ k when k != 2 -> i
| _ _ |> wfdn(rows, evi, i: (i + 1), nr)

tor wfdh {rows: []const i64, evi: i64, src: []const i64, lo: i64, hi: i64, i: i64, nr: i64} -> i64
wfdh = pkb(t: rows, i: (evi + (i * 6)), n: (nr * 6))
| _ k when k != 2 -> 0
| _ _ |> wfdh1(rows, evi, src, lo, hi, i, nr)

tor wfdh1 {rows: []const i64, evi: i64, src: []const i64, lo: i64, hi: i64, i: i64, nr: i64} -> i64
wfdh1 = weq(src, a: rows[((evi + (i * 6)) + 2)], b: rows[((evi + (i * 6)) + 3)], x: lo, y: hi)
| _ v when v == 1 -> 1
| _ _ |> wfdh(rows, evi, src, lo, hi, i: (i + 1), nr)

tor wbr0 {rows: []const i64, evi: i64, i: i64, nr: i64} -> i64
wbr0 = pkb(t: rows, i: (evi + (i * 6)), n: (nr * 6))
| _ k when (k == 2) || (k == 3) |> wbr0(rows, evi, i: (i + 1), nr)
| _ _ -> ((evi + (i * 6)))

tor wbrn {rows: []const i64, evi: i64, nr: i64} -> i64
wbrn = wbr0(rows, evi, i: 1, nr)
| _ b |> wbrn1(rows, b, i: 0, nr)

tor wbrn1 {rows: []const i64, b: i64, i: i64, nr: i64} -> i64
wbrn1 = pkb(t: rows, i: (b + (i * 6)), n: (nr * 6))
| _ k when k != 4 -> i
| _ _ |> wbrn1(rows, b, i: (i + 1), nr)

tor wbrh {rows: []const i64, evi: i64, src: []const i64, lo: i64, hi: i64, nr: i64} -> i64
wbrh = wbr0(rows, evi, i: 1, nr)
| _ b |> wbrh1(rows, b, src, lo, hi, i: 0, nr)

tor wbrh1 {rows: []const i64, b: i64, src: []const i64, lo: i64, hi: i64, i: i64, nr: i64} -> i64
wbrh1 = pkb(t: rows, i: (b + (i * 6)), n: (nr * 6))
| _ k when k != 4 -> 0
| _ _ |> wbrh2(rows, b, src, lo, hi, i, nr)

tor wbrh2 {rows: []const i64, b: i64, src: []const i64, lo: i64, hi: i64, i: i64, nr: i64} -> i64
wbrh2 = weq(src, a: rows[((b + (i * 6)) + 2)], b: rows[((b + (i * 6)) + 3)], x: lo, y: hi)
| _ v when v == 1 -> 1
| _ _ |> wbrh1(rows, b, src, lo, hi, i: (i + 1), nr)

tor wrp {k: i64} -> string
wrp = wn0()
| _ _ when k <= 0 -> ""
| _ _ |> wrp1(k)

tor wrp1 {k: i64} -> string
wrp1 = wrp(k: (k - 1))
| _ t |> wc2(a: ")", b: t)

tor wclo {inf: i64, iopen: i64, curk: i64, dep: i64} -> string
wclo = wn0()
| _ _ when inf == 0 -> ""
| _ _ |> wcloa(iopen, curk, dep)

tor wcloa {iopen: i64, curk: i64, dep: i64} -> string
wcloa = wrp(k: (iopen + (if((curk != 0)) (1 + (dep * 2)) else 0)))
| _ a |> wc3(a: if((curk == (0 - 1))) " (node terminal)" else "", b: a, c: "))")

tor wcls {iopen: i64, curk: i64, dep: i64} -> string
wcls = wn0()
| _ _ when curk == 0 |> wrp(k: iopen)
| _ _ when curk == (0 - 1) |> wrp(k: ((iopen + 1) + (dep * 2))) : p |> wc2(a: " (node terminal)", b: p)
| _ _ |> wrp(k: ((iopen + 1) + (dep * 2)))

tor wex {src: []const i64, lo: i64, hi: i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64} -> string
wex = wtb(src, lo, j: (hi - 1), n: hi)
| _ b |> wsk(src, i: lo, hi: b) : a |> wev(lv: 1, src, lo: a, hi: b, names, nsp, nn, strs, ssp, ns)

tor wpun {src: []const i64, lo: i64, hi: i64, nsp: []const i64, nn: i64} -> i64
wpun = wtb(src, lo, j: (hi - 1), n: hi)
| _ b |> wsk(src, i: lo, hi: b) : a |> wpun1(src, a, b, nsp, nn)

tor wpun1 {src: []const i64, a: i64, b: i64, nsp: []const i64, nn: i64} -> i64
wpun1 = wne(nsp, nn, p: a)
| _ e when e == b -> a
| _ _ |> wfd(src, i: a, hi: b, d: 0, ins: 0, last: (0 - 1)) : f |> wpun2(src, b, f, nsp, nn)

tor wpun2 {src: []const i64, b: i64, f: i64, nsp: []const i64, nn: i64} -> i64
wpun2 = wne(nsp, nn, p: (f + 1))
| _ e when (f >= 0) && (e == b) |> wpun3(src, f)
| _ _ -> ((0 - 1))

tor wpun3 {src: []const i64, f: i64} -> i64
wpun3 = pkb(t: src, i: (f - 1), n: @len(src))
| _ c |> wpun3b(c, f)

tor wpun3b {c: i64, f: i64} -> i64
wpun3b = wpe(c)
| _ _ -> ((f + 1))

tor wdk {nsp: []const i64, nn: i64, ltk: i64, ltl: i64, lth: i64, htl: i64, hth: i64, fevi: i64} -> i64
wdk = wn0()
| _ _ when (ltk == 1) || (ltk == 2) |> wevf(nsp, nn, lo: ltl)
| _ _ when ltk == 3 |> wevf(nsp, nn, lo: htl)
| _ _ -> fevi

tor warg {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64, ltk: i64, ltl: i64, lth: i64, htl: i64, hth: i64, argi: i64, fevi: i64} -> string
warg = wex(src, lo: rows[(i + 4)], hi: rows[(i + 5)], names, nsp, nn, strs, ssp, ns)
| _ e |> wdk(nsp, nn, ltk, ltl, lth, htl, hth, fevi) : d |> warg1(rows, nr, src, names, nsp, nn, i, d, argi, e)

tor warg1 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, d: i64, argi: i64, e: string} -> string
warg1 = wn0()
| _ _ when rows[(i + 2)] > 0 |> warg2(rows, nr, src, names, nsp, nn, i, d, e)
| _ _ |> wpun(src, lo: rows[(i + 4)], hi: rows[(i + 5)], nsp, nn) : p |> warg3(rows, nr, src, names, nsp, nn, i, d, argi, e, p)

tor warg2 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, d: i64, e: string} -> string
warg2 = wfdh(rows, evi: d, src, lo: rows[(i + 2)], hi: rows[(i + 3)], i: 1, nr)
| _ h when (d < 0) || (h == 1) |> warg2a(rows, names, nsp, nn, i, e)
| _ _ -> "(bad decl-param)"

tor warg2a {rows: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, e: string} -> string
warg2a = wnm(names, nsp, nn, p: rows[(i + 2)])
| _ nm |> wc5(a: " (", b: nm, c: " ", d: e, e: ")")

tor warg3 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, d: i64, argi: i64, e: string, p: i64} -> string
warg3 = wne(nsp, nn, p)
| _ pe |> warg3a(rows, nr, src, names, nsp, nn, i, d, argi, e, p, pe)

tor warg3a {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, d: i64, argi: i64, e: string, p: i64, pe: i64} -> string
warg3a = wfdh(rows, evi: d, src, lo: p, hi: pe, i: 1, nr)
| _ h when (p >= 0) && ((d < 0) || (h == 1)) |> wnm(names, nsp, nn, p) : nm |> wc5(a: " (", b: nm, c: " ", d: e, e: ")")
| _ _ |> warg4(rows, nr, src, names, nsp, nn, d, argi, e)

tor warg4 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, d: i64, argi: i64, e: string} -> string
warg4 = wn0()
| _ _ when d >= 0 |> warg5(rows, nr, src, names, nsp, nn, d, argi, e)
| _ _ -> "(bad arg-name)"

tor warg5 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, d: i64, argi: i64, e: string} -> string
warg5 = wfdn(rows, evi: d, i: 1, nr)
| _ n when (argi + 1) < n |> wnm(names, nsp, nn, p: rows[((d + ((argi + 1) * 6)) + 2)]) : nm |> wc5(a: " (", b: nm, c: " ", d: e, e: ")")
| _ _ -> "(bad arg-name)"

tor whev {nsp: []const i64, nn: i64, rows: []const i64, i: i64} -> string
whev = wdpe(nsp, nn, rows, i)
| _ d -> (if((d == 1)) " (bad dup-tor)" else "")

tor whim {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64} -> string
whim = wex(src, lo: rows[(i + 4)], hi: rows[(i + 5)], names, nsp, nn, strs, ssp, ns)
| _ e |> wnm(names, nsp, nn, p: rows[(i + 2)]) : nm |> wc7(a: " (def ", b: nm, c: " (bare ", d: e, e: "))", f: "", g: "")

tor whfw {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, plbl: i64} -> string
whfw = wnm(names, nsp, nn, p: rows[(i + 2)])
| _ nm |> whfw1(names, nsp, nn, plbl, nm)

tor whfw1 {names: []const string, nsp: []const i64, nn: i64, plbl: i64, nm: string} -> string
whfw1 = wn0()
| _ _ when plbl >= 0 |> wnm(names, nsp, nn, p: plbl) : lb |> wc5(a: " (def ", b: nm, c: " (subflow", d: (" (label " ++ (lb ++ ")")), e: "")
| _ _ |> wc5(a: " (def ", b: nm, c: " (subflow", d: "", e: "")

tor whca {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64} -> string
whca = wnm(names, nsp, nn, p: rows[(i + 2)])
| _ nm |> wc3(a: " (head ", b: nm, c: "")

tor whco {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, fevi: i64} -> string
whco = wbrh(rows, evi: fevi, src, lo: rows[(i + 2)], hi: rows[(i + 3)], nr)
| _ b |> wbrn(rows, evi: fevi, nr) : n |> whco1(rows, names, nsp, nn, i, fevi, b, n)

tor whco1 {rows: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, fevi: i64, b: i64, n: i64} -> string
whco1 = wnm(names, nsp, nn, p: rows[(i + 2)])
| _ nm -> (if((((fevi >= 0) && (n > 0)) && (b == 0))) " (bad decl-branch)" else (" (arm (tag " ++ (nm ++ ")")))

tor whbi {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64} -> string
whbi = wnm(names, nsp, nn, p: rows[(i + 2)])
| _ nm |> wc3(a: " (bind ", b: nm, c: ")")

tor whcn {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64} -> string
whcn = wex(src, lo: rows[(i + 2)], hi: rows[(i + 3)], names, nsp, nn, strs, ssp, ns)
| _ e |> wc3(a: " (when ", b: e, c: ")")

tor whct {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64, fevi: i64, nr: i64} -> string
whct = wbrh(rows, evi: fevi, src, lo: rows[(i + 2)], hi: rows[(i + 3)], nr)
| _ b |> whct1(rows, src, names, nsp, nn, strs, ssp, ns, i, fevi, b)

tor whct1 {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64, fevi: i64, b: i64} -> string
whct1 = wnm(names, nsp, nn, p: rows[(i + 2)])
| _ _ when (fevi >= 0) && (b == 0) -> "(bad ctor-branch)"
| _ nm |> whct2(rows, src, names, nsp, nn, strs, ssp, ns, i, nm)

tor whct2 {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64, nm: string} -> string
whct2 = wtb(src, lo: rows[(i + 4)], j: (rows[(i + 5)] - 1), n: rows[(i + 5)])
| _ be when rows[(i + 4)] < be |> wex(src, lo: rows[(i + 4)], hi: be, names, nsp, nn, strs, ssp, ns) : x |> wc7(a: " (node (ctor ", b: nm, c: " ", d: x, e: "))", f: "", g: "")
| _ _ |> wc7(a: " (node (ctor ", b: nm, c: " ", d: "(lit (cell))", e: "))", f: "", g: "")

tor wsti {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, curk: i64, pend: i64, flbl: i64, flbh: i64, jump: i64} -> string
wsti = wnm(names, nsp, nn, p: rows[(i + 2)])
| _ nm |> wsti1(rows, src, names, nsp, nn, i, curk, pend, flbl, flbh, jump, nm)

tor wsti1 {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, curk: i64, pend: i64, flbl: i64, flbh: i64, jump: i64, nm: string} -> string
wsti1 = weq(src, a: flbl, b: flbh, x: rows[(i + 2)], y: rows[(i + 3)])
| _ j when (jump == 1) && (j == 0) -> "(bad jump-label)"
| _ _ |> wsti2(curk, pend, jump, nm, names, nsp, nn)

tor wsti2 {curk: i64, pend: i64, jump: i64, nm: string, names: []const string, nsp: []const i64, nn: i64} -> string
wsti2 = wn0()
| _ _ when pend >= 0 |> wnm(names, nsp, nn, p: pend) : b |> wsti3(curk, pend, jump, nm, b)
| _ _ |> wsti3(curk, pend, jump, nm, b: "")

tor wsti3 {curk: i64, pend: i64, jump: i64, nm: string, b: string} -> string
wsti3 = wn0()
| _ _ when (curk == 0) && (pend >= 0) -> ((" (arm (tag _chain) (bind " ++ (b ++ (") (node (" ++ ((if((jump == 1)) "jump " else "invoke ") ++ nm)))))
| _ _ when curk == 0 -> ((" (arm (tag _chain) (node (" ++ ((if((jump == 1)) "jump " else "invoke ") ++ nm)))
| _ _ when ((curk == 3) || (curk == 4)) && (pend >= 0) -> ((")) (conts (arm (tag _chain) (bind " ++ (b ++ (") (node (" ++ ((if((jump == 1)) "jump " else "invoke ") ++ nm)))))
| _ _ when (curk == 3) || (curk == 4) -> ((")) (conts (arm (tag _chain) (node (" ++ ((if((jump == 1)) "jump " else "invoke ") ++ nm)))
| _ _ -> ((" (node (" ++ ((if((jump == 1)) "jump " else "invoke ") ++ nm)))

tor wfin {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, out: string, inf: i64, iopen: i64, curk: i64, dep: i64, pend: i64} -> string
wfin = wn0()
| _ _ when pend >= 0 -> ((out ++ "(bad pend)"))
| _ _ |> wclo(inf, iopen, curk, dep) : c |> wfin1(rows, nr, src, names, nsp, nn, out, c)

tor wfin1 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, out: string, c: string} -> string
wfin1 = wth(rows, nr, src, names, nsp, nn, i: 0, out: (out ++ c))
| _ t |> wc2(a: t, b: ")")

tor wth {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, out: string} -> string
wth = wrk(rows, i, nr)
| _ _ when i >= (nr * 6) -> out
| _ k when k == 1 |> wthi(rows, nr, src, names, nsp, nn, i, out)
| _ _ |> wth(rows, nr, src, names, nsp, nn, i: (i + 6), out)

tor wthi {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, out: string} -> string
wthi = whi(nsp, nn, lo: rows[(i + 2)])
| _ h |> wnm(names, nsp, nn, p: rows[(i + 2)]) : nm |> wthi1(rows, nr, src, names, nsp, nn, i, out, h, nm)

tor wthi1 {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, i: i64, out: string, h: i64, nm: string} -> string
wthi1 = wc5(a: out, b: if((h == 1)) "" else " (def ", c: if((h == 1)) "" else nm, d: if((h == 1)) "" else " thunk)", e: "")
| _ o |> wth(rows, nr, src, names, nsp, nn, i: (i + 6), out: o)

tor w-wk {rows: []const i64, nr: i64, src: []const i64, names: []const string, nsp: []const i64, nn: i64, strs: []const string, ssp: []const i64, ns: i64, i: i64, out: string, dead: i64, inev: i64, inf: i64, iopen: i64, ltk: i64, ltl: i64, lth: i64, htl: i64, hth: i64, argi: i64, curk: i64, ctk: i64, dep: i64, pend: i64, plbl: i64, ple: i64, flbl: i64, flbh: i64, fevi: i64, ano: i64} -> string
w-wk = wrk(rows, i, nr)
| _ _ when i >= (nr * 6) |> wfin(rows, nr, src, names, nsp, nn, out, inf, iopen, curk, dep, pend)
| _ k when k == 17 |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad wire-bad)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 1) |> wclo(inf, iopen, curk, dep) : c |> whev(nsp, nn, rows, i) : t |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (c ++ t)), dead: if((t == " (bad dup-tor)")) 1 else dead, inev: 1, inf: 0, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: 0, ctk: 0, dep: 0, pend, plbl, ple, flbl, flbh, fevi: (0 - 1), ano: 0)
| _ k when (dead == 0) && (k == 2) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (if((inev == 0)) "(bad fld-out)" else "")), dead: if((inev == 0)) 1 else dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 3) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (if((inev == 0)) "(bad ret-out)" else "")), dead: if((inev == 0)) 1 else dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 4) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (if((inev == 0)) "(bad brd-out)" else "")), dead: if((inev == 0)) 1 else dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 5) |> wclo(inf, iopen, curk, dep) : c |> whim(rows, src, names, nsp, nn, strs, ssp, ns, i) : t |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (c ++ t)), dead, inev: 0, inf: 0, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: 0, ctk: 0, dep: 0, pend, plbl, ple, flbl, flbh, fevi: (0 - 1), ano: 0)
| _ k when (dead == 0) && (k == 6) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out, dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl: rows[(i + 2)], ple: rows[(i + 3)], flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 7)) && (pend >= 0) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad pend)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 7) |> wclo(inf, iopen, curk, dep) : c |> whfw(rows, src, names, nsp, nn, i, plbl) : t |> wevf(nsp, nn, lo: rows[(i + 2)]) : f |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (c ++ t)), dead, inev: 0, inf: 1, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: 0, ctk: 0, dep: 0, pend: (0 - 1), plbl: (0 - 1), ple: (0 - 1), flbl: plbl, flbh: ple, fevi: f, ano: 0)
| _ k when ((dead == 0) && (k == 8)) && ((inf == 0) || (ltk != 0)) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad head)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 8) |> whca(rows, src, names, nsp, nn, i) : t |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead, inev, inf, iopen: 1, ltk: 1, ltl: rows[(i + 2)], lth: rows[(i + 3)], htl: rows[(i + 2)], hth: rows[(i + 3)], argi: 0, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 9)) && (iopen == 0) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad arg)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 9) |> warg(rows, nr, src, names, nsp, nn, strs, ssp, ns, i, ltk, ltl, lth, htl, hth, argi, fevi) : t |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi: (argi + 1), curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 10)) && (ltk == 0) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad rbind)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 10) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out, dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend: rows[(i + 2)], plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 11)) && (inf == 0) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad cont)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 11)) && (pend >= 0) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad pend)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 11)) && (ano == 1) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad chain-scope)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 11) |> wcls(iopen, curk, dep) : c |> wevf(nsp, nn, lo: htl) : d |> whco(rows, nr, src, names, nsp, nn, i, fevi: d) : t |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ (c ++ t)), dead: if((t == " (bad decl-branch)")) 1 else dead, inev, inf, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: (0 - 1), ctk: 0, dep: 0, pend: (0 - 1), plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 12)) && (curk == 0) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad bind)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 12) |> whbi(rows, src, names, nsp, nn, i) : t |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 13)) && (curk == 0) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad cond)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 13) |> whcn(rows, src, names, nsp, nn, strs, ssp, ns, i) : t |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (((dead == 0) && (k == 14)) && (rows[(i + 1)] == 1)) && ((curk != (0 - 1)) || (inf == 0)) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad step-expr)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 14)) && (rows[(i + 1)] == 1) |> wex(src, lo: rows[(i + 2)], hi: rows[(i + 3)], names, nsp, nn, strs, ssp, ns) : e |> wc5(a: " (node (produce ", b: e, c: ")", d: ")", e: "") : t |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead, inev, inf, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: 1, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (((dead == 0) && (k == 14)) && (rows[(i + 1)] == 2)) && (((curk == 1) || (curk == 2)) || (curk == 5)) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad chain-after)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 14)) && (rows[(i + 1)] == 2) |> wsti(rows, src, names, nsp, nn, i, curk, pend, flbl, flbh, jump: 0) : t |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead: if((t == "(bad jump-label)")) 1 else dead, inev, inf, iopen: 2, ltk: 2, ltl: rows[(i + 2)], lth: rows[(i + 3)], htl, hth, argi: 0, curk: if((curk == 0)) 3 else if((curk == (0 - 1))) 3 else curk, ctk: 3, dep: if(((curk == 3) || (curk == 4))) (dep + 1) else dep, pend: (0 - 1), plbl, ple, flbl, flbh, fevi, ano: if((curk == 0)) 1 else ano)
| _ k when (((dead == 0) && (k == 14)) && (rows[(i + 1)] == 3)) && (((curk == 1) || (curk == 2)) || (curk == 5)) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad chain-after)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when ((dead == 0) && (k == 14)) && (rows[(i + 1)] == 3) |> wsti(rows, src, names, nsp, nn, i, curk, pend, flbl, flbh, jump: 1) : t |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead: if((t == "(bad jump-label)")) 1 else dead, inev, inf, iopen: 2, ltk: 3, ltl: rows[(i + 2)], lth: rows[(i + 3)], htl, hth, argi: 0, curk: if((curk == 0)) 4 else if((curk == (0 - 1))) 4 else curk, ctk: 4, dep: if(((curk == 3) || (curk == 4))) (dep + 1) else dep, pend: (0 - 1), plbl, ple, flbl, flbh, fevi, ano: if((curk == 0)) 1 else ano)
| _ k when ((dead == 0) && (k == 15)) && ((curk != (0 - 1)) || (inf == 0)) |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ "(bad ctor)"), dead: 1, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 15) |> whct(rows, src, names, nsp, nn, strs, ssp, ns, i, fevi, nr) : t |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ t), dead: if((t == "(bad ctor-branch)")) 1 else dead, inev, inf, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: 2, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ k when (dead == 0) && (k == 16) |> wclo(inf, iopen, curk, dep) : c |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out: (out ++ c), dead, inev: 0, inf: 0, iopen: 0, ltk: 0, ltl, lth, htl, hth, argi: 0, curk: 0, ctk: 0, dep: 0, pend: (0 - 1), plbl, ple, flbl, flbh, fevi: (0 - 1), ano: 0)
| _ _ when dead == 1 |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out, dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)
| _ _ |> w-wk(rows, nr, src, names, nsp, nn, strs, ssp, ns, i: (i + 6), out, dead, inev, inf, iopen, ltk, ltl, lth, htl, hth, argi, curk, ctk, dep, pend, plbl, ple, flbl, flbh, fevi, ano)

tor w-main {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, strs: []const string, ssp: []const i64} -> string
w-main = w-wk(rows, nr: (@len(rows) / 6), src, names, nsp, nn: @len(names), strs, ssp, ns: @len(strs), i: 0, out: "(graph", dead: 0, inev: 0, inf: 0, iopen: 0, ltk: 0, ltl: 0, lth: 0, htl: 0, hth: 0, argi: 0, curk: 0, ctk: 0, dep: 0, pend: (0 - 1), plbl: (0 - 1), ple: (0 - 1), flbl: (0 - 1), flbh: (0 - 1), fevi: (0 - 1), ano: 0)
| _ g -> g

tor main {rows: []const i64, src: []const i64, names: []const string, nsp: []const i64, strs: []const string, ssp: []const i64} -> string
main = w-main(rows, src, names, nsp, strs, ssp)
| _ r -> r