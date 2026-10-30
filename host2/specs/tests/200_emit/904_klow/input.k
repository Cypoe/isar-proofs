// klow.k — a koru-spelled reifier → program.ast.json (generated)
// flat six-int rows + source bytes in; escaped JSON text
// out (span bytes as \u00xx).  arg-less invoke refuses:
// `src`/`rows`/`mod` unbound.
tor pkb {t: []const i64, i: i64, n: i64} -> i64
pkb -> (if(((i < 0) || (i >= n))) (0 - 1) else t[i])

tor lxt {src: []const i64, i: i64, hi: i64, d: i64, ins: i64} -> i64
lxt = pkb(t: src, i, n: hi)
| fin c when c < 0 -> hi
| ql c when (ins == 1) && (c == 34) |> lxt(src, i: (i + 1), hi, d, ins: 0)
| bs c when (ins == 1) && (c == 92) |> lxt(src, i: (i + 2), hi, d, ins)
| iq _ when ins == 1 |> lxt(src, i: (i + 1), hi, d, ins)
| qo c when c == 34 |> lxt(src, i: (i + 1), hi, d, ins: 1)
| dop c when (c == 40) || ((c == 91) || (c == 123)) |> lxt(src, i: (i + 1), hi, d: (d + 1), ins)
| dcl c when (c == 41) || ((c == 93) || (c == 125)) |> lxt(src, i: (i + 1), hi, d: (d - 1), ins)
| oo c when (d == 0) && ((c == 124) && (((i + 1) < hi) && (src[(i + 1)] == 124))) |> lxt(src, i: (i + 2), hi, d, ins)
| ob c when (d == 0) && ((c == 124) && ((i > 0) && (src[(i - 1)] == 124))) |> lxt(src, i: (i + 1), hi, d, ins)
| pp c when (d == 0) && (c == 124) -> i
| aw c when (d == 0) && (((c == 61) || (c == 45)) && (((i + 1) < hi) && (src[(i + 1)] == 62))) -> i
| cm c when (d == 0) && ((c == 47) && (((i + 1) < hi) && (src[(i + 1)] == 47))) -> i
| mo _ |> lxt(src, i: (i + 1), hi, d, ins)

tor ltma {src: []const i64, i: i64, hi: i64} -> i64
ltma = pkb(t: src, i, n: hi)
| ws c when (c == 32) || ((c == 9) || ((c == 10) || (c == 13))) |> ltma(src, i: (i + 1), hi)
| dn _ -> i

tor ltmb {src: []const i64, lo: i64, j: i64, n: i64} -> i64
ltmb = pkb(t: src, i: j, n)
| ws c when (j >= lo) && ((c == 32) || ((c == 9) || ((c == 10) || (c == 13)))) |> ltmb(src, lo, j: (j - 1), n)
| dn _ -> ((j + 1))

tor ltk1 {src: []const i64, i: i64, hi: i64} -> i64
ltk1 = pkb(t: src, i, n: hi)
| fin c when c < 0 -> hi
| ct c when (c == 47) && (((i + 1) < hi) && (src[(i + 1)] == 47)) -> i
| ws c when (c == 32) || ((c == 9) || ((c == 10) || (c == 13))) -> i
| mo _ |> ltk1(src, i: (i + 1), hi)

tor lty1 {src: []const i64, i: i64, hi: i64} -> i64
lty1 = pkb(t: src, i, n: hi)
| fin c when c < 0 -> hi
| ct c when (c == 47) && (((i + 1) < hi) && (src[(i + 1)] == 47)) -> i
| mo _ |> lty1(src, i: (i + 1), hi)

tor ltm2 {src: []const i64, lo: i64, j: i64, n: i64} -> i64
ltm2 = pkb(t: src, i: j, n)
| ws c when (j >= lo) && ((c == 32) || (c == 9)) |> ltm2(src, lo, j: (j - 1), n)
| dn _ -> ((j + 1))

tor lln {src: []const i64, i: i64, off: i64, n: i64, l: i64} -> i64
lln = pkb(t: src, i, n)
| fin c when (i >= off) || (c < 0) -> l
| nl c when c == 10 |> lln(src, i: (i + 1), off, n, l: (l + 1))
| ch _ |> lln(src, i: (i + 1), off, n, l)

tor lbs {src: []const i64, i: i64, n: i64} -> i64
lbs = pkb(t: src, i: (i - 1), n)
| nl c when (i <= 0) || (c == 10) -> i
| ch _ |> lbs(src, i: (i - 1), n)

tor lpb {src: []const i64, i: i64, ls: i64, j: i64, n: i64} -> i64
lpb = pkb(t: src, i, n)
| pb c when ((i + 4) <= j) && ((c == 112) && ((src[(i + 1)] == 117) && ((src[(i + 2)] == 98) && (((src[(i + 3)] == 32) || (src[(i + 3)] == 9)) && ((i == ls) || ((src[(i - 1)] == 32) || (src[(i - 1)] == 9))))))) -> 1
| nx _ when i < j |> lpb(src, i: (i + 1), ls, j, n)
| no _ -> 0

tor lpub {src: []const i64, j: i64, n: i64} -> i64
lpub = lbs(src, i: j, n)
| s ls |> lpb(src, i: ls, ls, j, n)

tor lhx {d: i64} -> string
lhx -> (if((d < 10)) @intToString(d) else if((d == 10)) "a" else if((d == 11)) "b" else if((d == 12)) "c" else if((d == 13)) "d" else if((d == 14)) "e" else "f")

tor escl {src: []const i64, i: i64, hi: i64, out: string} -> string
escl = pkb(t: src, i, n: hi)
| fin c when c < 0 -> out
| ch c when c <= 127 |> esca(src, i, hi, out, c)

tor esca {src: []const i64, i: i64, hi: i64, out: string, c: i64} -> string
esca = lhx(d: (c / 16))
| hd a |> escb(src, i, hi, out, c, a)

tor escb {src: []const i64, i: i64, hi: i64, out: string, c: i64, a: string} -> string
escb = lhx(d: (c % 16))
| hd b |> escl(src, i: (i + 1), hi, out: (out ++ ("\\u00" ++ (a ++ b))))

tor escx {src: []const i64, lo: i64, hi: i64, n: i64, out: string} -> string
escx = lxt(src, i: lo, hi, d: 0, ins: 0)
| cut c |> escx1(src, lo, xt: c, n, out)

tor escx1 {src: []const i64, lo: i64, xt: i64, n: i64, out: string} -> string
escx1 = ltma(src, i: lo, hi: xt)
| at a |> escx2(src, a, xt, n, out)

tor escx2 {src: []const i64, a: i64, xt: i64, n: i64, out: string} -> string
escx2 = ltmb(src, lo: a, j: (xt - 1), n)
| bt b |> escl(src, i: a, hi: b, out)

tor esct {src: []const i64, lo: i64, hi: i64, n: i64, out: string} -> string
esct = ltmb(src, lo, j: (hi - 1), n)
| tb b |> esct1(src, lo, b, n, out)

tor esct1 {src: []const i64, lo: i64, b: i64, n: i64, out: string} -> string
esct1 = ltk1(src, i: lo, hi: b)
| ct c |> escl(src, i: lo, hi: c, out)

tor escty {src: []const i64, lo: i64, hi: i64, n: i64, out: string} -> string
escty = ltmb(src, lo, j: (hi - 1), n)
| tb b |> escty1(src, lo, b, n, out)

tor escty1 {src: []const i64, lo: i64, b: i64, n: i64, out: string} -> string
escty1 = lty1(src, i: lo, hi: b)
| ct c |> escty2(src, lo, c, n, out)

tor escty2 {src: []const i64, lo: i64, c: i64, n: i64, out: string} -> string
escty2 = ltm2(src, lo, j: (c - 1), n)
| db d |> escl(src, i: lo, hi: d, out)

tor lcls {dp: i64, mod: []const i64, fln: i64, nmod: i64, out: string} -> string
lcls = pkb(t: mod, i: 0, n: nmod)
| done _ when dp == 0 -> out
| more _ |> lclsm(dp, mod, fln, nmod, out)

tor lclsm {dp: i64, mod: []const i64, fln: i64, nmod: i64, out: string} -> string
lclsm = escl(src: mod, i: 0, hi: nmod, out: (out ++ "],\"location\":{\"file\":\""))
| md e |> lclsn(dp, mod, fln, nmod, out: e)

tor lclsn {dp: i64, mod: []const i64, fln: i64, nmod: i64, out: string} -> string
lclsn = pkb(t: mod, i: 0, n: nmod)
| go _ |> lcls(dp: (dp - 1), mod, fln, nmod, out: (out ++ ("\",\"line\":" ++ (@intToString(fln) ++ ",\"col\":0}}"))))

tor ltail {mod: []const i64, nmod: i64, out: string} -> string
ltail = escl(src: mod, i: 0, hi: nmod, out: (out ++ "],\"main_module_name\":\""))
| done e -> ((e ++ "\",\"parts\":[]}"))

tor limp {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
limp = esct(src, lo: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], n: @len(src), out: (out ++ ",{\"import_decl\":{\"path\":\""))
| p e |> limp2(rows, i, n, src, mod, out: e, p0, p1)

tor limp2 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
limp2 = esct(src, lo: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], n: @len(src), out: (out ++ "\",\"local_name\":\""))
| p e |> limpm(rows, i, n, src, mod, out: e, p0, p1)

tor limpm {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
limpm = escl(src: mod, i: 0, hi: @len(mod), out: (out ++ "\",\"module\":\""))
| p e |> ltop(rows, i: (i + 1), n, src, mod, out: (e ++ "\"}}"), p0, p1, q0: (0 - 1))

tor limpl {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
limpl = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ ",{\"immediate_impl\":{\"event_path\":{\"module_qualifier\":null,\"segments\":[\""))
| p e |> limpl2(rows, i, n, src, mod, out: e, p0, p1)

tor limpl2 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
limpl2 = escx(src, lo: rows[((i * 6) + 4)], hi: rows[((i * 6) + 5)], n: @len(src), out: (out ++ "\"]},\"value\":{\"branch_name\":\"\",\"fields\":[],\"plain_value\":\""))
| p e |> limplm(rows, i, n, src, mod, out: e, p0, p1)

tor limplm {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
limplm = escl(src: mod, i: 0, hi: @len(mod), out: (out ++ "\",\"has_expressions\":true,\"is_bare_return\":true},\"annotations\":[],\"module\":\""))
| p e |> ltop(rows, i: (i + 1), n, src, mod, out: (e ++ "\",\"is_impl\":false}}"), p0, p1, q0: (0 - 1))

tor levo {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
levo = lpub(src, j: rows[((i * 6) + 2)], n: @len(src))
| pb evp |> levoe(rows, i, n, src, mod, out, evp, p0, p1)

tor levoe {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, evp: i64, p0: i64, p1: i64} -> string
levoe = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ ",{\"event_decl\":{\"path\":{\"module_qualifier\":null,\"segments\":[\""))
| p e |> levf(rows, i: (i + 1), n, src, mod, out: (e ++ "\"]},\"input\":{\"fields\":["), ff: 0, bf: 0, r0: (0 - 1), r1: (0 - 1), evp, p0, p1)

tor levf {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, ff: i64, bf: i64, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
levf = pkb(t: rows, i: (i * 6), n)
| fld k when (k == 2) && (((rows[((i * 6) + 2)] >= 0) && (rows[((i * 6) + 3)] >= rows[((i * 6) + 2)])) && (rows[((i * 6) + 3)] <= @len(src))) |> lfld(rows, i, n, src, mod, out, ff, r0, r1, evp, p0, p1)
| ret k when (k == 3) && (((rows[((i * 6) + 2)] >= 0) && (rows[((i * 6) + 3)] >= rows[((i * 6) + 2)])) && (rows[((i * 6) + 3)] <= @len(src))) |> levf(rows, i: (i + 1), n, src, mod, out, ff, bf, r0: rows[((i * 6) + 2)], r1: rows[((i * 6) + 3)], evp, p0, p1)
| brf k when (k == 4) && ((bf == 0) && (((rows[((i * 6) + 2)] >= 0) && (rows[((i * 6) + 3)] >= rows[((i * 6) + 2)])) && (rows[((i * 6) + 3)] <= @len(src)))) |> lbrdf(rows, i, n, src, mod, out, r0, r1, evp, p0, p1)
| brn k when (k == 4) && ((bf == 1) && (((rows[((i * 6) + 2)] >= 0) && (rows[((i * 6) + 3)] >= rows[((i * 6) + 2)])) && (rows[((i * 6) + 3)] <= @len(src)))) |> lbrdn(rows, i, n, src, mod, out, r0, r1, evp, p0, p1)
| clo _ when bf == 0 |> levcc(rows, i, n, src, mod, out, r0, r1, evp, p0, p1)
| clb _ when bf == 1 |> levcc2(rows, i, n, src, mod, out, r0, r1, evp, p0, p1)

tor lfld {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, ff: i64, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
lfld = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ ((if((ff == 1)) "," else "") ++ "{\"name\":\"")))
| p e |> lfldn(rows, i, n, src, mod, out: e, r0, r1, evp, p0, p1)

tor lfldn {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
lfldn = escty(src, lo: rows[((i * 6) + 4)], hi: rows[((i * 6) + 5)], n: @len(src), out: (out ++ "\",\"type\":\""))
| p e |> levf(rows, i: (i + 1), n, src, mod, out: (e ++ "\",\"module_path\":null,\"phantom\":null,\"is_source\":false,\"is_file\":false,\"is_embed_file\":false,\"is_expression\":false,\"is_invocation_meta\":false,\"expression\":null,\"expression_str\":null,\"owns_expression\":false,\"default\":null}"), ff: 1, bf: 0, r0, r1, evp, p0, p1)

tor lbrdf {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
lbrdf = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ "],\"is_wildcard\":false},\"branches\":[{\"name\":\""))
| p e |> levf(rows, i: (i + 1), n, src, mod, out: (e ++ "\",\"kind\":\"terminal\",\"resume\":null,\"resume_phantom\":null,\"is_optional\":false,\"is_panic\":false,\"payload\":{\"fields\":[]}}"), ff: 1, bf: 1, r0, r1, evp, p0, p1)

tor lbrdn {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
lbrdn = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ ",{\"name\":\""))
| p e |> levf(rows, i: (i + 1), n, src, mod, out: (e ++ "\",\"kind\":\"terminal\",\"resume\":null,\"resume_phantom\":null,\"is_optional\":false,\"is_panic\":false,\"payload\":{\"fields\":[]}}"), ff: 1, bf: 1, r0, r1, evp, p0, p1)

tor levcc {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
levcc = pkb(t: src, i: r0, n: @len(src))
| hasr _ when r0 >= 0 |> levc1(rows, i, n, src, mod, out: (out ++ "],\"is_wildcard\":false},\"branches\":[],\"return_type\":\""), r0, r1, evp, p0, p1)
| nor _ |> levcm(rows, i, n, src, mod, out: (out ++ "],\"is_wildcard\":false},\"branches\":[],\"return_type\":null"), evp, p0, p1)

tor levcc2 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
levcc2 = pkb(t: src, i: r0, n: @len(src))
| hasr _ when r0 >= 0 |> levc1(rows, i, n, src, mod, out: (out ++ "],\"return_type\":\""), r0, r1, evp, p0, p1)
| nor _ |> levcm(rows, i, n, src, mod, out: (out ++ "],\"return_type\":null"), evp, p0, p1)

tor levc1 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, r0: i64, r1: i64, evp: i64, p0: i64, p1: i64} -> string
levc1 = esct(src, lo: r0, hi: r1, n: @len(src), out)
| t e |> levcm(rows, i, n, src, mod, out: (e ++ "\""), evp, p0, p1)

tor levcm {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, evp: i64, p0: i64, p1: i64} -> string
levcm = escl(src: mod, i: 0, hi: @len(mod), out: (out ++ (",\"return_phantom\":null,\"is_public\":" ++ ((if((evp == 1)) "true" else "false") ++ ",\"is_implicit_flow\":false,\"annotations\":[],\"prose\":\"\",\"is_pure\":false,\"is_transitively_pure\":false,\"module\":\""))))
| m e |> ltop(rows, i, n, src, mod, out: (e ++ "\"}}"), p0, p1, q0: (0 - 1))

tor lflw {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64} -> string
lflw = lln(src, i: 0, off: rows[((i * 6) + 2)], n: @len(src), l: 1)
| ln l |> lhead(rows, i: (i + 1), n, src, mod, out: (out ++ ",{\"flow\":{\"invocation\":"), f0: rows[((i * 6) + 2)], f1: rows[((i * 6) + 3)], fln: l, k4: 0, pr0: p0, pr1: p1, q0: (0 - 1), q1: (0 - 1), dp: 0, af: 0, cs: 0, hn: 0)

tor lhead {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lhead = pkb(t: rows, i: (i * 6), n)
| call k when (k == 8) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> lcall(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor lcall {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lcall = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ "{\"event\":[\""))
| e v |> linv(rows, i: (i + 1), n, src, mod, out: (v ++ "\"],\"args\":["), f0, f1, fln, k4: if((rows[((i * 6) + 2)] == f0)) 1 else 0, pr0, pr1, q0, q1, dp, af, cs, hn, wh: 0, as: 0)

tor linv {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, wh: i64, as: i64} -> string
linv = pkb(t: rows, i: (i * 6), n)
| arg k when (k == 9) && ((rows[((i * 6) + 4)] >= 0) && ((rows[((i * 6) + 4)] >= 0) && ((rows[((i * 6) + 5)] >= rows[((i * 6) + 4)]) && (rows[((i * 6) + 5)] <= @len(src))))) |> larg(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh, as)
| rb k when (k == 10) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> lrb(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh)
| oth _ |> lconts(rows, i, n, src, mod, out: (out ++ ("],\"variant\":null,\"return_binding\":null" ++ ((if((wh == 1)) "}}" else "}") ++ ",\"continuations\":["))), f0, f1, fln, k4, pr0, pr1, q0, q1, dp: (dp + 1), af: 0, cs: if((wh == 1)) 1 else 0, hn)

tor larg {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, wh: i64, as: i64} -> string
larg = pkb(t: src, i: rows[((i * 6) + 2)], n: @len(src))
| nm _ when rows[((i * 6) + 2)] > 0 |> largn(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh, as)
| ps _ |> largp(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh, as)

tor largn {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, wh: i64, as: i64} -> string
largn = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ ((if((as == 1)) "," else "") ++ "{\"name\":\"")))
| nm e |> largm(rows, i, n, src, mod, out: (e ++ "\",\"value\":\""), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh)

tor largp {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, wh: i64, as: i64} -> string
largp = escx(src, lo: rows[((i * 6) + 4)], hi: rows[((i * 6) + 5)], n: @len(src), out: (out ++ ((if((as == 1)) "," else "") ++ "{\"name\":\"\",\"value\":\"")))
| v e |> linv(rows, i: (i + 1), n, src, mod, out: (e ++ "\"}"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh, as: 1)

tor largm {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, wh: i64} -> string
largm = escx(src, lo: rows[((i * 6) + 4)], hi: rows[((i * 6) + 5)], n: @len(src), out)
| v e |> linv(rows, i: (i + 1), n, src, mod, out: (e ++ "\"}"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh, as: 1)

tor lrb {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, wh: i64} -> string
lrb = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ "],\"variant\":null,\"return_binding\":\""))
| e v |> lconts(rows, i: (i + 1), n, src, mod, out: (v ++ ("\"" ++ ((if((wh == 1)) "}}" else "}") ++ ",\"continuations\":["))), f0, f1, fln, k4, pr0, pr1, q0: rows[((i * 6) + 2)], q1: rows[((i * 6) + 3)], dp: (dp + 1), af: 0, cs: if((wh == 1)) 1 else 0, hn)

tor lbind {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lbind = pkb(t: rows, i: (i * 6), n)
| bd k when (k == 12) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> lbd(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| oth _ |> lcond(rows, i, n, src, mod, out: (out ++ "null,\"binding_type\":\"branch_payload\",\"condition\":"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor lbd {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lbd = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ "\""))
| e v |> lcond(rows, i: (i + 1), n, src, mod, out: (v ++ "\",\"binding_type\":\"branch_payload\",\"condition\":"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor lcond {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lcond = pkb(t: rows, i: (i * 6), n)
| cd k when (k == 13) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> lcd(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| oth _ |> lstep(rows, i, n, src, mod, out: (out ++ "null,\"step\":"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor lcd {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lcd = escx(src, lo: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], n: @len(src), out: (out ++ "\""))
| e v |> lstep(rows, i: (i + 1), n, src, mod, out: (v ++ "\",\"step\":"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor lstep {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lstep = pkb(t: rows, i: (i * 6), n)
| se k when (k == 14) && ((rows[((i * 6) + 1)] == 1) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src))))) |> lsxp(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| si k when (k == 14) && (((rows[((i * 6) + 1)] == 2) || (rows[((i * 6) + 1)] == 3)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src))))) |> lsiv(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| ct k when (k == 15) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> lctor(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| oth _ |> lconts(rows, i, n, src, mod, out: (out ++ "{\"type\":\"terminal\"},\"continuations\":["), f0, f1, fln, k4, pr0, pr1, q0, q1, dp: (dp + 1), af: 0, cs: 0, hn)

tor lsxp {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lsxp = escx(src, lo: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], n: @len(src), out: (out ++ "{\"type\":\"produce\",\"plain_value\":\""))
| e v |> lconts(rows, i: (i + 1), n, src, mod, out: (v ++ "\"},\"continuations\":["), f0, f1, fln, k4, pr0, pr1, q0, q1, dp: (dp + 1), af: 0, cs: 0, hn)

tor lsiv {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lsiv = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ ("{\"type\":\"invocation\",\"invocation\":{\"event\":[" ++ (if((rows[((i * 6) + 1)] == 3)) "\"@" else "\""))))
| e v |> linv(rows, i: (i + 1), n, src, mod, out: (v ++ "\"],\"args\":["), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, wh: 1, as: 0)

tor lctor {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lctor = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ "{\"type\":\"branch_constructor\",\"branch_constructor\":{\"branch_name\":\""))
| e v |> lctor1(rows, i, n, src, mod, out: (v ++ "\",\"fields\":[],\"plain_value\":"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor lctor1 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lctor1 = lxt(src, i: rows[((i * 6) + 4)], hi: rows[((i * 6) + 5)], d: 0, ins: 0)
| x xt |> lctor2(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, xt)

tor lctor2 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, xt: i64} -> string
lctor2 = ltma(src, i: rows[((i * 6) + 4)], hi: xt)
| a a |> lctor3(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, xt, a)

tor lctor3 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, xt: i64, a: i64} -> string
lctor3 = ltmb(src, lo: a, j: (xt - 1), n: @len(src))
| b b |> lctor4(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, xt, a, b)

tor lctor4 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, xt: i64, a: i64, b: i64} -> string
lctor4 = pkb(t: src, i: a, n: @len(src))
| has _ when a < b |> lctor5(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn, a, b)
| non _ when (a >= b) && (rows[((i * 6) + 4)] >= xt) |> lconts(rows, i: (i + 1), n, src, mod, out: (out ++ "null,\"has_expressions\":false,\"is_bare_return\":false}},\"continuations\":["), f0, f1, fln, k4, pr0, pr1, q0, q1, dp: (dp + 1), af: 0, cs: 0, hn)

tor lctor5 {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64, a: i64, b: i64} -> string
lctor5 = escl(src, i: a, hi: b, out: (out ++ "\""))
| v e |> lconts(rows, i: (i + 1), n, src, mod, out: (e ++ "\",\"has_expressions\":true,\"is_bare_return\":false}},\"continuations\":["), f0, f1, fln, k4, pr0, pr1, q0, q1, dp: (dp + 1), af: 0, cs: 0, hn)

tor lconts {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lconts = pkb(t: rows, i: (i * 6), n)
| cn k when (k == 11) && (((q0 < 0) && (hn == 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src))))) |> larmc(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| st k when (k == 14) && (((rows[((i * 6) + 1)] == 2) || (rows[((i * 6) + 1)] == 3)) && ((cs == 1) || (((dp == 1) && (af == 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src))))))) |> llink(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| oth _ |> litemc(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor larmc {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
larmc = pkb(t: rows, i: (i * 6), n)
| deep _ when dp > 1 |> larmd(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| shal _ when dp == 1 |> lcarmp(rows, i, n, src, mod, out: (out ++ (if((af == 1)) "," else "")), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor larmd {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
larmd = lcls(dp: (dp - 1), mod, fln, nmod: @len(mod), out)
| e v |> lcarmp(rows, i, n, src, mod, out: (v ++ ","), f0, f1, fln, k4, pr0, pr1, q0, q1, dp: 1, af, cs, hn)

tor lcarmp {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
lcarmp = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out: (out ++ "{\"branch\":\""))
| e v |> lbind(rows, i: (i + 1), n, src, mod, out: (v ++ "\",\"kind\":\"terminal\",\"is_catchall\":false,\"binding\":"), f0, f1, fln, k4, pr0, pr1, q0: (0 - 1), q1: (0 - 1), dp, af, cs: 0, hn)

tor llink {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
llink = pkb(t: src, i: q0, n: @len(src))
| pb _ when q0 >= 0 |> llinkb(rows, i, n, src, mod, out: (out ++ ((if((af == 1)) "," else "") ++ "{\"branch\":\"\",\"kind\":\"terminal\",\"is_catchall\":false,\"binding\":\"")), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| nb _ when q0 < 0 |> llinkn(rows, i, n, src, mod, out: (out ++ ((if((af == 1)) "," else "") ++ "{\"branch\":\"\",\"kind\":\"terminal\",\"is_catchall\":false,\"binding\":null")), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor llinkb {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
llinkb = escl(src, i: q0, hi: q1, out)
| e v |> llinkn(rows, i, n, src, mod, out: (v ++ "\""), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor llinkn {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
llinkn = pkb(t: rows, i: (i * 6), n)
| go _ |> llinke(rows, i, n, src, mod, out: (out ++ (",\"binding_type\":\"branch_payload\",\"condition\":null,\"step\":{\"type\":\"invocation\",\"invocation\":{\"event\":[" ++ (if((rows[((i * 6) + 1)] == 3)) "\"@" else "\""))), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor llinke {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
llinke = escl(src, i: rows[((i * 6) + 2)], hi: rows[((i * 6) + 3)], out)
| e v |> linv(rows, i: (i + 1), n, src, mod, out: (v ++ "\"],\"args\":["), f0, f1, fln, k4, pr0, pr1, q0: (0 - 1), q1: (0 - 1), dp, af, cs, hn: if(((dp == 1) && (af == 0))) 1 else hn, wh: 1, as: 0)

tor litemc {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
litemc = pkb(t: rows, i: (i * 6), n)
| deep _ when dp > 1 |> litemd(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| shal _ when dp == 1 |> litemp(rows, i, n, src, mod, out, f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor litemd {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
litemd = lcls(dp: (dp - 1), mod, fln, nmod: @len(mod), out)
| e v |> litemp(rows, i, n, src, mod, out: v, f0, f1, fln, k4, pr0, pr1, q0, q1, dp: 1, af, cs, hn)

tor litemp {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
litemp = pkb(t: src, i: pr0, n: @len(src))
| f4 _ when k4 == 1 |> liteml(rows, i, n, src, mod, out: (out ++ "],\"pre_label\":null,\"impl_of\":null"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| hp _ when (k4 == 0) && (pr0 >= 0) |> litem3p(rows, i, n, src, mod, out: (out ++ "],\"pre_label\":\""), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)
| np _ when (k4 == 0) && (pr0 < 0) |> litem3i(rows, i, n, src, mod, out: (out ++ "],\"pre_label\":null,\"impl_of\":[\""), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor litem3p {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
litem3p = escl(src, i: pr0, hi: pr1, out)
| e v |> litem3i(rows, i, n, src, mod, out: (v ++ "\",\"impl_of\":[\""), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor litem3i {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
litem3i = escl(src, i: f0, hi: f1, out)
| e v |> liteml(rows, i, n, src, mod, out: (v ++ "\"]"), f0, f1, fln, k4, pr0, pr1, q0, q1, dp, af, cs, hn)

tor liteml {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, f0: i64, f1: i64, fln: i64, k4: i64, pr0: i64, pr1: i64, q0: i64, q1: i64, dp: i64, af: i64, cs: i64, hn: i64} -> string
liteml = escl(src: mod, i: 0, hi: @len(mod), out: (out ++ ",\"location\":{\"file\":\""))
| e v |> ltop(rows, i, n, src, mod, out: (v ++ ("\",\"line\":" ++ (@intToString(fln) ++ ",\"col\":0}}}"))), p0: (0 - 1), p1: (0 - 1), q0)

tor ltop {rows: []const i64, i: i64, n: i64, src: []const i64, mod: []const i64, out: string, p0: i64, p1: i64, q0: i64} -> string
ltop = pkb(t: rows, i: (i * 6), n)
| fin _ when ((i * 6) >= n) && (q0 < 0) |> ltail(mod, nmod: @len(mod), out)
| ev k when ((k == 1) && (q0 < 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> levo(rows, i, n, src, mod, out, p0, p1)
| im k when (((k == 5) && (q0 < 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src))))) && ((rows[((i * 6) + 4)] >= 0) && ((rows[((i * 6) + 5)] >= rows[((i * 6) + 4)]) && (rows[((i * 6) + 5)] <= @len(src)))) |> limpl(rows, i, n, src, mod, out, p0, p1)
| lb k when (k == 6) && (((q0 < 0) && (p0 < 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src))))) |> ltop(rows, i: (i + 1), n, src, mod, out, p0: rows[((i * 6) + 2)], p1: rows[((i * 6) + 3)], q0)
| fw k when ((k == 7) && (q0 < 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> lflw(rows, i, n, src, mod, out, p0, p1)
| ip k when ((k == 16) && (q0 < 0)) && ((rows[((i * 6) + 2)] >= 0) && ((rows[((i * 6) + 3)] >= rows[((i * 6) + 2)]) && (rows[((i * 6) + 3)] <= @len(src)))) |> limp(rows, i, n, src, mod, out, p0, p1)

tor main {src: []const i64, rows: []const i64, mod: []const i64} -> string
main = escl(src: mod, i: 0, hi: @len(mod), out: "{\"module_annotations\":[],\"items\":[{\"import_decl\":{\"path\":\"std/compiler\",\"local_name\":\"std.compiler\",\"module\":\"")
| m e |> ltop(rows, i: 0, n: @len(rows), src, mod, out: (e ++ "\"}}"), p0: (0 - 1), p1: (0 - 1), q0: (0 - 1))