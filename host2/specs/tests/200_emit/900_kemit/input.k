// kemit.k — the C99 compiler as a koru program (generated)
// arg-less invoke refuses: `src` unbound; the emit leg
// supplies it via --emit (quote of the source program)
tor emit {src: program} -> string
emit = ident(x: src)
| go s when (s.tag == 30) && ((@len(s.kids) == 3) && ((@len(s.kids[0]) == 1) && ((s.kids[0][0].name == "main") && ((s.kids[1] == "main") && ((@len(s.kids[2]) == 0) && ((s.kids[0][0].v.tag == 27) && (@len(s.kids[0][0].v.kids) == 1))))))) |> render(e: s.kids[0][0].v.kids[0]) : c |> wrap(c)

tor render {e: expr} -> string
render = tag-num(e)
| lit t when (t == 8) && (e.kids[0].tag == 1) -> @intToString(e.kids[0].kids[0])
| bin t when t == 10 |> op-str(n: e.kids[0]) : op |> render(e: e.kids[1]) : l |> render(e: e.kids[2]) : r |> join4(l, op, r)
| un t when (t == 11) && (e.kids[0] == 0) |> render(e: e.kids[1]) : s |> paren-neg(s)

tor op-str {n: i64} -> string
op-str = idnum(x: n)
| add m when m == 0 -> "+"
| sub m when m == 1 -> "-"
| mul m when m == 2 -> "*"
| div m when m == 3 -> "/"
| mod m when m == 4 -> "%"

tor ident {x: program} -> program
ident -> x

tor tag-num {e: expr} -> i64
tag-num -> (e.tag)

tor idnum {x: i64} -> i64
idnum -> x

tor join4 {l: string, op: string, r: string} -> string
join4 -> (("(" ++ (l ++ (" " ++ (op ++ (" " ++ (r ++ ")")))))))

tor paren-neg {s: string} -> string
paren-neg -> (("(-" ++ (s ++ ")")))

tor wrap {c: string} -> string
wrap -> (("int main(void) { return " ++ (c ++ "; }")))
