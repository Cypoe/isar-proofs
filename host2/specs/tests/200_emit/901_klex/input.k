// klex.k — a koru-spelled sexpr lexer over char codes (generated)
// chars arrives as (arr int) on the wire; the host does
// bytes->codes.  arg-less invoke refuses: `chars` unbound.
tor peek {chars: []const i64, i: i64, n: i64} -> i64
peek -> (if((i >= n)) (0 - 1) else chars[i])

tor lex {chars: []const i64, i: i64, n: i64, out: string} -> string
lex = peek(chars, i, n)
| fin c when c < 0 -> out
| ws c when (c == 32) || ((c == 9) || ((c == 10) || (c == 13))) |> lex(chars, i: (i + 1), n, out)
| lp c when c == 40 |> lex(chars, i: (i + 1), n, out: (out ++ "(lparen) "))
| rp c when c == 41 |> lex(chars, i: (i + 1), n, out: (out ++ "(rparen) "))
| op c when (c == 43) || ((c == 42) || (c == 47)) |> lex(chars, i: (i + 1), n, out: (out ++ ("(op " ++ (@intToString(c) ++ ") "))))
| dg c when (c >= 48) && (c <= 57) |> digits(chars, j: i, n, v: 0, out)
| at c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> atom-end(chars, i, j: i, n, out)
| bad c -> ((out ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ") "))))))

tor digits {chars: []const i64, j: i64, n: i64, v: i64, out: string} -> string
digits = peek(chars, i: j, n)
| more c when (c >= 48) && (c <= 57) |> digits(chars, j: (j + 1), n, v: ((v * 10) + (c - 48)), out)
| stop |> lex(chars, i: j, n, out: (out ++ ("(num " ++ (@intToString(v) ++ ") "))))

tor atom-end {chars: []const i64, i: i64, j: i64, n: i64, out: string} -> string
atom-end = peek(chars, i: j, n)
| more c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> atom-end(chars, i, j: (j + 1), n, out)
| stop |> lex(chars, i: j, n, out: (out ++ ("(atom " ++ (@intToString(i) ++ (" " ++ (@intToString((j - i)) ++ ") "))))))

tor main {chars: []const i64} -> string
main = lex(chars, i: 0, n: @len(chars), out: "")
| done s -> s
