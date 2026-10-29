// ksexp.k — a koru-spelled sexpr parser over char codes (generated)
// explicit-stack parse: depth is the stack register;
// nodes print as (kind start end) spans — no chr/slice.
// arg-less invoke refuses: `chars` unbound.
tor peek {chars: []const i64, i: i64, n: i64} -> i64
peek -> if((i >= n)) (0 - 1) else chars[i]

tor sx {chars: []const i64, i: i64, n: i64, depth: i64, need: i64, seen: i64, out: string} -> string
sx = peek(chars, i, n)
| fin c when c < 0 -> if(((depth == 0) && (seen == 1))) out else ((out ++ (if((need == 1)) " " else "")) ++ ("(bad " ++ (@intToString(n) ++ (" " ++ (@intToString((0 - 1)) ++ ")")))))
| ws c when (c == 32) || ((c == 9) || ((c == 10) || (c == 13))) |> sx(chars, i: (i + 1), n, depth, need, seen, out)
| lp-bad c when (c == 40) && ((depth == 0) && (seen == 1)) -> ((out ++ (if((need == 1)) " " else "")) ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ")")))))
| lp c when c == 40 |> sx(chars, i: (i + 1), n, depth: (depth + 1), need: 0, seen: 1, out: ((out ++ (if((need == 1)) " " else "")) ++ "(seq "))
| rp-bad c when (c == 41) && (depth == 0) -> ((out ++ (if((need == 1)) " " else "")) ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ")")))))
| rp c when c == 41 |> sx(chars, i: (i + 1), n, depth: (depth - 1), need: 1, seen, out: (out ++ ")"))
| tok-bad c when (((c >= 48) && (c <= 57)) || ((((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57)))))) || ((c == 43) || ((c == 42) || (c == 47))))) && (depth == 0) -> ((out ++ (if((need == 1)) " " else "")) ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ")")))))
| dg c when (c >= 48) && (c <= 57) |> num(chars, i, j: i, n, depth, need, seen, out)
| at c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> atom(chars, i, j: i, n, depth, need, seen, out)
| op c when (c == 43) || ((c == 42) || (c == 47)) |> sx(chars, i: (i + 1), n, depth, need: 1, seen, out: ((out ++ (if((need == 1)) " " else "")) ++ ("(op " ++ (@intToString(i) ++ (" " ++ (@intToString((i + 1)) ++ ")"))))))
| bad c -> ((out ++ (if((need == 1)) " " else "")) ++ ("(bad " ++ (@intToString(i) ++ (" " ++ (@intToString(c) ++ ")")))))

tor num {chars: []const i64, i: i64, j: i64, n: i64, depth: i64, need: i64, seen: i64, out: string} -> string
num = peek(chars, i: j, n)
| more c when (c >= 48) && (c <= 57) |> num(chars, i, j: (j + 1), n, depth, need, seen, out)
| stop |> sx(chars, i: j, n, depth, need: 1, seen, out: ((out ++ (if((need == 1)) " " else "")) ++ ("(num " ++ (@intToString(i) ++ (" " ++ (@intToString(j) ++ ")"))))))

tor atom {chars: []const i64, i: i64, j: i64, n: i64, depth: i64, need: i64, seen: i64, out: string} -> string
atom = peek(chars, i: j, n)
| more c when ((c >= 97) && (c <= 122)) || (((c >= 65) && (c <= 90)) || ((c == 95) || ((c == 45) || ((c >= 48) && (c <= 57))))) |> atom(chars, i, j: (j + 1), n, depth, need, seen, out)
| stop |> sx(chars, i: j, n, depth, need: 1, seen, out: ((out ++ (if((need == 1)) " " else "")) ++ ("(atom " ++ (@intToString(i) ++ (" " ++ (@intToString(j) ++ ")"))))))

tor main {chars: []const i64} -> string
main = sx(chars, i: 0, n: @len(chars), depth: 0, need: 0, seen: 0, out: "")
| done s -> s
