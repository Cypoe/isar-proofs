// ported from W:\src\koru\examples\lantern\input.k
// The real file drives std/io + app/lantern (light/douse/read) +
// std/kernel lifecycle; those are foreign-callable leaves here —
// declared tors, oracle rows in cases.json. `describe` is verbatim;
// `delve` keeps the guarded-conditional + recursion shape.
tor describe { room: i64 } -> string
describe = cond(expr: room)
| c r when r == 0 -> "a dim alcove"
| c _ -> "a vaulted hall"

tor cond { expr: i64 }
| c i64
| stop

tor print-ln { msg: string }

tor pick { expr: bool }
| then
| else

tor delve { room: i64 }

delve = pick(expr: room > 4)
| then |> print-ln(msg: "You climb back into daylight.")
| else |> describe(room): d |> print-ln(msg: d) |> delve(room: room + 1)
