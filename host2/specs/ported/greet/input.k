// ported from W:\src\koru\examples\greet\hello.k
// Real file: import std/io, tor greet, greet -> concat, and a
// top-level `greet (name: "World"): msg |> std/io:print.ln(msg)`.
// The top-level flow is out of subset (flows must be impls), so the
// driver wraps it: `run = greet(...): msg |> print-ln(msg)`.
tor greet { name: string } -> string
greet -> "Hello, " ++ name ++ "!"

tor print-ln { msg: string }

run = greet(name: "World"): msg |> print-ln(msg)
