// ported from W:\src\koru\benchmarks\workloads\ — bend-style: multiple
// entries in one file, each a row in cases.json. The real benches use
// std loops/folds; these keep the shape with declared leaf events.
tor step { i: i64 }
| go i64
| done

// sum_range_foldable port: fold 5..1 into acc through a tag dispatch
tor sum-range { n: i64, acc: i64 } -> i64
sum-range = step(i: n)
| go i |> sum-range(n: i - 1, acc: acc + i)
| done -> acc

// fib-shaped accumulation over the same leaf
tor fib-walk { n: i64, a: i64, b: i64 } -> i64
fib-walk = step(i: n)
| go i |> fib-walk(n: i - 1, a: b, b: a + b)
| done -> a
