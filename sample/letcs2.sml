let cs inc(n: int): int @g1 =
  n + 1 in
let rec repapply[h:>g1](n:int)(f: <int->int@h>)(x: <int@h>): <int@h> =
  if n == 0 then x
  else `{@h ~f ~{ repapply@@h (n - 1) f x } }
in
`{@g1
  let x:int@g2 = 10 in
  ~{repapply@@g2 (inc (inc 0)) `{@g2 inc } `{@g2 x }}
}
