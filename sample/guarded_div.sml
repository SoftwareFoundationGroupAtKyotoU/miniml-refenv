let assert_locus[g1:>!](
  f: ref (<int->int@g1> -> <int->int@g1>) -> <int->int@g1>
): <int->int@g1> =
  let r: ref (<int->int@g1> -> <int->int@g1>) = ref (fun (x: <int->int@g1>) -> x) in
  let c: <int->int@g1> = f r in
  let transformer: <int->int@g1> -> <int->int@g1> = !r in
  transformer c in

let add_assert[g1:>!]
    (locus: ref (<int->int@g1> -> <int->int@g1>))
    (transformer: <int->int@g1> -> <int->int@g1>)
    : unit =
  locus := (
    let oldtr: <int->int@g1> -> <int->int@g1> = !locus in
    fun (x:<int->int@g1>) -> oldtr (transformer x)) in

let guarded_div[g1:>!][g2:>g1]
    (locus: ref (<int->int@g1> -> <int->int@g1>))
    (x: <int@g2>)
    (y: <int@g1>)
    : <int@g2> =
  let () = add_assert@@g1
             locus
             (fun (z:<int->int@g1>) -> `{@g1 if 0 < ~y then ~z else (fun(w:int)->w)}) in
  `{@g2 ~x / ~y} in

`{@!
  let rec fib (n:int): int =
    if n < 2 then 1
    else fib (n - 1) + fib (n - 2) in
  fun (y:int@h1) -> ~{
    assert_locus@@h1 (fun (locus:ref (<int->int@h1> -> <int->int@h1>)) ->
      `{@h1 fun (z:int@h3) -> (fib 100) + ~{guarded_div@@h1@@h3 locus `{@h3 z } `{@h1 y }}})}
}
