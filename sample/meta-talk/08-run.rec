let rec spower_[g:>!](n:int)(xq:<int@g>): <int@g> @ h =
  if n == 0 then
    `{@g 1 }
  else if n == 1 then
    xq
  else
    `{@g ~xq * ~{spower_@@g (n - 1) xq} } in

let spower(n:int): <int->int@!> =
  `{@! fun (x:int@g1) -> ~{spower_@@g1 n `{@g1 x}}} in

(* One can evaluate code at runtime as long as classifiers are consistent.
 * unquote can carry index, how many stages to shift (defaults to 1 if omitted)
 * This case, (spower 5) has type <int@!> and the current classifier is h.
 * ! <: h and hence this unquote type-checks.
 *)

~0{ spower 5 } 3
(* spower 5 = `{@! fun (x:int) -> x * x * x * x * x }
 * evaluates to a closure fun (x:int) -> x * x * x * x * x
 *)

