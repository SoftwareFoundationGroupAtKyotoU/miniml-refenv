(* There is another form of CSP what we call cross-stage definitions.
 * It is natural to assume that library functions are shared across stages.
 * `let cs` can provide similar functionality.
 *)
let cs sqr(x:int) : int@g1 = x * x in

let rec spower_[g2 :> g1](n : int)(xq : <int@g2>) : <int@g2> @ g3 =
  if n == 0 then
    `{@g2 1 }
  else if n == 1 then
    xq
  else if n mod 2 == 1 then
   `{@g2 ~xq * ~{spower_@@g2 (n - 1) xq }}
  else
   `{@g2 sqr ~{spower_@@g2 (n / 2) xq} } in

let spower(n:int) : <int->int@g1> =
  `{@g1 fun(x:int@g3) -> ~{spower_@@g3 n `{@g3 x }}} in

spower 5
(* evaluates to

  `{@g1 fun(x:int) -> x * sqr (sqr x) }

  and cross-stage definition will be copied over, resulting

  `{@!
      let cs sqr(x:int) : int@g1 = x * x in
      fun(x:int) -> x * sqr (sqr x)
   }

  (* note that classifier has changed from g1 to ! *)
*)
