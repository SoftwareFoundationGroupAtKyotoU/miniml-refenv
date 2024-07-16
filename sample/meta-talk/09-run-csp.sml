(* Let's consider optimized version of spwoer *)
let sqr(x : int) : int @ g1 = x * x in

(* SPOILER: code types can refer to classifiers of run-time environment *)
let rec spower_[g2 :> g1](n : int)(xq : <int@g2>) : <int@g2> @ g3 =
  if n == 0 then
   `{@g2 1 }
  else if n mod 2 == 1 then
   `{@g2 ~xq * ~{spower_@@g2 (n - 1) xq }}
  else
   (* we can use sqr inside quote, (as long as classifier is consistent)
      apparently cross-stage persistence *)
   `{@g2 sqr ~{spower_@@g2 (n / 2) xq} } in

let spower(n : int) : <int -> int @ g1> =
  `{@g1 fun(x:int@g4) -> ~{spower_@@g4 n `{@g4 x }}} in

~0{
  spower 11
  (* evaluates to `{@g1 fun(x:int) -> x * sqr (x * sqr (sqr x)) } *)
} 3
(* And we can perform run-time evaluation on open code!
 * This is safe because sqr is defined at the current env,
 * and it can be confirmed statically
 * g1 (code from (spower 5)) -> sqr:int->int
 * g3 (current classifier)   -> sqr:int->int, spower_:..., spower:...
 *)

