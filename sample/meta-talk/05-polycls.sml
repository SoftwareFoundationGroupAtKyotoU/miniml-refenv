(* [g :> !]...  introduces a polymorphic classifier g
 * that has more variables than !
 *)
let rec spower_ [g :> !](n : int)(xq : <int@g>): <int@g> =
  if n == 0 then
    `{@g 1 }
  else if n == 1 then
    xq
  else
    `{@g ~xq * ~{spower_@@g (n - 1) xq } } in

let spower(n : int): <int -> int @ !> =
  (* here polymorphic classifier of spower_ is instanciated
   * with new classifier g1. This type-checks because ! <: g1 holds
   * !  -> empty
   * g1 -> x : int
   *)
  `{@! fun (x : int @ g1) -> ~{spower_@@g1 n `{@g1 x } } } in

spower 5
(* we get
 * `{@! fun (x:int) -> x * x * x * x * x }
 *)

