let rec spower_ (n : int)(xq : <int@!>): <int@!> =
  if n == 0 then
    `{@! 1 }
  else if n == 1 then
    xq
  else
    `{@! ~xq * ~{spower_ (n - 1) xq} } in

let spower(n : int): <int -> int @ !> =
  (* type error at spower_ n `{@g1 x }
   * `{@g1 x } : <int @ g1> while spower_ accepts <int @ !>
   *)
  `{@! fun (x : int @ g1) -> ~{ spower_ n `{@g1 x }}} in

spower 5
(* we want
 * `{@! fun (x:int) -> x * x * x * x * x }
 *)
