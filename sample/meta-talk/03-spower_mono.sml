(* spower_ specializes power function *)
let rec spower_ (n : int)(xq : <int@!>): <int@!> =
  if n == 0 then
    `{@! 1 }
  else if n == 1 then
    xq
  else
    `{@! ~xq * ~{spower_ (n - 1) xq} } in

spower_ 5 `{@! 3 }
(* will generate
   `{@! 3 * 3 * 3 * 3 * 3 }
*)
