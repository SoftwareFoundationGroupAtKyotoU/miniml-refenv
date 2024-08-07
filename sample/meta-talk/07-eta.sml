(* Example of higher-order use of polymorphic classifier
 * eta lifts code-to-code function to code of function
 *)
let eta(f: [g1 :> !](<int@g1> -> <int@g1>)): <int -> int @!> =
  `{@! fun(x : int @ g2) -> ~{ f@@g2 `{@g2 x } }} in

eta (fun [g3:>!](y: <int@g3>) -> `{@g3 ~y + 1 })
(* evaluate to `{@! (fun (x:int) -> x + 1) } *)
