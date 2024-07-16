fun [g :> !](x:<int@g>) ->
  (* g <: ! need to hold in order to type-check,
   * but ! <: g in fact
   * ! (current env) -> empty
   * g (code in x)   -> (any env)
   *)
  `{@! 1 + ~x }
