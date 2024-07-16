let x : <int@!> = `{@! 1 } in

`{@!
  (* let introduce a new classifier g
   * and current classifier is g
   *)
  let y : int @ g = 10 in

  (* ~x type-checks because ! <: g holds
   * ! (env of code in x) -> empty
   * g (current env)      -> y : int
   *)
  ~x + y
}
