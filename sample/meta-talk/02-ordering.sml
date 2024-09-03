let x : <int@!> = `{@! 1 } in

`{@!
  (* let introduce a new classifier g
   * and current classifier is g
   * g -> y : int
   *)
  let y : int @ g = 10 in

  (* when performing ~x,
   * we want to check that ! <: g holds (= g is bigger env than !)
   * ! (env of code in x) -> empty
   * g (current env)      -> y : int
   *)
  ~x + y
}
