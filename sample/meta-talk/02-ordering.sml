let x : <int@!> = `{@! 1 } in

`{@!
  (* let introduce a new classifier g
   * and current classifier is g
   *)
  let y : int @ g = 10 in

  (* ~x type-checks because ! <: g holds *)
  ~x + y
}
