(* One can safely store code fragments to mutable state
 * This is famous example of scope extrusion with mutable state
 *)

let r: ref <int@!> = ref `{@! 0 } in

let x: <int->int@!> = `{@! fun (y:int@g1) ->
    ~{
      (* type error at `{@! y }, because y is not available at ! *)
      let () = (r := `{@! y }) in
      `{@g1 y }
    }
  } in

!r
