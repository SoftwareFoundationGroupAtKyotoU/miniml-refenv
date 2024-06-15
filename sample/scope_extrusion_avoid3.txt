let r: ref <int@g1> = ref `{@g1 0 } in
let x: <int->int@!> = `{@! fun (y:int@g1) ->
    ~{
      let () = r := `{@g1 y } in
      `{@g1 x }
    }
  } in
!r
