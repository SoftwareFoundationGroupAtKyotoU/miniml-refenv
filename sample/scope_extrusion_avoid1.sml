let r: ref <int@!> = ref `{@! 0 } in
let x: <int->int@!> = `{@! fun (y:int@g1) ->
    ~{
      let () = (r := `{@! y }) in
      `{@g1 y }
    }
  } in
!r
