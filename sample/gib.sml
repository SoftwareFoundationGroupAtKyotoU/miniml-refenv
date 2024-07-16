let emptytbl[g1:>!][g2:>g1](n:int)(fail:unit -> <int@g2>)(_:<int@g2> -> <int@g2>): <int@g2> = fail() in
let weaken[g1:>!][g2:>g1](x:<int@g1>):<int@g2> = `{@g2 ~x } in
let ext[g1:>!]
  (tbl: [g2:>g1] int -> (unit -> <int@g2>) -> (<int@g2> -> <int@g2>) -> <int@g2>)
  (newidx: int)
  (newval: <int@g1>)
  : [g2:>g1] int -> (unit -> <int@g2>) -> (<int@g2> -> <int@g2>) -> <int@g2> =
  fun[g2:>g1](idx:int)(fail:unit-><int@g2>)(ok:<int@g2>-><int@g2>) ->
    let newval2: <int@g2> = weaken@@g1@@g2 newval in
    let fallback (_:unit): <int@g2> =
      if idx == newidx
        then (ok newval2)
        else (fail ()) in
    tbl@@g2 idx fallback ok in
let weakmap[g1:>!][g2:>g1]
  (tbl: [g3:>g1] int -> (unit -> <int@g3>) -> (<int@g3> -> <int@g3>) -> <int@g3>)
  : [g3:>g2] int -> (unit -> <int@g3>) -> (<int@g3> -> <int@g3>) -> <int@g3> =
  fun[g3:>g2](idx:int)(fail:unit-><int@g3>)(ok:<int@g3>-><int@g3>) ->
    tbl@@g3 idx fail ok in
let rec gib_st3[g1:>!]
  (tbl:[g2:>g1] int -> (unit -> <int@g2>) -> (<int@g2> -> <int@g2>) -> <int@g2>)
  (n:int)
  (m1:<int@g1>)
  (m2:<int@g1>)
  (k: [g2:>g1] ([g3:>g2] int -> (unit -> <int@g3>) -> (<int@g3> -> <int@g3>) -> <int@g3>) -> <int@g2> -> <int@g2>)
  : <int@g1> =
  tbl@@g1 n
  (fun (_:unit) ->
     if n == 0 then k@@g1 (ext@@g1 tbl 0 m1) m1
     else if n == 1 then k@@g1 (ext@@g1 tbl 1 m2) m2
     else
     gib_st3@@g1 tbl (n - 1) m1 m2
       (fun [h1:>g1]
            (tbl1:[g3:>h1] int -> (unit -> <int@g3>) -> (<int@g3> -> <int@g3>) -> <int@g3>)
            (v1:<int@h1>) ->
              gib_st3@@h1 tbl1 (n - 2) (weaken@@g1@@h1 m1) (weaken@@g1@@h1 m2)
                (fun [h2:>h1]
                     (tbl2: [g3:>h2] int -> (unit -> <int@g3>) -> (<int@g3> -> <int@g3>) -> <int@g3>)
                     (v2:<int@h2>) ->
                 `{@h2
                     let x3:int@h3 = ~v1 + ~v2 in
                      ~{ k@@h3 (ext@@h3 (weakmap@@h2@@h3 tbl2) n `{@h3 x3 }) `{@h3 x3 } }
                  })))
  (fun (v:<int@g1>) -> k@@g1 tbl v) in
gib_st3@@! (emptytbl@@!) 10 `{@! 2 } `{@! 3 }
  (fun[g2:>!](tbl:([g3:>g2] int -> (unit -> <int@g3>) -> (<int@g3> -> <int@g3>) -> <int@g3>))(x:<int@g2>) -> x)
