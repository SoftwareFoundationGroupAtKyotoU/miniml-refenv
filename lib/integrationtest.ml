open Base
open Syntax

let%test_unit "hoge" =
  [%test_result: Typ.t option]
    ({|
        fun(x:<int@!>) ->
          `[_:>!]{
            if 0 < 1 + ~x
            then ~x * 10
            else 0
          }
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer Context.empty)
    ~expect:(Option.Some("<int@!>-><int@!>" |> Cui.read_typ));
  [%test_result: Typ.t option]
    ({|
        fun(f:[g1:>!]<int@g1>-><int@g1>) ->
          `[_:>!]{ fun(x:int@g2) -> ~{ f@@g2 `[_:>g2]{x} }}
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer Context.empty)
    ~expect:(Option.Some("([g1:>!]<int@g1>-><int@g1>)-><int->int@!>" |> Cui.read_typ));
  [%test_result: Typ.t option]
    ({|
        let f[g1:>!](x:<int@g1>) : <int@g1>
          = `[_:>g1]{ 1 + ~x } in
        fun (y:int@g2) -> ~0{ f@@g2 `[_:>g2]{ y } }
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer Context.empty)
    ~expect:(Option.Some("int -> int" |> Cui.read_typ));
  [%test_result: Typ.t option]
    ({|
         let rec spow[g1:>!](n:int)(x:<int@g1>):<int@g1> =
           if n < 1 then
             `[_:>g1]{ 1 }
           else
             `[_:>g1]{ ~x * ~{spow@@g1 (n - 1) x}} in
         spow@@! 4 `[_:>!]{ 3 }
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer Context.empty)
    ~expect:(Option.Some("<int@!>" |> Cui.read_typ))

let%test_unit "big test cases" =
  let subject = Cui.read_term {|
      let rec spower_[g:>!](n:int)(xq:<int@g>)(cont:[h:>g]<int@h>-><int@h>):<int@g> =
        if n == 0 then
          cont@@g `[_:>g]{ 1 }
        else if n == 1 then
          cont@@g xq
        else if n mod 2 == 1 then
          spower_@@g (n - 1) xq
            (fun[g1:>g](yq:<int@g1>) -> cont@@g1 `[_:>g1]{~xq * ~yq})
        else
          `[_:>g] {
            let x2:int@g2 = ~xq * ~xq in
            ~{
              spower_@@g2 (n / 2) `[_:>g2]{x2}
                (fun[g3:>g2](yq:<int@g3>) -> cont@@g3 yq)
            }
          } in
      let spower(n:int):<int->int@!> =
        `[_:>!]{ fun(x:int@g)->
           ~{ spower_@@g n `[_:>g]{x} (fun[g1:>g](y:<int@g1>) -> y) }
        } in
      ~0{spower 11} 2
|} in
  [%test_result: Typ.t option]
    (Typechecker.typeinfer Context.empty subject)
    ~expect:(Option.Some(BaseInt))
