open Base
open Syntax

let%test_unit "hoge" =
  [%test_result: Typ.t option]
    ({|
        fun(x:<int@!>) ->
          `{@!
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
          `{@! fun(x:int@g2) -> ~{ f@@g2 `{@g2 x } }}
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer Context.empty)
    ~expect:(Option.Some("([g1:>!]<int@g1>-><int@g1>)-><int->int@!>" |> Cui.read_typ));
  [%test_result: Typ.t option]
    ({|
        let f[g1:>!](x:<int@g1>) : <int@g1>
          = `{@g1 1 + ~x } in
        fun (y:int@g2) -> ~0{ f@@g2 `{@g2 y } }
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer Context.empty)
    ~expect:(Option.Some("int -> int" |> Cui.read_typ));
  [%test_result: Typ.t option]
    ({|
         let rec spow[g1:>!](n:int)(x:<int@g1>):<int@g1> =
           if n < 1 then
             `{@g1 1 }
           else
             `{@g1 ~x * ~{spow@@g1 (n - 1) x}} in
         spow@@! 4 `{@! 3 }
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer Context.empty)
    ~expect:(Option.Some("<int@!>" |> Cui.read_typ))

let%test_unit "big test cases" =
  let subject = Cui.read_term {|
      let rec spower_[g:>!](n:int)(xq:<int@g>)(cont:[h:>g]<int@h>-><int@h>):<int@g> =
        if n == 0 then
          cont@@g `{@g 1 }
        else if n == 1 then
          cont@@g xq
        else if n mod 2 == 1 then
          spower_@@g (n - 1) xq
            (fun[g1:>g](yq:<int@g1>) -> cont@@g1 `{@g1 ~xq * ~yq})
        else
          `{@g
            let x2:int@g2 = ~xq * ~xq in
            ~{
              spower_@@g2 (n / 2) `{@g2 x2}
                (fun[g3:>g2](yq:<int@g3>) -> cont@@g3 yq)
            }
          } in
      let spower(n:int):<int->int@!> =
        `{@!
           fun(x:int@g)->
             ~{ spower_@@g n `{@g x } (fun[g1:>g](y:<int@g1>) -> y) }
        } in
      spower 11
     |} in
  [%test_result: Typ.t option]
    (subject |> Typechecker.typeinfer Context.empty)
    ~expect:(Option.Some(Typ.(Code(Cls.init, Func(BaseInt, BaseInt)))));
  [%test_result: Evaluator.Value.t]
    (subject |> Evaluator.eval 0 [] [] (fun x -> x))
    ~expect:(Evaluator.Value.Code(
        {|
         `{@!
            fun (x:int) ->
              let x1:int = x * x in
              let x2:int = x1 * x1 in
              let x3:int = x2 * x2 in
              x * (x1 * x3)
         }
         |} |> Cui.read_term
      ));

  let subject = Cui.read_term {|
      let rec spower_[g:>!](n:int)(xq:<int@g>)(cont:[h:>g]<int@h>-><int@h>):<int@g> =
        if n == 0 then
          cont@@g `{@g 1 }
        else if n == 1 then
          cont@@g xq
        else if n mod 2 == 1 then
          spower_@@g (n - 1) xq
            (fun[g1:>g](yq:<int@g1>) -> cont@@g1 `{@g1 ~xq * ~yq})
        else
          `{@g
            let x2:int@g2 = ~xq * ~xq in
            ~{
              spower_@@g2 (n / 2) `{@g2 x2}
                (fun[g3:>g2](yq:<int@g3>) -> cont@@g3 yq)
            }
          } in
      let spower(n:int):<int->int@!> =
        `{@!
           fun(x:int@g)->
             ~{ spower_@@g n `{@g x } (fun[g1:>g](y:<int@g1>) -> y) }
        } in
      let power(n:int)(x:int@g):int =
        ~0{spower_@@g n `{@g x } (fun[g1:>g](y:<int@g1>) -> y)} in
      (~0{spower 11} 2) + (power 11 2)
  |} in
  [%test_result: Typ.t option]
    (subject |> Typechecker.typeinfer Context.empty)
    ~expect:(Option.Some(BaseInt));
  [%test_result: Evaluator.Value.t]
    (subject |> Evaluator.eval 0 [] [] (fun x -> x))
    ~expect:(Evaluator.Value.Int(4096));
