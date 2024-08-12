open Base
open Syntax
open Result

let%test_unit "hoge" =
  [%test_result: (Typ.t, string) Result.t]
    ({|
        fun(x:<int@!>) ->
          `{@!
            if 0 < 1 + ~x
            then ~x * 10
            else 0
          }
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer true Context.empty)
    ~expect:(return ("<int@!>-><int@!>" |> Cui.read_typ));
  [%test_result: (Typ.t, string) Result.t]
    ({|
        fun(f:[g1:>!]<int@g1>-><int@g1>) ->
          `{@! fun(x:int@g2) -> ~{ f@@g2 `{@g2 x } }}
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer true Context.empty)
    ~expect:(return ("([g1:>!]<int@g1>-><int@g1>)-><int->int@!>" |> Cui.read_typ));
  [%test_result: (Typ.t, string) Result.t]
    ({|
        let f[g1:>!](x:<int@g1>) : <int@g1>
          = `{@g1 1 + ~x } in
        fun (y:int@g2) -> ~0{ f@@g2 `{@g2 y } }
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer true Context.empty)
    ~expect:(return ("int -> int" |> Cui.read_typ));
  [%test_result: (Typ.t, string) Result.t]
    ({|
         let rec spow[g1:>!](n:int)(x:<int@g1>):<int@g1> =
           if n < 1 then
             `{@g1 1 }
           else
             `{@g1 ~x * ~{spow@@g1 (n - 1) x}} in
         spow@@! 4 `{@! 3 }
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer true Context.empty)
    ~expect:(return ("<int@!>" |> Cui.read_typ))

let%test_unit "avoidance of scope extrusion" =
  assert (is_error
    ({|
      let r: <int@!> = ref `{@! 0 } in
      let x: <int->int@!> = `{@! fun (x:int@g1) ->
          ~{
            let () = r := `{@! x } in
            `{@g1 x }
          }
        } in
      !r
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer true Context.empty)
  );
  assert (is_error ({|
      let r: <int@!> = ref `{@! 0 } in
      let x: <int->int@!> = `{@! fun (x:int@g1) ->
          ~{
            let () = r := `{@g1 x } in
            `{@g1 x }
          }
        } in
      !r
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer true Context.empty));
  assert (is_error ({|
      let r: <int@!> = ref `{@g1 0 } in
      let x: <int->int@!> = `{@! fun (x:int@g1) ->
          ~{
            let () = r := `{@g1 x } in
            `{@g1 x }
          }
        } in
      !r
     |}
     |> Cui.read_term
     |> Typechecker.typeinfer true Context.empty))

let%test_unit "nested rename" =
  let _ = "This test case confirms that g1 in f will be properly renamed to !" in
  let subject = Cui.read_term {|
      let f[g1:>!](k : [g2:>g1]<int@g2> -> <int@g2>):<int@g1> = k@@g1 `{@g1 1 } in
        f@@! (fun[g2:>!](x:<int@g2>) -> `{@g2 1 + ~x })
      |} in
  [%test_result: (Typ.t, string) Result.t]
    (subject |> Typechecker.typeinfer true Context.empty)
    ~expect:(return (Typ.(Code(Cls.init, BaseInt))));
  [%test_result: Evalcommon.Value.t]
    (subject |> Evaluator.eval_v)
    ~expect:(Evalcommon.Value.Code(
        "`{@! 1 + 1 }"  |> Cui.read_term
      ))

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
  [%test_result: (Typ.t, string) Result.t]
    (subject |> Typechecker.typeinfer true Context.empty)
    ~expect:(return (Typ.(Code(Cls.init, Func(BaseInt, BaseInt)))));
  [%test_result: Evalcommon.Value.t]
    (subject |> Evaluator.eval_v)
    ~expect:(Evalcommon.Value.Code(
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
  [%test_result: (Typ.t, string) Result.t]
    (subject |> Typechecker.typeinfer true Context.empty)
    ~expect:(return (Typ.BaseInt));
  [%test_result: Evalcommon.Value.t]
    (subject |> Evaluator.eval_v)
    ~expect:(Evalcommon.Value.Int(4096))

  let%test_unit "big test cases" =
    let subject = Cui.read_term
        {|
           let assert_locus[g1:>!](
             f: ref (<int->int@g1> -> <int->int@g1>) -> <int->int@g1>
           ): <int->int@g1> =
             let r: ref (<int->int@g1> -> <int->int@g1>) = ref (fun (x: <int->int@g1>) -> x) in
             let c: <int->int@g1> = f r in
             let transformer: <int->int@g1> -> <int->int@g1> = !r in
             transformer c in

           let add_assert[g1:>!]
               (locus: ref (<int->int@g1> -> <int->int@g1>))
               (transformer: <int->int@g1> -> <int->int@g1>)
               : unit =
             locus := (
               let oldtr: <int->int@g1> -> <int->int@g1> = !locus in
               fun (x:<int->int@g1>) -> oldtr (transformer x)) in

           let guarded_div[g1:>!][g2:>g1]
               (locus: ref (<int->int@g1> -> <int->int@g1>))
               (x: <int@g2>)
               (y: <int@g1>)
               : <int@g2> =
             let () = add_assert@@g1
                        locus
                        (fun (z:<int->int@g1>) -> `{@g1 if 0 < ~y then ~z else (fun(w:int)->w)}) in
             `{@g2 ~x / ~y} in

          `{@!
             let rec fib (n:int): int =
               if n < 2 then 1
               else fib (n - 1) + fib (n - 2) in
             fun (y:int@h1) -> ~{
               assert_locus@@h1 (fun (locus:ref (<int->int@h1> -> <int->int@h1>)) ->
                 `{@h1 fun (z:int@h3) -> (fib 100) + ~{guarded_div@@h1@@h3 locus `{@h3 z } `{@h1 y }}})}
           }
     |} in
  [%test_result: (Typ.t, string) Result.t]
    (subject |> Typechecker.typeinfer true Context.empty)
    ~expect:(return (Typ.(Code(Cls.init, Func(BaseInt, Func(BaseInt, BaseInt))))));
  [%test_result: Evalcommon.Value.t]
    (subject |> Evaluator.eval_v)
    ~expect:(Evalcommon.Value.Code(
        {|
           `{@!
             let rec fib (n:int): int =
               if n < 2 then 1
               else fib (n - 1) + fib (n - 2) in
             fun (y:int@h1) -> if 0 < y then (fun (z:int@h3) -> (fib 100) + z / y) else (fun (x:int@h3) -> x)
            }
         |} |> Cui.read_term
      ))
