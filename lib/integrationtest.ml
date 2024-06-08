open Base
open Syntax

let%test_unit "hoge" =
  let subject = Cui.read_term "1 + 1" in
  [%test_eq: Typ.t option]
    (Typechecker.typeinfer
       Context.empty
       subject)
    (Option.Some(Typ.BaseInt));
  let subject = Cui.read_term "1 + 2 * 3 - 4 * 111" in
  [%test_eq: Typ.t option]
    (Typechecker.typeinfer
       Context.empty
       subject)
    (Option.Some(Typ.BaseInt));
  let subject = Cui.read_term "1 < 2 - 3" in
  [%test_eq: Typ.t option]
    (Typechecker.typeinfer
       Context.empty
       subject)
    (Option.Some(Typ.BaseBool));
  let subject = Cui.read_term "if 0 < x then y else z * 2" in
  [%test_eq: Typ.t option]
    (Typechecker.typeinfer
       Context.(from [Var(Var.from_string("x"), BaseInt, Cls.alloc());
                      Var(Var.from_string("y"), BaseInt, Cls.alloc());
                      Var(Var.from_string("z"), BaseInt, Cls.alloc())])
       subject)
    (Option.Some(Typ.BaseInt));
  let subject = Cui.read_term "fun(x:int) -> 0 < x" in
  [%test_eq: Typ.t option]
    (Typechecker.typeinfer Context.empty subject)
    (Option.Some(Typ.(Func(BaseInt, BaseBool))));
  let subject = Cui.read_term "fun(x:<int@!>) -> `[_:>!]{1+~x}" in
  [%test_eq: Typ.t option]
    (Typechecker.typeinfer Context.empty subject)
    (Option.Some(Typ.(Func(Code(Cls.init, BaseInt), Code(Cls.init, BaseInt)))));
  let subject = Cui.read_term {|
    fun(f:[g1:>!]<int@g1>-><int@g1>) ->
      `[_:>!]{ fun(x:int@g2) -> ~{ f@@g2 `[_:>g2]{x} }}
|}
  in
  [%test_eq: Typ.t option]
    (Typechecker.typeinfer Context.empty subject)
    (Option.Some(Typ.(Func(PolyCls(Cls.from_string "g1", Cls.init, Func(Code(Cls.from_string "g1", BaseInt), Code(Cls.from_string "g1", BaseInt))), Code(Cls.init, Func(BaseInt, BaseInt))))))

let%test_unit "big test cases" [@tags "disabled"] =
  let subject = Cui.read_term {|
      let rec spower_[g:>!](n:int)(xq:<int@g>)(cont:[h:>g]<int@h>-><int@h>):<int@g> =
        if n == 0 then
          cont@@g `[_:>g]{ 1 }
        else if n == 1 then
          cont@@g xq
        else if n mod 2 == 1 then
          spower_@@g (n-1) xq
            (fun[g1:>g](yq:<int@g1>) -> cont@@g1 `[_:>g1]{~xq * ~yq})
        else
          `[_:>g] {
            let x2:int@g2 = ~xq * ~xq in
            ~{
              spower_@@g2 (n/2) `[_:>g2]{x2}
                (fun[g3:>g2](yq:<int@g3>) -> cont@@g3 yq)
            }
          } in
      let spower(n:int):<int->int@!> =
        `[_:>!]{ fun x:int@g ->
           ~{ spower_@@g n `[_:>g]{x} (fun[g1:>g](y:<int@g1>) -> y) }
        } in
      ~0{spower 11} 2
|} in
  [%test_eq: Typ.t option]
    (Typechecker.typeinfer Context.empty subject)
    (Option.None)
