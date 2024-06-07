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
  let subject = Cui.read_term "fun(x:int) -> { 0 < x }" in
  [%test_eq: Typ.t option]
    (Typechecker.typeinfer Context.empty subject)
    (Option.Some(Typ.(Func(BaseInt, BaseBool))));
  let subject = Cui.read_term "`[g1:>!]{ 1 + 2 }" in
  [%test_eq: Typ.t option]
    (Typechecker.typeinfer Context.empty subject)
    (Option.Some(Typ.(Code(Cls.init, BaseInt))));

