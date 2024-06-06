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
