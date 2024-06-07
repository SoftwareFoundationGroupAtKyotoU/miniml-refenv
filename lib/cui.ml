open Syntax

let read_term (input: string): Term.t =
  Parser.toplevel Lexer.main (Lexing.from_string input)

let%test_module "read term" = (module struct
  let op a c b = Term.(App(App(Const(c), a), b))

  let%test_unit "bool literal" =
  [%test_result: Term.t]
    (read_term "true")
    ~expect:Term.(Bool true);
  [%test_result: Term.t]
    (read_term "false")
    ~expect:Term.(Bool false)

  let%test_unit "int literal" =
  [%test_result: Term.t]
    (read_term "10")
    ~expect:Term.(Int 10);
  [%test_result: Term.t]
    (read_term "-10")
    ~expect:Term.(Int(-10));
  [%test_result: Term.t]
    (read_term "00")
    ~expect:Term.(Int(0))

  let%test_unit "arith" =
    [%test_result: Term.t]
      (read_term "1 + 2")
      ~expect:Term.(op (Int 1) Const.Plus (Int 2));
    [%test_result: Term.t]
      (read_term "1 + 2 + 3")
      ~expect:Term.(op (op (Int 1) Const.Plus (Int 2)) Const.Plus (Int 3));
    [%test_result: Term.t]
      (read_term "1 - 2")
      ~expect:Term.(op (Int 1) Const.Minus (Int 2));
    [%test_result: Term.t]
      (read_term "1 - 2 - 3")
      ~expect:Term.(op (op (Int 1) Const.Minus (Int 2)) Const.Minus (Int 3));
    [%test_result: Term.t]
      (read_term "1 + 2 - 3")
      ~expect:Term.(op (op (Int 1) Const.Plus (Int 2)) Const.Minus (Int 3));
    [%test_result: Term.t]
      (read_term "1 * 2")
      ~expect:Term.(op (Int 1) Const.Mult (Int 2));
    [%test_result: Term.t]
      (read_term "1 * 2 + 3")
      ~expect:Term.(op (op (Int 1) Const.Mult (Int 2)) Const.Plus (Int 3));
    [%test_result: Term.t]
      (read_term "1 + 2 * 3")
      ~expect:Term.(op (Int 1) Const.Plus (op (Int 2) Const.Mult (Int 3)))

  let%test_unit "comparizon" =
    [%test_result: Term.t]
      (read_term "1 < 2")
      ~expect:Term.(op (Int 1) Const.LT (Int 2));
    [%test_result: Term.t]
      (read_term "1 + 2 < 3 * 4")
      ~expect:Term.(op (op (Int 1) Const.Plus (Int 2)) Const.LT (op (Int 3) Const.Mult (Int 4)))

  let%test_unit "logical operators" =
    [%test_result: Term.t]
      (read_term "true && false")
      ~expect:Term.(op (Bool true) Const.And (Bool false));
    [%test_result: Term.t]
      (read_term "true || false")
      ~expect:Term.(op (Bool true) Const.Or (Bool false));
    [%test_result: Term.t]
      (read_term "true || false && true")
      ~expect:Term.(op (Bool true) Const.Or (op (Bool false) Const.And (Bool true)));
    [%test_result: Term.t]
      (read_term "1 < 2 && false")
      ~expect:Term.(op (op (Int 1) Const.LT (Int 2)) Const.And (Bool false))

  let%test_unit "variable" =
    [%test_result: Term.t]
      (read_term "x")
      ~expect:Term.(Var(Var.from_string("x")));
    [%test_result: Term.t]
      (read_term "x12")
      ~expect:Term.(Var(Var.from_string("x12")));
    [%test_result: Term.t]
      (read_term "x12__12y")
      ~expect:Term.(Var(Var.from_string("x12__12y")))

  let%test_unit "function" =
    [%test_result: Term.t]
      (read_term "fun(x:int@g1) -> { x + 1 }")
      ~expect:Term.(Lam(Var.from_string "x",
                        Typ.BaseInt,
                        Cls.from_string "g1",
                        (op (Var(Var.from_string "x")) Const.Plus (Int 1))));
    let subject = (read_term "fun(x:int) -> { x+1 }") in
    match subject with
    | Lam(v, ty, _, tm) -> (
        [%test_eq: Var.t] v (Var.from_string "x");
        [%test_eq: Typ.t] ty Typ.BaseInt;
        [%test_eq: Term.t] tm (op (Var(Var.from_string "x")) Const.Plus (Int 1));
      )
    | _ -> failwith "boom"

    let%test_unit "app" =
    [%test_result: Term.t]
      (read_term "1 + f x")
      ~expect:Term.(op (Int 1) Const.Plus (App(Var(Var.from_string "f"),Var(Var.from_string "x"))));
    [%test_result: Term.t]
      (read_term "if true then 1 else f 1")
      ~expect:Term.(If(Bool(true), Int(1), App(Var(Var.from_string("f")), Int(1))));
    [%test_result: Term.t]
      (read_term "fun(x:int@g1)->{ f } 2 3")
      ~expect:Term.(App(App(Lam(Var.from_string "x",
                                Typ.BaseInt,
                                Cls.from_string "g1",
                                Var(Var.from_string "f")),
                            Int(2)),
                        Int(3)))

  let%test_unit "if statement" =
    [%test_result: Term.t]
      (read_term "if true then 1 else 2")
      ~expect:Term.(If(Bool(true), Int(1), Int(2)));
    [%test_result: Term.t]
      (read_term "if true then 1 else 2 + 1")
      ~expect:Term.(If(Bool(true), Int(1),
                      op (Int 2) Const.Plus (Int 1)))

  let%test_unit "paren" =
    [%test_result: Term.t]
      (read_term "(1)")
      ~expect:Term.(Int(1));
    [%test_result: Term.t]
      (read_term "1 + (2 + 3)")
      ~expect:Term.(App(App(Const(Const.Plus), Int(1)),(App(App(Const(Const.Plus), Int(2)),Int(3)));))

end)

let read_typ (input: string): Typ.t =
  Parser.toplevel_typ Lexer.main (Lexing.from_string input)

let%test_module "read type" = (module struct
  let%test_unit "base types" =
  [%test_result: Typ.t]
    (read_typ "bool")
    ~expect:Typ.BaseBool;
  [%test_result: Typ.t]
    (read_typ "int")
    ~expect:Typ.BaseInt;
  [%test_result: Typ.t]
    (read_typ "int -> int")
    ~expect:Typ.(Func(BaseInt, BaseInt))

end)
