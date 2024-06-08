open Syntax

let read_term (input: string): Term.t =
  Parser.toplevel Lexer.main (Lexing.from_string input)

let%test_module "read term" = (module struct
  let op a c b = Term.(App(App(Const(c), a), b))

  let g1 = Cls.from_string "g1"
  let g2 = Cls.from_string "g2"
  let g3 = Cls.from_string "g3"
  let x = Var.from_string "x"
  let y = Var.from_string "y"
  let f = Var.from_string "f"

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
      (read_term "not false")
      ~expect:Term.(App(Const(Const.Not), Bool(false)));
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
      ~expect:Term.(Var(x));
    [%test_result: Term.t]
      (read_term "x12")
      ~expect:Term.(Var(Var.from_string("x12")));
    [%test_result: Term.t]
      (read_term "x12__12y")
      ~expect:Term.(Var(Var.from_string("x12__12y")))

  let%test_unit "function" =
    [%test_result: Term.t]
      (read_term "fun(x:int@g1) -> x + 1")
      ~expect:Term.(Lam(x, Typ.BaseInt, g1,
                        (op (Var(x)) Const.Plus (Int 1))));
    [%test_result: Term.t]
      (read_term "fun(x:int@g1)(y:bool@g2) -> if y then x else 0")
      ~expect:Term.(Lam(x, Typ.BaseInt, g1, Lam(y, Typ.BaseBool, g2, If(Var(y),Var(x),Int(0)))));
    let subject = (read_term "fun(x:int) -> x + 1") in
    match subject with
    | Lam(v, ty, _, tm) -> (
        [%test_eq: Var.t] v (x);
        [%test_eq: Typ.t] ty Typ.BaseInt;
        [%test_eq: Term.t] tm (op (Var(x)) Const.Plus (Int 1));
      )
    | _ -> failwith "boom"

    let%test_unit "app" =
    [%test_result: Term.t]
      (read_term "1 + f x")
      ~expect:Term.(op (Int 1) Const.Plus (App(Var(f),Var(x))));
    [%test_result: Term.t]
      (read_term "if true then 1 else f 1")
      ~expect:Term.(If(Bool(true), Int(1), App(Var(f), Int(1))));
    [%test_result: Term.t]
      (read_term "fun(x:int@g1)-> f 2")
      ~expect:Term.(Lam(x, Typ.BaseInt, g1, App(Var(f), Int(2))))

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

  let%test_unit "quote" =
    [%test_result: Term.t]
      (read_term "`{@! f 1 }")
      ~expect:Term.(Quo(Cls.init,
                        App(Var(f), Int(1))));
    let subject = read_term "`{@g2 f 1 }" in
    (match subject with
     | Term.Quo (_, _) -> assert(true)
     | _ -> failwith "subject is expected to be a quotation")

  let%test_unit "unquote" =
    [%test_result: Term.t]
      (read_term "~{ f 1 }")
      ~expect:Term.(Unq(1, App(Var(f), Int(1))));
    [%test_result: Term.t]
      (read_term "~0{ f 1 }")
      ~expect:Term.(Unq(0, App(Var(f), Int(1))));
    [%test_result: Term.t]
      (read_term "~10{ f 1 }")
      ~expect:Term.(Unq(10, App(Var(f), Int(1))));
    [%test_result: Term.t]
      (read_term "~x")
      ~expect:Term.(Unq(1, Var(x)));
    [%test_result: Term.t]
      (read_term "~0x")
      ~expect:Term.(Unq(0, Var(x)))

  let%test_unit "polymorphic classifier" =
    [%test_result: Term.t]
      (read_term "fun [g1:>!] -> 1")
      ~expect:Term.(PolyCls(g1, Cls.init, Int(1)));
    [%test_result: Term.t]
      (read_term "fun [g1:>!][g2:>g1](x:<int@g2>@g3) -> 1")
      ~expect:Term.(PolyCls(g1, Cls.init, PolyCls(g2, g1, Lam(x, Typ.(Code(g2,BaseInt)), g3, Int(1)))))


  let%test_unit "classifier application" =
    [%test_result: Term.t]
      (read_term "x @@ g1")
      ~expect:Term.(AppCls(Var(x), Cls.from_string("g1")))

  let%test_unit "let syntax" =
    [%test_result: Term.t]
      (read_term "let x:int@g1 = 1 in x")
      ~expect:Term.(App(Lam(x, BaseInt, g1, Var(x)), Int(1)));
    match (read_term "let x:int = 1 in x") with
    | (App(Lam(xs, ts, _, tms1), tms2)) ->
      [%test_result: Var.t] xs ~expect:x;
      [%test_result: Typ.t] ts ~expect:Typ.BaseInt;
      [%test_result: Term.t] tms1 ~expect:(Term.Var x);
      [%test_result: Term.t]  tms2~expect:(Term.Int 1);
    | _ -> failwith "false"

  let%test_unit "let syntax as function definitions" =
    [%test_result: Term.t]
      (read_term "let f(x:int@g1):int@g2 = x + 1 in f 1")
      ~expect:Term.(App(Lam(f, Typ.(Func(BaseInt, BaseInt)), g2, App(Var(f), Int(1))), Lam(x, BaseInt, g1, op (Var x) Const.Plus (Int 1))));
    [%test_result: Term.t]
      (read_term "let f[g1:>!]:<int@g1>@g2 = `{@g1 1} in f@@!")
      ~expect:Term.(App(Lam(f, Typ.(PolyCls(g1, Cls.init, Code(g1, BaseInt))), g2, AppCls(Var(f), Cls.init)), PolyCls(g1, Cls.init, Quo(g1, Int(1)))));
    [%test_result: Term.t]
      (read_term "let f[g1:>!](x:<int@g1>@g3):<int@g1>@g2 = x in f")
      ~expect:Term.(App(Lam(f, Typ.(PolyCls(g1, Cls.init, Func(Code(g1, BaseInt), Code(g1, BaseInt)))), g2, Var(f)), PolyCls(g1, Cls.init, Lam(x, Code(g1, BaseInt), g3, Var(x)))))

  let%test_unit "let rec syntax" =
    [%test_result: Term.t]
      (read_term {|
         let rec f(x:int@g2):int@g1 = f x in
         f 0
      |})
      ~expect:Term.(App(Lam(f, Typ.(Func(BaseInt, BaseInt)), g1,
                            App(Var(f), Int(0))),
                        Fix(Lam(f, Typ.(Func(BaseInt, BaseInt)), g1,
                                Lam(x, BaseInt, g2, App(Var(f), Var(x)))))))


end)

let read_typ (input: string): Typ.t =
  Parser.toplevel_typ Lexer.main (Lexing.from_string input)

let%test_module "read type" = (module struct
  let g1 = Cls.from_string "g1"

  let%test_unit "base types" =
  [%test_result: Typ.t]
    (read_typ "bool")
    ~expect:Typ.BaseBool;
  [%test_result: Typ.t]
    (read_typ "int")
    ~expect:Typ.BaseInt;
  [%test_result: Typ.t]
    (read_typ "int -> int")
    ~expect:Typ.(Func(BaseInt, BaseInt));
  [%test_result: Typ.t]
    (read_typ "int -> int -> int")
    ~expect:Typ.(Func(BaseInt, Func(BaseInt, BaseInt)));
  [%test_result: Typ.t]
    (read_typ "<int@!>")
    ~expect:Typ.(Code(Cls.init, BaseInt));
  [%test_result: Typ.t]
    (read_typ "[g1:>!]<int@g1>")
    ~expect:Typ.(PolyCls(g1, Cls.init, Code(g1, BaseInt)));
  [%test_result: Typ.t]
    (read_typ "[g1:>!]int->int")
    ~expect:Typ.(PolyCls(g1, Cls.init, Func(BaseInt, BaseInt)));
  [%test_result: Typ.t]
    (read_typ "([g1:>!]int)->int")
    ~expect:Typ.(Func(PolyCls(g1, Cls.init, BaseInt), BaseInt))

end)
