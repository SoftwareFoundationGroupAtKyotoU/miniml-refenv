open Syntax

let read_term (input: string): Term.t =
  Parser.toplevel Lexer.main (Lexing.from_string input)

let%test_module "read term" = (module struct
  let op a c b = Term.(App(App(Const(c), a), b))

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


  let%test_unit "paren" =
    [%test_result: Term.t]
      (read_term "(1)")
      ~expect:Term.(Int(1));
    [%test_result: Term.t]
      (read_term "1 + (2 + 3)")
      ~expect:Term.(App(App(Const(Const.Plus), Int(1)),(App(App(Const(Const.Plus), Int(2)),Int(3)));));

end)

