open Base
open Syntax
open Evalcommon

module Cont = struct
  type t =
    (* Continuation that takes run-time values *)
    | BinOpL0 of BinOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | BinOpR0 of BinOp.t * Value.t
    | UniOp0 of UniOp.t
    | ShortCircuitOpL0 of ShortCircuitOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppL0 of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppR0 of Value.t
    | RuntimeEval0 of Value.t RuntimeEnv.t * CodeEnv.t
    | Unq0 of int
    | ClsApp0 of Cls.t
    | IfCond0 of Term.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | Fix0
    (* Continuation that takes future-stage values *)
    | Lamf of Var.t * Cls.t * Typ.t
    | AppLf of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppRf of Value.t
    | Quof of Cls.t
    | Unqf of int
    | ClsAbsf of Cls.t * Cls.t
    | ClsAppf of Cls.t
  [@@deriving compare, equal, sexp]
end

module State = struct
  type t =
    | EvalTerm of int * Term.t * Value.t RuntimeEnv.t * CodeEnv.t * (Cont.t list) * Store.t
    | ApplyCont of int * (Cont.t list) * Value.t * Store.t
  [@@deriving compare, equal, sexp]

  let init(tm:Term.t): t = EvalTerm(0, tm, [], [], [], [])
end

type stepResult =
  | InProgress of State.t
  | Done of Value.t * Store.t

let describe (state: State.t): unit =
  Printf.sprintf !"State: %{sexp:State.t}" state
  |> Stdio.print_endline

let run ?(debug=false) (state: State.t): Value.t * Store.t =
  let step (state: State.t): stepResult =
    if debug then describe state;
    match (state : State.t) with
    | State.EvalTerm (lv, tm, renv, cenv, cont, store) ->
      if Int.equal lv 0 then
        (match tm with
         (* Already a value *)
         | Term.Int i -> InProgress(State.ApplyCont(lv, cont, Value.Int i, store))
         | Term.Bool b -> InProgress(State.ApplyCont(lv, cont, Value.Bool b, store))
         | Term.BinOp (op, arg1, arg2) ->
           InProgress(State.EvalTerm(lv, arg1, renv, cenv, (Cont.BinOpL0(op, arg2, renv, cenv))::cont, store))
         | Term.UniOp (op, arg) ->
           InProgress(State.EvalTerm(lv, arg, renv, cenv, (Cont.UniOp0(op)) :: cont, store))
         | Term.ShortCircuitOp (op, arg1, arg2) ->
           InProgress(State.EvalTerm(lv, arg1, renv, cenv, (Cont.ShortCircuitOpL0(op, arg2, renv, cenv)) :: cont, store))
         | Term.Var var ->
           let v = RuntimeEnv.lookup_var var renv in
           InProgress(State.ApplyCont(lv, cont, v, store))
         | Term.Lam _ ->
           let v = Value.Clos(renv, cenv, tm) in
           InProgress(State.ApplyCont(lv, cont, v, store))
         | Term.App (func, arg) ->
           InProgress(State.EvalTerm(lv, func, renv, cenv, (Cont.AppL0(arg, renv, cenv)) :: cont, store))
         | Term.Quo (cls, body) ->
           InProgress(State.EvalTerm(lv+1, body, renv, cenv, (Cont.Quof(CodeEnv.rename_cls cls cenv)) :: cont, store))
         | Term.Unq (0, code) ->
           InProgress(State.EvalTerm(0, code, renv, cenv, (Cont.RuntimeEval0(renv, cenv)) :: cont, store))
         | Term.Unq (_, _) -> failwith "Invalid level given to unquote"
         | Term.PolyCls _ ->
           let v = Value.Clos(renv, cenv, tm) in
           InProgress(State.ApplyCont(lv, cont, v, store))
         | Term.AppCls (func, cls) ->
           InProgress(State.EvalTerm(0, func, renv, cenv, (Cont.ClsApp0(CodeEnv.rename_cls cls cenv)) :: cont, store))
         | Term.Fix func ->
           InProgress(State.EvalTerm(0, func, renv, cenv, Cont.Fix0 :: cont, store))
         | Term.If (cond, thenn, elsee) ->
           InProgress(State.EvalTerm(0, cond, renv, cenv, (Cont.IfCond0(thenn, elsee, renv, cenv)) :: cont, store))
         | Term.Nil -> InProgress(State.ApplyCont(lv, cont, Value.Nil, store))
         | Term.Ref _ -> failwith "not implemented!"
         | Term.Deref _ -> failwith "not implemented!"
         | Term.Assign (_, _) -> failwith "not implemented!"
         | Term.Letcs (_, _, _, _, _) -> failwith "not implemented!")
      else
        failwith "not implemented!"
    | State.ApplyCont (lv, conts, v, store) ->
      if Int.equal lv 0 then
        (match conts with
         | [] -> Done(v, store)
         | (Cont.BinOpL0(op, tm, renv, cenv) :: rest) ->
           InProgress(State.EvalTerm(lv, tm, renv, cenv, (Cont.BinOpR0(op, v)) :: rest, store))
         | (Cont.BinOpR0(op, v2) :: rest) ->
           let result = Primitives.performBinOp op v2 v in
           InProgress(State.ApplyCont(lv, rest, result, store))
         | (Cont.UniOp0(op) :: rest) ->
           let result = Primitives.performUniOp op v in
           InProgress(State.ApplyCont(lv, rest, result, store))
         | (Cont.ShortCircuitOpL0(op, argr, renv, cenv) :: rest) ->
           (match (op, v) with
            | (ShortCircuitOp.And, Value.Bool false) ->
              InProgress(State.ApplyCont(lv, rest, Value.Bool(false), store))
            | (ShortCircuitOp.Or, Value.Bool true) ->
              InProgress(State.ApplyCont(lv, rest, Value.Bool(true), store))
            | (ShortCircuitOp.And, Value.Bool true)
            | (ShortCircuitOp.Or, Value.Bool false) ->
              InProgress(State.EvalTerm(lv, argr, renv, cenv, rest, store))
            | _ -> failwith "Expected Bool"
           )
         | (Cont.AppL0(tm, renv, cenv) :: rest) ->
           InProgress(State.EvalTerm(lv, tm, renv, cenv, (Cont.AppR0 v) :: rest, store))
         | (Cont.AppR0(func) :: rest) ->
           (match func with
            | Value.Clos(renv1, cenv1, Term.Lam(var, _, ty, body)) ->
              let renv2 = (var, ty, v) :: renv1 in
              InProgress(State.EvalTerm(lv, body, renv2, cenv1, rest, store))
            | _ -> failwith "expected closure")
         | (Cont.RuntimeEval0(renv, cenv) :: rest) ->
           (match v with
            | Value.Code (Term.Quo(_, body)) ->
              InProgress(State.EvalTerm(lv, body, renv, cenv, rest, store))
            | _ -> failwith "Expected quote")
         | (Cont.ClsApp0(cls) :: rest) ->
           (match v with
            | Value.Clos (renv, cenv, Term.PolyCls(cls1, _, body)) ->
              let cenv1 = (CodeEnv.Cls(cls1, cls)) :: cenv in
              InProgress(State.EvalTerm(lv, body, renv, cenv1, rest, store))
            | _ -> failwith "expected polycls"
           )
         | (Cont.IfCond0(thenn, elsee, renv, cenv) :: rest) ->
           (match v with
            | (Value.Bool b) ->
              let branch = if b then thenn else elsee in
              InProgress(State.EvalTerm(lv, branch, renv, cenv, rest, store))
            | _ -> failwith "expected boolean")
         | (Cont.Fix0 :: rest) ->
           (match v with
            | Clos(renv1, cenv1, (Lam(self, _, clss, Lam(v, cls, typ, body)) as fixed)) ->
              let eta = Value.Clos(renv1, cenv1, Lam(v, cls, typ, App(Fix fixed, Var(v)))) in
              let renv2 = (self, clss, eta) :: renv1 in
              InProgress(State.ApplyCont(lv, rest, (Value.Clos(renv2, cenv1, Lam(v, cls, typ, body))), store))
            | Clos(renv1, cenv1, (Lam(self, _, clss, PolyCls(cls, base, body)) as fixed)) ->
              let eta = Value.Clos(renv1, cenv1, PolyCls(cls, base, AppCls(Fix fixed, cls))) in
              let renv2 = (self, clss, eta) :: renv1 in
              InProgress(State.ApplyCont(lv, rest, (Value.Clos(renv2, cenv1, PolyCls(cls, base, body))), store))
            | _ -> failwith "unexpected form of fix")
         | _ -> failwith "not implemented")
      else
        failwith "not implemented" in

  let rec loop (state: State.t): Value.t * Store.t =
    match step state with
    | InProgress next_state -> loop next_state
    | Done(v, store) -> (v, store) in
  loop state

let eval_v ?(debug=false)(tm: Term.t): Value.t =
  let (v, _) =run ~debug:debug (State.init tm) in v

let%test_module "read term" = (module struct
  let%test_unit "literals" =
    [%test_result: Value.t]
      ("1"
       |> Cui.read_term
       |> eval_v)
      ~expect:(Value.Int 1);
    [%test_result: Value.t]
      ("true"
       |> Cui.read_term
       |> eval_v)
      ~expect:(Value.Bool true);
    [%test_result: Value.t]
      ("()"
       |> Cui.read_term
       |> eval_v)
      ~expect:(Value.Nil)

  let%test_unit "binary/unary operators" =
    [%test_result: Value.t]
      ("1 + 2"
       |> Cui.read_term
       |> eval_v)
      ~expect:(Value.Int 3);
    [%test_result: Value.t]
      ("not (1 < 2)"
       |> Cui.read_term
       |> eval_v)
      ~expect:(Value.Bool false)

    let%test_unit "shortcircuit operators" =
      [%test_result: Value.t]
        ("(1 < 2) && (2 < 3)"
         |> Cui.read_term
         |> eval_v)
        ~expect:(Value.Bool true);
      [%test_result: Value.t]
        ("(1 < 2) && not (2 < 3)"
         |> Cui.read_term
         |> eval_v)
        ~expect:(Value.Bool false);
      [%test_result: Value.t]
        ("not (1 < 2) && (2 < 3)"
         |> Cui.read_term
         |> eval_v)
        ~expect:(Value.Bool false);
      [%test_result: Value.t]
        ("(1 < 2) || (2 < 3)"
         |> Cui.read_term
         |> eval_v)
        ~expect:(Value.Bool true);
      [%test_result: Value.t]
        ("not (1 < 2) || (2 < 3)"
         |> Cui.read_term
         |> eval_v)
        ~expect:(Value.Bool true);
      [%test_result: Value.t]
        ("not (1 < 2) && not (2 < 3)"
         |> Cui.read_term
         |> eval_v)
        ~expect:(Value.Bool false)

    let%test_unit "if statement" =
      [%test_result: Value.t]
        ("if true then 1 else 0"
         |> Cui.read_term
         |> eval_v)
        ~expect:(Value.Int 1)

    let%test_unit "lambda redex" =
      [%test_result: Value.t]
        ("let x:int = 1 in x"
         |> Cui.read_term
         |> eval_v)
        ~expect:(Value.Int 1);
      [%test_result: Value.t]
        ("let x:int = 1 in x"
         |> Cui.read_term
         |> eval_v)
        ~expect:(Value.Int 1)

    let%test_unit "recursion" =
      [%test_result: Value.t]
        ({|
       let rec f(x:int):int =
         if x < 1
         then 0
         else x + f(x - 1) in
       f 10
      |}
         |> Cui.read_term
         |> eval_v)
        ~expect:(Value.Int 55)

  end)

(* let%test_unit "code generation" = *)
(*   [%test_result: Value.t] *)
(*     ("`{@! 1 }" *)
(*      |> Cui.read_term *)
(*      |> eval_v) *)
(*     ~expect:(Value.Code(Term.(Quo(Cls.init, Int 1)))); *)
(*   [%test_result: Value.t] *)
(*     ("`{@! 1 + 1 }" *)
(*      |> Cui.read_term *)
(*      |> eval_v) *)
(*     ~expect:(Value.Code(Term.(Quo(Cls.init, BinOp(BinOp.Plus, Int 1, Int 1))))); *)
(*   [%test_result: Value.t] *)
(*     ("`{@! fun (x:int@g) -> ~{ `{@g x } }  }" *)
(*      |> Cui.read_term *)
(*      |> eval_v) *)
(*     ~expect:(Value.Code ("`{@! fun (x:int@g) -> x}" |> Cui.read_term)); *)
(*   [%test_result: Value.t] *)
(*     ({| *)
(*         `{@! *)
(*           let x:int@g1 = 1 in *)
(*           ~{ *)
(*             let f (y:int):<int@g1> = `{@g1 x} in *)
(*             `{@g1 *)
(*               let x:int = 2 in *)
(*               ~{ f 0 } + x *)
(*             } *)
(*           } *)
(*         } *)

(*      |} *)
(*      |> Cui.read_term *)
(*      |> eval_v) *)
(*     ~expect:(Value.Code ( *)
(*         {| *)
(*            `{@! *)
(*              let x1:int = 1 in *)
(*              let x2:int = 2 in *)
(*              x1 + x2 *)
(*            } *)
(*          |} |> Cui.read_term *)
(*       )) *)

(* let%test_unit "unquote with different levels" = *)
(*   [%test_result: Value.t] *)
(*     ("~0{`{@! 2 }}" *)
(*      |> Cui.read_term *)
(*      |> eval_v) *)
(*     ~expect:(Int 2); *)
(*   [%test_result: Value.t] *)
(*     ({| *)
(*         let x:<int@!> = `{@! 1 } in *)
(*         `{@! `{@! ~2{ x } } } *)
(*      |} *)
(*      |> Cui.read_term *)
(*      |> eval_v) *)
(*     ~expect:(Value.Code ( *)
(*         "`{@! `{@! 1 } }" |> Cui.read_term *)
(*       )) *)

(* let%test_unit "polymorphic context" = *)
(*   [%test_result: Value.t] *)
(*     ({| *)
(*         let f[g1:>!](x:<int@g1>) : <int@g1> *)
(*           = `{@g1 1 + ~x } in *)
(*         `{@! fun (y:int@g2) -> ~{ f@@g2 `{@g2 y } }} *)
(*      |} *)
(*      |> Cui.read_term *)
(*      |> eval_v) *)
(*     ~expect:(Value.Code ( *)
(*         "`{@! fun (y:int@g2) -> 1 + y }" |> Cui.read_term *)
(*       )) *)

(* let%test_unit "ref" = *)
(*   [%test_result: Value.t] *)
(*     ({| *)
(*         let r: ref int = ref 1 in *)
(*         let () = r := 2 in *)
(*         !r *)
(*      |} *)
(*      |> Cui.read_term *)
(*      |> eval_v) *)
(*     ~expect:(Value.Int 2); *)
(*   [%test_result: Value.t] *)
(*     ({| *)
(*         let r: ref int = ref 0 in *)
(*         let rec loop (n:int): unit = *)
(*           if n < 1 then *)
(*             () *)
(*           else *)
(*             let c: int = !r in *)
(*             let () = r := (c + n) in *)
(*             loop (n - 1) in *)
(*         let () = loop 10 in *)
(*         !r *)
(*      |} *)
(*      |> Cui.read_term *)
(*      |> eval_v) *)
(*     ~expect:(Value.Int 55) *)
