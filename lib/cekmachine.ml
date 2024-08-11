open Base
open Syntax

module RuntimeEnv = struct
  type 'a t = (Var.t * Cls.t * 'a) list
  [@@deriving compare, equal, sexp]

  let rec lookup_var(v:Var.t)(env:'a t): 'a =
    match env with
    | [] -> failwith "failed to lookup var"
    | (v1, _, value) :: rest ->
      if Var.equal v v1
      then value
      else rest |> lookup_var v

  let current(env: 'a t): Cls.t =
    match env with
    | [] -> Cls.init
    | (_, g, _) :: _ -> g
end

module CodeEnv = struct
  type elm =
    | Var of Var.t * Var.t
    | Cls of Cls.t * Cls.t
  [@@deriving compare, equal, sexp]

  type t = elm list
  [@@deriving compare, equal, sexp]

  let rec rename_var(v:Var.t)(env: t): Var.t =
    match env with
    | [] -> v
    | Var(from, dest) :: rest ->
        if Var.equal v from
        then dest
        else rest |> rename_var v
    | _ :: rest -> rest |> rename_var v

  let rec rename_cls(cls: Cls.t)(env: t): Cls.t =
    match env with
    | [] -> cls
    | Cls(from, dest) :: rest ->
      if Cls.equal cls from
      then
        rest |> rename_cls dest
      else rest |> rename_cls cls
    | _ :: rest -> rest |> rename_cls cls

  let rec rename_cls_in_typ(typ: Typ.t)(env: t): Typ.t =
    match (typ : Typ.t) with
    | Typ.BaseInt
    | Typ.BaseBool -> typ
    | Typ.Func (func, arg) ->
      let func' = env |> rename_cls_in_typ func in
      let arg' = env |> rename_cls_in_typ arg in
      Typ.Func(func', arg')
    | Typ.Code (base, ty) ->
      let base' = env |> rename_cls base in
      let ty' = env |> rename_cls_in_typ ty in
      Typ.Code(base', ty')
    | Typ.PolyCls (cls, base, ty) ->
      let cls' = Cls.color cls in
      let base' = env |> rename_cls base in
      let ty' = ty |> Typ.rename_cls cls cls' in
      let ty' = env |> rename_cls_in_typ ty' in
      Typ.PolyCls (cls', base', ty')
    | Typ.Unit -> Typ.Unit
    | Typ.Ref ty -> Typ.Ref(env |> rename_cls_in_typ ty)
end

module Loc = struct
  type t = int
  [@@deriving compare, equal, sexp]

  let counter = ref 0

  let alloc () =
    let ret = !counter in
    counter := ret + 1;
    ret
end

module Value = struct
  type t =
    | Int of int
    | Bool of bool
    | Clos of t RuntimeEnv.t * CodeEnv.t * Term.t
    | Code of Term.t
    | Fut of Term.t
    | Loc of Loc.t
    | Nil
  [@@deriving compare, equal, sexp]
end

module Store = struct
  type t = (Loc.t * Value.t) list
  [@@deriving compare, equal, sexp]

  let rec lookup loc store =
    match store with
    | [] -> failwith "failed to lookup store"
    | (loc1, v) :: rest ->
      if Loc.equal loc loc1
      then v
      else lookup loc rest

  let rec update loc newv store =
    match store with
    | [] -> failwith "failed to lookup store"
    | (loc1, v) :: rest ->
      if Loc.equal loc loc1
      then (loc1, newv) :: rest
      else (loc1, v) :: update loc newv rest
end

module Continuation = struct
  type t =
    (* Continuation that takes run-time values *)
    | BinOpL0 of BinOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | BinOpR0 of BinOp.t * Value.t
    | UniOp0 of UniOp.t
    | ShortCircuitOpL0 of ShortCircuitOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | ShortCircuitOpR0 of ShortCircuitOp.t * Value.t
    | AppL0 of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppR0 of Value.t
    | RuntimeEval0 of Value.t RuntimeEnv.t * CodeEnv.t
    | Unq0 of int
    | ClsApp0 of Cls.t
    (* Continuation that takes future-stage values *)
    | Lamf of Var.t * Cls.t * Typ.t
    | AppLf of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppRf of Value.t
    | Quof of Cls.t
    | Unqf of int
    | ClsAbsf of Cls.t * Cls.t
    | ClsAppf of Cls.t
end

module State = struct
  type t =
    | EvalTerm of int * Term.t * Value.t RuntimeEnv.t * CodeEnv.t * (Continuation.t list) * Store.t
    | ApplyCont of int * (Continuation.t list) * Value.t * Store.t

  let init(tm:Term.t): t = EvalTerm(0, tm, [], [], [], [])
end

let performBinOp(op:BinOp.t)(a:Value.t)(b:Value.t): Value.t =
  (match op with
   | BinOp.Plus -> (match (a, b) with
       | (Int ai, Int bi) -> Int (ai + bi)
       | _ -> failwith "type mismatch: binop plus")
   | BinOp.Mult -> (match (a, b) with
       | (Int ai, Int bi) -> Int (ai * bi)
       | _ -> failwith "type mismatch: binop mult")
   | BinOp.Minus -> (match (a, b) with
       | (Int ai, Int bi) -> Int (ai - bi)
       | _ -> failwith "type mismatch: binop minus")
   | BinOp.Div -> (match (a, b) with
       | (Int ai, Int bi) -> Int (ai / bi)
       | _ -> failwith "type mismatch: binop div")
   | BinOp.Mod -> (match (a, b) with
       | (Int ai, Int bi) -> Int (Int.rem ai bi)
       | _ -> failwith "type mismatch: binop mod")
   | BinOp.LT -> (match (a, b) with
       | (Int ai, Int bi) -> Bool (ai < bi)
       | _ -> failwith "type mismatch: binop lt")
   | BinOp.Equal -> (match (a, b) with
       | (Int ai, Int bi) -> Bool (Int.equal ai bi)
       | _ -> failwith "type mismatch: binop eq"))

let performUniOp(op:UniOp.t)(a:Value.t): Value.t =
  match (op, a) with
  | (UniOp.Not, Bool(b)) -> Bool(not b)
  | _ -> failwith "type mismatch: uniop not"

type stepResult =
  | InProgress of State.t
  | Done of Value.t * Store.t

let run ?(debug=false) (state: State.t): Value.t * Store.t =
  let step (state: State.t): stepResult =
    match (state : State.t) with
    | State.EvalTerm (lv, tm, renv, cenv, cont, store) ->
      if Int.equal lv 0 then
        (match tm with
         (* Already a value *)
         | Term.Int i -> InProgress(State.ApplyCont(lv, cont, Value.Int i, store))
         | Term.Bool b -> InProgress(State.ApplyCont(lv, cont, Value.Bool b, store))
         | Term.BinOp (op, arg1, arg2) ->
           InProgress(State.EvalTerm(lv, arg1, renv, cenv, (Continuation.BinOpL0(op, arg2, renv, cenv))::cont, store))
         | Term.UniOp (op, arg) ->
           InProgress(State.EvalTerm(lv, arg, renv, cenv, (Continuation.UniOp0(op)) :: cont, store))
         | Term.ShortCircuitOp (op, arg1, arg2) ->
           InProgress(State.EvalTerm(lv, arg1, renv, cenv, (Continuation.ShortCircuitOpL0(op, arg2, renv, cenv)) :: cont, store))
         | Term.Var var ->
           let v = RuntimeEnv.lookup_var var renv in
           InProgress(State.ApplyCont(lv, cont, v, store))
         | Term.Lam _ ->
           let v = Value.Clos(renv, cenv, tm) in
           InProgress(State.ApplyCont(lv, cont, v, store))
         | Term.App (func, arg) ->
           InProgress(State.EvalTerm(lv, func, renv, cenv, (Continuation.AppL0(arg, renv, cenv)) :: cont, store))
         | Term.Quo (cls, body) ->
           InProgress(State.EvalTerm(lv+1, body, renv, cenv, (Continuation.Quof(CodeEnv.rename_cls cls cenv)) :: cont, store))
         | Term.Unq (0, code) ->
           InProgress(State.EvalTerm(0, code, renv, cenv, (Continuation.RuntimeEval0(renv, cenv)) :: cont, store))
         | Term.Unq (_, _) -> failwith "Invalid level given to unquote"
         | Term.PolyCls _ ->
           let v = Value.Clos(renv, cenv, tm) in
           InProgress(State.ApplyCont(lv, cont, v, store))
         | Term.AppCls (func, cls) ->
           InProgress(State.EvalTerm(0, func, renv, cenv, (Continuation.ClsApp0(CodeEnv.rename_cls cls cenv)) :: cont, store))
         | Term.Fix _ -> failwith "not implemented!"
         | Term.If (_, _, _) -> failwith "not implemented!"
         | Term.Nil -> failwith "not implemented!"
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
         | (Continuation.BinOpL0(op, tm, renv, cenv) :: rest) ->
           InProgress(State.EvalTerm(lv, tm, renv, cenv, (Continuation.BinOpR0(op, v)) :: rest, store))
         | (Continuation.BinOpR0(op, v2) :: rest) ->
           let result = performBinOp op v v2 in
           InProgress(State.ApplyCont(lv, rest, result, store))
         | (Continuation.AppL0(tm, renv, cenv) :: rest) ->
           InProgress(State.EvalTerm(lv, tm, renv, cenv, (Continuation.AppR0 v) :: rest, store))
         | (Continuation.AppR0(v2) :: rest) ->
           (match v with
            | Value.Clos(renv1, cenv1, Term.Lam(var, _, ty, body)) ->
              let renv2 = (var, ty, v2) :: renv1 in
              InProgress(State.EvalTerm(lv, body, renv2, cenv1, rest, store))
            | _ -> failwith "expected closure")
         | (Continuation.RuntimeEval0(renv, cenv) :: rest) ->
           (match v with
            | Value.Code (Term.Quo(_, body)) ->
              InProgress(State.EvalTerm(lv, body, renv, cenv, rest, store))
            | _ -> failwith "Expected quote")
         | (Continuation.ClsApp0(cls) :: rest) ->
           (match v with
            | Value.Clos (renv, cenv, Term.PolyCls(cls1, base, body)) ->
              let cenv1 = (CodeEnv.Cls(cls1, cls)) :: cenv in
              InProgress(State.EvalTerm(lv, body, renv, cenv1, rest, store))
            | _ -> failwith "expected polycls"
           )
         | _ -> failwith "not implemented")
      else
        failwith "not implemented" in

  let rec loop (state: State.t): Value.t * Store.t =
    match step state with
    | InProgress next_state -> loop next_state
    | Done(v, store) -> (v, store) in
  loop state

let eval_v(tm: Term.t): Value.t =
  let (v, _) = State.init tm |> run in v

let%test_unit "hoge" =
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
    ("1 + 2"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Int 3);
  [%test_result: Value.t]
    ("not (1 < 2)"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Bool false);
  [%test_result: Value.t]
    ("(1 < 2) && (2 < 3)"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Bool true);
  [%test_result: Value.t]
    ("if true then 1 else 0"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Int 1);
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

let%test_unit "code generation" =
  [%test_result: Value.t]
    ("`{@! 1 }"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Code(Term.(Quo(Cls.init, Int 1))));
  [%test_result: Value.t]
    ("`{@! 1 + 1 }"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Code(Term.(Quo(Cls.init, BinOp(BinOp.Plus, Int 1, Int 1)))));
  [%test_result: Value.t]
    ("`{@! fun (x:int@g) -> ~{ `{@g x } }  }"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Code ("`{@! fun (x:int@g) -> x}" |> Cui.read_term));
  [%test_result: Value.t]
    ({|
        `{@!
          let x:int@g1 = 1 in
          ~{
            let f (y:int):<int@g1> = `{@g1 x} in
            `{@g1
              let x:int = 2 in
              ~{ f 0 } + x
            }
          }
        }

     |}
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Code (
        {|
           `{@!
             let x1:int = 1 in
             let x2:int = 2 in
             x1 + x2
           }
         |} |> Cui.read_term
      ))

let%test_unit "unquote with different levels" =
  [%test_result: Value.t]
    ("~0{`{@! 2 }}"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Int 2);
  [%test_result: Value.t]
    ({|
        let x:<int@!> = `{@! 1 } in
        `{@! `{@! ~2{ x } } }
     |}
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Code (
        "`{@! `{@! 1 } }" |> Cui.read_term
      ))

let%test_unit "polymorphic context" =
  [%test_result: Value.t]
    ({|
        let f[g1:>!](x:<int@g1>) : <int@g1>
          = `{@g1 1 + ~x } in
        `{@! fun (y:int@g2) -> ~{ f@@g2 `{@g2 y } }}
     |}
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Code (
        "`{@! fun (y:int@g2) -> 1 + y }" |> Cui.read_term
      ))

let%test_unit "ref" =
  [%test_result: Value.t]
    ({|
        let r: ref int = ref 1 in
        let () = r := 2 in
        !r
     |}
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Int 2);
  [%test_result: Value.t]
    ({|
        let r: ref int = ref 0 in
        let rec loop (n:int): unit =
          if n < 1 then
            ()
          else
            let c: int = !r in
            let () = r := (c + n) in
            loop (n - 1) in
        let () = loop 10 in
        !r
     |}
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Int 55)
