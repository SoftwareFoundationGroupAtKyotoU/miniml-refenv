open Base
open Syntax
open Evalcommon

module Cont = struct
  type t_0 =
    (* Continutation that takes run-time values *)
    | BinOpL0 of BinOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | BinOpR0 of BinOp.t * Value.t
    | UniOp0 of UniOp.t
    | ShortCircuitOpL0 of ShortCircuitOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppL0 of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppR0 of Value.t
    | RuntimeEval0 of Value.t RuntimeEnv.t * CodeEnv.t
    | Unq0 of int
    | AppCls0 of Cls.t
    | IfCond0 of Term.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | LetcsVal0 of Var.t * Typ.t * Cls.t * Term.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | LetcsBody0 of Var.t * Typ.t * Cls.t * Term.t * Cls.t
    | Lift0 of Cls.t
    | Ref0
    | Deref0
    | AssignDest0 of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AssignNewVal0 of Value.t
  [@@deriving compare, equal, sexp]

  type t_f =
    (* Continuation that takes future-stage values *)
    | BinOpLf of BinOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | BinOpRf of BinOp.t * Term.t
    | UniOpf of UniOp.t
    | ShortCircuitOpLf of ShortCircuitOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | ShortCircuitOpRf of ShortCircuitOp.t * Term.t
    | Lamf of Var.t * Typ.t * Cls.t
    | AppLf of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppRf of Term.t
    | Quof of Cls.t
    | Unqf of int
    | PolyClsf of Cls.t * Cls.t
    | AppClsf of Cls.t
    | Fixf of Var.t * Typ.t * Cls.t
    | IfCondf of Term.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | IfThenf of Term.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | IfElsef of Term.t * Term.t
    | LetcsValf of Var.t * Typ.t * Cls.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | LetcsBodyf of Var.t * Typ.t * Cls.t * Term.t
    | Liftf of Cls.t
    | Reff
    | Dereff
    | AssignDestf of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AssignNewValf of Term.t
  [@@deriving compare, equal, sexp]

  type t =
    | Runtime of t_0
    | Future of t_f
  [@@deriving compare, equal, sexp]
end

module Config = struct
  type t =
    | EvalTerm of int * Term.t * Value.t RuntimeEnv.t * CodeEnv.t * (Cont.t list) * Store.t
    | ApplyCont0 of (Cont.t list) * Value.t * Store.t
    | ApplyContf of int * (Cont.t list) * Term.t * Store.t
  [@@deriving compare, equal, sexp]

  let init(tm:Term.t): t = EvalTerm(0, tm, [], [], [], [])
end

type stepResult =
  | InProgress of Config.t
  | Done of Value.t * Store.t

let describe (state: Config.t): unit =
  Printf.sprintf !"State: %{sexp:Config.t}" state
  |> Stdio.print_endline

let expand_eta (tm: Term.t)(ty: Typ.t): Term.t =
  (match ty with
   | Func(targ, _) ->
     (match tm with
      | Lam _ -> tm
      | _ ->
        let var = Var.gen () in
        let cls = Cls.gen () in
        Term.(Lam(var, targ, cls, App(tm, Var(var)))))
   | PolyCls(_, base, _) ->
     (match tm with
      | PolyCls _ -> tm
      | _ ->
        let cls = Cls.gen () in
        Term.(PolyCls(cls, base, AppCls(tm, cls))))
   | _ -> failwith "Eta expansion works only for functions and polymorphic classifiers")

let run ?(debug=false) (state: Config.t): Value.t * Store.t =
  let step (state: Config.t): stepResult =
    if debug then describe state;
    match (state : Config.t) with
    | Config.EvalTerm (lv, tm, renv, cenv, conts, store) ->
      if Int.equal lv 0 then
        let return (v: Value.t) =
          (* Apply the current continuation to v *)
          InProgress(Config.ApplyCont0(conts, v, store)) in
        let enter (inner: Term.t)(cont: Cont.t_0) =
          (* Evaluate inner while pushing rest computaion cont to the current continuation *)
          InProgress(Config.EvalTerm(0, inner, renv, cenv, Cont.Runtime(cont) :: conts, store)) in
        (match tm with
         | Term.Int i ->
           return (Value.Int i)
         | Term.Bool b ->
           return (Value.Bool b)
         | Term.BinOp (op, arg1, arg2) ->
           enter arg1 (Cont.BinOpL0(op, arg2, renv, cenv))
         | Term.UniOp (op, arg) ->
           enter arg (Cont.UniOp0(op))
         | Term.ShortCircuitOp (op, arg1, arg2) ->
           enter arg1 (Cont.ShortCircuitOpL0(op, arg2, renv, cenv))
         | Term.Var var ->
           return (RuntimeEnv.lookup_var var renv)
         | Term.Lam _ ->
           return (Value.Clos(renv, cenv, tm))
         | Term.App (func, arg) ->
           enter func (Cont.AppL0(arg, renv, cenv))
         | Term.Quo (cls, body) ->
           (* Switch from runtime to future *)
           let conts1 = Cont.(Future(Quof(CodeEnv.rename_cls cls cenv))) :: conts in
           InProgress(Config.EvalTerm(lv+1, body, renv, cenv, conts1, store))
         | Term.Unq (0, code) ->
           enter code (Cont.RuntimeEval0(renv, cenv))
         | Term.Unq (_, _) ->
           failwith "Invalid level given to unquote"
         | Term.PolyCls _ ->
           return (Value.Clos(renv, cenv, tm))
         | Term.AppCls (func, cls) ->
           enter func (Cont.AppCls0(CodeEnv.rename_cls cls cenv))
         | Term.Fix (self, tys, clss, func) ->
           (match tys with
            | Func _
            | PolyCls _ ->
              let renv1 = (self, clss, Value.Clos(renv, cenv, expand_eta tm tys)) :: renv in
              InProgress(Config.EvalTerm(0, func, renv1, cenv, conts, store))
            | _ -> failwith "Unexpected type for fixpoint")
         | Term.If (cond, thenn, elsee) ->
           enter cond (Cont.IfCond0(thenn, elsee, renv, cenv))
         | Term.Nil ->
           return Value.Nil
         | Term.Ref init ->
           enter init Cont.Ref0
         | Term.Deref loc ->
           enter loc Cont.Deref0
         | Term.Assign (dest, newval) ->
           enter dest (Cont.AssignDest0(newval, renv, cenv))
         | Term.Letcs (var, ty, cls, tm, body) ->
           enter tm (Cont.LetcsVal0(var, ty, cls, tm, body, renv, cenv))
         | Term.Lift (cls, tm) ->
           enter tm (Cont.Lift0(CodeEnv.rename_cls cls cenv)))
      else
        let return (tm: Term.t) =
          (* Apply the current continuation to v *)
          InProgress(Config.ApplyContf(lv, conts, tm, store)) in
        let enter (inner: Term.t)(cont: Cont.t_f) =
          (* Evaluate inner while pushing rest computaion cont to the current continuation *)
          InProgress(Config.EvalTerm(lv, inner, renv, cenv, Cont.Future(cont) :: conts, store)) in
        let enter_with_bind (inner: Term.t)(cenv1: CodeEnv.t)(cont: Cont.t_f) =
          (* Evaluate inner while pushing rest computaion cont to the current continuation *)
          InProgress(Config.EvalTerm(lv, inner, renv, cenv1, Cont.Future(cont) :: conts, store)) in
        (match tm with
         | Term.Int i ->
           return (Term.Int i)
         | Term.Bool b ->
           return (Term.Bool b)
         | Term.BinOp (op, argl, argr) ->
           enter argl (Cont.BinOpLf(op, argr, renv, cenv))
         | Term.UniOp (op, arg) ->
           enter arg (Cont.UniOpf(op))
         | Term.ShortCircuitOp (op, argl, argr) ->
           enter argl (Cont.ShortCircuitOpLf(op, argr, renv, cenv))
         | Term.Var var ->
           return (Term.Var (CodeEnv.rename_var var cenv))
         | Term.Lam (var, ty, cls, body) ->
           let var1 = Var.color var in
           let cls1 = Cls.color cls in
           let ty1 = CodeEnv.rename_cls_in_typ ty cenv in
           let cenv1 = CodeEnv.Var(var, var1) :: CodeEnv.Cls(cls, cls1) :: cenv in
           enter_with_bind body cenv1 (Cont.Lamf(var1, ty1, cls1))
         | Term.App (func, arg) ->
           enter func (Cont.AppLf(arg, renv, cenv))
         | Term.Quo (cls, body) ->
           let conts1 = Cont.(Future(Quof(CodeEnv.rename_cls cls cenv))) :: conts in
           InProgress(Config.EvalTerm(lv + 1, body, renv, cenv, conts1, store))
         | Term.Unq (lvdiff, tm) ->
           if Int.(lv < lvdiff) then
             failwith "lvdiff too large"
           else
             let conts1 = if Int.equal lv lvdiff
               then Cont.(Runtime(Unq0(lvdiff))) :: conts
               (* Switch from future to runtime *)
               else Cont.(Future(Unqf(lvdiff))) :: conts in
             InProgress(Config.EvalTerm(lv - lvdiff, tm, renv, cenv, conts1, store))
         | Term.PolyCls (cls, base, body) ->
           let cls1 = Cls.color cls in
           let base1 = cenv |> CodeEnv.rename_cls base in
           let cenv1 = (CodeEnv.(Cls(cls, cls1) :: cenv)) in
           enter_with_bind body cenv1 (Cont.PolyClsf(cls1, base1))
         | Term.AppCls (func, cls) ->
           enter func (Cont.AppClsf (CodeEnv.rename_cls cls cenv))
         | Term.Fix (var, ty, cls, func) ->
           let var1 = Var.color var in
           let cls1 = Cls.color cls in
           let ty1 = CodeEnv.rename_cls_in_typ ty cenv in
           let cenv1 = CodeEnv.Var(var, var1) :: CodeEnv.Cls(cls, cls1) :: cenv in
           enter_with_bind func cenv1 (Cont.Fixf(var1, ty1, cls1))
         | Term.If (cond, thenn, elsee) ->
           enter cond (Cont.IfCondf(thenn, elsee, renv, cenv))
         | Term.Nil ->
           return Term.Nil
         | Term.Ref init ->
           enter init Cont.Reff
         | Term.Deref loc ->
           enter loc Cont.Dereff
         | Term.Assign (dest, newval) ->
           enter dest (Cont.AssignDestf(newval, renv, cenv))
         | Term.Letcs (var, ty, cls, def, body) ->
           let var1 = Var.color var in
           let cls1 = Cls.color cls in
           let ty1 = CodeEnv.rename_cls_in_typ ty cenv in
           let cenv1 = CodeEnv.Var(var, var1) :: CodeEnv.Cls(cls, cls1) :: cenv in
           enter def (Cont.LetcsValf(var1, ty1, cls1, body, renv, cenv1))
         | Term.Lift (cls, tm) ->
           enter tm (Cont.Liftf(CodeEnv.rename_cls cls cenv))
        )
    | Config.ApplyCont0 (conts, v, store) ->
      (match conts with
       | [] -> Done(v, store)
       | (Cont.Runtime(head) :: rest) ->
         let return (v: Value.t): stepResult =
           (* apply the contiuation to v *)
           InProgress(Config.ApplyCont0(rest, v, store)) in
         let eval (tm: Term.t)(renv: Value.t RuntimeEnv.t)(cenv: CodeEnv.t): stepResult =
           (* compute tm under renv and cenv, and then apply the result to the current continuation *)
           InProgress(Config.EvalTerm(0, tm, renv, cenv, rest, store)) in
         let resume (tm: Term.t)(renv: Value.t RuntimeEnv.t)(cenv: CodeEnv.t)(cont: Cont.t_0): stepResult =
           (* resume computing tm under renv and cenv with pushing cont to the current continuation *)
           InProgress(Config.EvalTerm(0, tm, renv, cenv, Cont.Runtime(cont) :: rest, store)) in
         (match head with
          | Cont.BinOpL0(op, tm, renv, cenv) ->
            resume tm renv cenv (Cont.(BinOpR0(op, v)))
          | Cont.BinOpR0(op, v2) ->
            return (Primitives.performBinOp op v2 v)
          | Cont.UniOp0(op) ->
            return (Primitives.performUniOp op v)
          | Cont.ShortCircuitOpL0(op, argr, renv, cenv) ->
            (match (op, v) with
             | (ShortCircuitOp.And, Value.Bool false) ->
               return (Value.Bool(false))
             | (ShortCircuitOp.Or, Value.Bool true) ->
               return (Value.Bool(true))
             | (ShortCircuitOp.And, Value.Bool true)
             | (ShortCircuitOp.Or, Value.Bool false) ->
               eval argr renv cenv
             | _ -> failwith "Expected Bool"
            )
          | Cont.AppL0(arg, renv, cenv) ->
            resume arg renv cenv (Cont.AppR0 v)
          | Cont.AppR0(func) ->
            (match func with
             | Value.Clos(renv, cenv, Term.Lam(var, _, ty, body)) ->
               eval body ((var, ty, v) :: renv) cenv
             | _ -> failwith "expected closure")
          | Cont.RuntimeEval0(renv, cenv) ->
            (match v with
             | Value.Code (Term.Quo(_, body)) ->
               eval body renv cenv
             | _ -> failwith "Expected quoted code")
          | Cont.Unq0(lvdiff) ->
            assert(lvdiff > 0);
            (match v with
             | Value.Code (Term.Quo(_, result)) ->
               (* Switch from runtime to future *)
               InProgress(Config.ApplyContf(lvdiff, rest, result, store))
             | _ -> failwith "expected quoted code"
            )
          | Cont.AppCls0(cls) ->
            (match v with
             | Value.Clos (renv, cenv, Term.PolyCls(cls1, _, body)) ->
               eval body renv (CodeEnv.Cls(cls1, cls) :: cenv)
             | _ -> failwith "expected polycls"
            )
          | Cont.IfCond0(thenn, elsee, renv, cenv) ->
            (match v with
             | (Value.Bool b) ->
               eval (if b then thenn else elsee) renv cenv
             | _ -> failwith "expected boolean")
          | Cont.LetcsVal0(var, ty, cls, def, body, renv, cenv) ->
            let renv1 = (var, cls, v) :: renv in
            let cont = Cont.LetcsBody0(var, ty, cls, def, RuntimeEnv.current renv) in
            resume body renv1 cenv cont
          | Cont.LetcsBody0(var, ty, cls, def, current_cls) ->
            (match v with
             | Value.Code Term.Quo(_, body) ->
               return (Value.Code(Term.Quo(current_cls, Term.Letcs(var, ty, cls, def, body))))
             | Value.Nil
             | Value.Bool _
             | Value.Int _ ->
               return v
             | _ -> failwith "expected code or primitive values ")
          | Cont.Lift0 cls ->
            (match v with
             | Value.Int i ->
               return (Value.Code (Term.Quo(cls, Term.Int i)))
             | Value.Bool b ->
               return (Value.Code (Term.Quo(cls, Term.Bool b)))
             | _ -> failwith "expected liftable values")
          | Cont.Ref0 ->
            let newloc = Loc.alloc () in
            InProgress(Config.ApplyCont0(rest, Value.Loc newloc, (newloc, v) :: store))
          | Cont.Deref0 ->
            (match v with
             | Value.Loc(loc) ->
               return (Store.lookup loc store)
             | _ -> failwith "expected location")
          | Cont.AssignDest0(newval, renv, cenv) ->
            resume newval renv cenv (Cont.AssignNewVal0 v)
          | Cont.AssignNewVal0(vloc) ->
            (match vloc with
             | (Value.Loc cloc) ->
               let store1 = Store.update cloc v store in
               InProgress(Config.ApplyCont0(rest, Value.Nil, store1))
             | _ -> failwith "expected location"
            )
         )
       | _ -> failwith "Ill-formed configuraiton: runtime value is passed to future continutation")
    | Config.ApplyContf (lv, conts, v, store) ->
      (match conts with
       | [] -> failwith "Ill-formed configuraiton: machine can only exit at runtime"
       | Cont.Runtime(_) :: _ ->
         failwith "Ill-formed configuraiton: future value being passed to current continutation"
       | Future head :: rest ->
         let return (tm: Term.t): stepResult =
           (* apply the contiuation to v *)
           InProgress(Config.ApplyContf(lv, rest, tm, store)) in
         let resume (tm: Term.t)(renv: Value.t RuntimeEnv.t)(cenv: CodeEnv.t)(cont: Cont.t_f): stepResult =
           (* resume computing tm under renv and cenv with pushing cont to the current continuation *)
           InProgress(Config.EvalTerm(lv, tm, renv, cenv, Cont.Future(cont) :: rest, store)) in
         (match head with
          | Cont.BinOpLf(op, tm, renv, cenv) ->
            resume tm renv cenv (Cont.BinOpRf(op, v))
          | Cont.BinOpRf(op, vl) ->
            return (Term.BinOp(op, vl, v))
          | Cont.UniOpf(op) ->
            return (Term.UniOp(op, v))
          | Cont.ShortCircuitOpLf(op, argr, renv, cenv) ->
            resume argr renv cenv (Cont.ShortCircuitOpRf(op, v))
          | Cont.ShortCircuitOpRf(op, vl) ->
            return (Term.ShortCircuitOp(op, vl, v))
          | Cont.Lamf(var, ty, cls) ->
            return (Term.Lam(var, ty, cls, v))
          | Cont.AppLf(arg, renv, cenv) ->
            resume arg renv cenv (Cont.AppRf(v))
          | Cont.AppRf(vfunc) ->
            return (Term.App(vfunc, v))
          | Cont.Quof(cls) ->
            if Int.equal lv 1 then
              (* Switch from future to runtime *)
              let result = Value.Code(Term.Quo(cls, v)) in
              InProgress(Config.ApplyCont0(rest, result, store))
            else
              let result = Term.Quo(cls, v) in
              InProgress(Config.ApplyContf(lv-1, rest, result, store))
          | Cont.Unqf lvdiff ->
            let result = Term.Unq(lvdiff, v) in
            InProgress(Config.ApplyContf(lv + lvdiff, rest, result, store))
          | Cont.PolyClsf(cls, base) ->
            return (Term.PolyCls(cls, base, v))
          | Cont.AppClsf(cls) ->
            return (Term.AppCls(v, cls))
          | Cont.Fixf(var, ty, cls) ->
            return (Term.Fix(var, ty, cls, v))
          | Cont.IfCondf(thenn, elsee, renv, cenv) ->
            resume thenn renv cenv (Cont.IfThenf(v, elsee, renv, cenv))
          | Cont.IfThenf(condv, elsee, renv, cenv) ->
            resume elsee renv cenv (Cont.IfElsef(condv, v))
          | Cont.IfElsef(condv, thenv) ->
            return (Term.If(condv, thenv, v))
          | Cont.LetcsValf(var, ty, cls, body, renv, cenv) ->
            resume body renv cenv (Cont.LetcsBodyf(var, ty, cls, v))
          | Cont.LetcsBodyf(var, ty, cls, vval) ->
            return (Term.Letcs (var, ty, cls, vval, v))
          | Cont.Liftf(cls)->
            return (Term.Lift(cls, v))
          | Cont.Reff ->
            return (Term.Ref(v))
          | Cont.Dereff ->
            return (Term.Deref(v))
          | Cont.AssignDestf(newval, renv, cenv) ->
            resume newval renv cenv (Cont.AssignNewValf(v))
          | Cont.AssignNewValf(vdest) ->
            return (Term.Assign(vdest, v))
         )) in
  let rec loop (state: Config.t): Value.t * Store.t =
    match step state with
    | InProgress next_state -> loop next_state
    | Done(v, store) -> (v, store) in
  loop state

let eval_v ?(debug=false)(tm: Term.t): Value.t =
  let (v, _) =run ~debug:debug (Config.init tm) in v

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

  let%test_unit "generate code with unquote" =
    [%test_result: Value.t]
      ("`{@! let x:<int@!> = `{@! 1 } in `{@! ~x }}"
       |> Cui.read_term
       |> eval_v)
      ~expect:(Value.Code (
          "`{@! let x:<int@!> = `{@! 1 } in `{@! ~x }}" |> Cui.read_term
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

  let%test_unit "let cs" =
    [%test_result: Value.t]
      ({|
          let cs sqr(x:int@g) : int = x * x in
          `{@! sqr 1 }
        |}
       |> Cui.read_term
       |> eval_v)
      ~expect:(Value.Code (
          {|
              `{@! let cs sqr(x:int) : int = x * x in
                   sqr 1 }
            |} |> Cui.read_term
        ))

  let%test_unit "lift" =
    [%test_result: Value.t]
      ({|
          lift@@! (1 + 1)
        |}
       |> Cui.read_term
       |> eval_v)
      ~expect:(Value.Code (
          "`{@! 2 }" |> Cui.read_term
        ));
    [%test_result: Value.t]
      ({|
          lift@@! (1 < 2)
        |}
       |> Cui.read_term
       |> eval_v)
      ~expect:(Value.Code (
          "`{@! true }" |> Cui.read_term
        ))

end)


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
