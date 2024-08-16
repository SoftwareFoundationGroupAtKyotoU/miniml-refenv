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
    | Fix0
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
    | Fixf
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

let run ?(debug=false) (state: Config.t): Value.t * Store.t =
  let step (state: Config.t): stepResult =
    if debug then describe state;
    match (state : Config.t) with
    | Config.EvalTerm (lv, tm, renv, cenv, conts, store) ->
      if Int.equal lv 0 then
        (match tm with
         | Term.Int i -> InProgress(Config.ApplyCont0(conts, Value.Int i, store))
         | Term.Bool b -> InProgress(Config.ApplyCont0(conts, Value.Bool b, store))
         | Term.BinOp (op, arg1, arg2) ->
           let conts1 = Cont.(Runtime(BinOpL0(op, arg2, renv, cenv))) :: conts in
           InProgress(Config.EvalTerm(lv, arg1, renv, cenv, conts1, store))
         | Term.UniOp (op, arg) ->
           let conts1 = Cont.(Runtime(Cont.UniOp0(op))) :: conts in
           InProgress(Config.EvalTerm(lv, arg, renv, cenv, conts1, store))
         | Term.ShortCircuitOp (op, arg1, arg2) ->
           let conts1  =Cont.(Runtime(Cont.ShortCircuitOpL0(op, arg2, renv, cenv))) :: conts in
           InProgress(Config.EvalTerm(lv, arg1, renv, cenv, conts1, store))
         | Term.Var var ->
           let result = RuntimeEnv.lookup_var var renv in
           InProgress(Config.ApplyCont0(conts, result, store))
         | Term.Lam _ ->
           let result = Value.Clos(renv, cenv, tm) in
           InProgress(Config.ApplyCont0(conts, result, store))
         | Term.App (func, arg) ->
           let conts1 = Cont.(Runtime(AppL0(arg, renv, cenv))) :: conts in
           InProgress(Config.EvalTerm(lv, func, renv, cenv, conts1, store))
         | Term.Quo (cls, body) ->
           (* Switch from runtime to future *)
           let conts1 = Cont.(Future(Quof(CodeEnv.rename_cls cls cenv))) :: conts in
           InProgress(Config.EvalTerm(lv+1, body, renv, cenv, conts1, store))
         | Term.Unq (0, code) ->
           let conts1 = Cont.(Runtime(RuntimeEval0(renv, cenv))) :: conts in
           InProgress(Config.EvalTerm(0, code, renv, cenv, conts1, store))
         | Term.Unq (_, _) -> failwith "Invalid level given to unquote"
         | Term.PolyCls _ ->
           let result = Value.Clos(renv, cenv, tm) in
           InProgress(Config.ApplyCont0(conts, result, store))
         | Term.AppCls (func, cls) ->
           let conts1 = Cont.(Runtime(AppCls0(CodeEnv.rename_cls cls cenv))) :: conts in
           InProgress(Config.EvalTerm(0, func, renv, cenv, conts1, store))
         | Term.Fix func ->
           let conts1 = Cont.(Runtime(Fix0)) :: conts in
           InProgress(Config.EvalTerm(0, func, renv, cenv, conts1, store))
         | Term.If (cond, thenn, elsee) ->
           let conts1 = Cont.(Runtime(IfCond0(thenn, elsee, renv, cenv))) :: conts in
           InProgress(Config.EvalTerm(0, cond, renv, cenv, conts1, store))
         | Term.Nil -> InProgress(Config.ApplyCont0(conts, Value.Nil, store))
         | Term.Ref init ->
           let conts1 = Cont.(Runtime(Ref0)) :: conts in
           InProgress(Config.EvalTerm(0, init, renv, cenv, conts1, store))
         | Term.Deref loc ->
           let conts1 = Cont.(Runtime(Deref0)) :: conts in
           InProgress(Config.EvalTerm(0, loc, renv, cenv, conts1, store))
         | Term.Assign (dest, newval) ->
           let conts1 = Cont.(Runtime(AssignDest0(newval, renv, cenv))) :: conts in
           InProgress(Config.EvalTerm(0, dest, renv, cenv, conts1, store))
         | Term.Letcs (var, ty, cls, tm, body) ->
           let conts1 = Cont.(Runtime(LetcsVal0(var, ty, cls, tm, body, renv, cenv))) :: conts in
           InProgress(Config.EvalTerm(lv, tm, renv, cenv, conts1, store))
         | Term.Lift (cls, tm) ->
           let conts1 = Cont.(Runtime(Lift0(CodeEnv.rename_cls cls cenv))) :: conts in
           InProgress(Config.EvalTerm(lv, tm, renv, cenv, conts1, store)))
      else
        (match tm with
         | Term.Int i ->
           InProgress(Config.ApplyContf(lv, conts, Term.Int i, store))
         | Term.Bool b ->
           InProgress(Config.ApplyContf(lv, conts, Term.Bool(b), store))
         | Term.BinOp (op, argl, argr) ->
           let conts1 = Cont.(Future(BinOpLf(op, argr, renv, cenv))) :: conts in
           InProgress(Config.EvalTerm(lv, argl, renv, cenv, conts1, store))
         | Term.UniOp (op, arg) ->
           let conts1 = Cont.(Future(UniOpf(op))) :: conts in
           InProgress(Config.EvalTerm(lv, arg, renv, cenv, conts1, store))
         | Term.ShortCircuitOp (op, argl, argr) ->
           let conts1 = Cont.(Future(ShortCircuitOpLf(op, argr, renv, cenv))) :: conts in
           InProgress(Config.EvalTerm(lv, argl, renv, cenv, conts1, store))
         | Term.Var var ->
           let result = Term.Var (CodeEnv.rename_var var cenv) in
           InProgress(Config.ApplyContf(lv, conts, result, store))
         | Term.Lam (var, ty, cls, body) ->
           let var1 = Var.color var in
           let cls1 = Cls.color cls in
           let ty1 = CodeEnv.rename_cls_in_typ ty cenv in
           let cenv1 = CodeEnv.Var(var, var1) :: CodeEnv.Cls(cls, cls1) :: cenv in
           let conts1 = Cont.(Future(Lamf(var1, ty1, cls1))) :: conts in
           InProgress(Config.EvalTerm(lv, body, renv, cenv1, conts1, store))
         | Term.App (func, arg) ->
           let conts1 = Cont.(Future(AppLf(arg, renv, cenv))) :: conts in
           InProgress(Config.EvalTerm(lv, func, renv, cenv, conts1, store))
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
           let conts1 = Cont.(Future(PolyClsf(cls1, base1))) :: conts in
           InProgress(Config.EvalTerm(lv, body, renv, cenv1, conts1, store))
         | Term.AppCls (func, cls) ->
           let cls = CodeEnv.rename_cls cls cenv in
           let conts1 = Cont.(Future(AppClsf cls)) :: conts in
           InProgress(Config.EvalTerm(lv, func, renv, cenv, conts1, store))
         | Term.Fix func ->
           let conts1 = Cont.(Future(Fixf)) :: conts in
           InProgress(Config.EvalTerm(lv, func, renv, cenv, conts1, store))
         | Term.If (cond, thenn, elsee) ->
           let conts1 = Cont.(Future(IfCondf(thenn, elsee, renv, cenv))) :: conts in
           InProgress(Config.EvalTerm(lv, cond, renv, cenv, conts1, store))
         | Term.Nil ->
           InProgress(Config.ApplyContf(lv, conts, Term.Nil, store))
         | Term.Ref init ->
           let conts1 = Cont.(Future(Reff)) :: conts in
           InProgress(Config.EvalTerm(lv, init, renv, cenv, conts1, store))
         | Term.Deref loc ->
           let conts1 = Cont.(Future(Dereff)) :: conts in
           InProgress(Config.EvalTerm(lv, loc, renv, cenv, conts1, store))
         | Term.Assign (dest, newval) ->
           let conts1 = Cont.(Future(AssignDestf(newval, renv, cenv))) :: conts in
           InProgress(Config.EvalTerm(lv, dest, renv, cenv, conts1, store))
         | Term.Letcs (var, ty, cls, def, body) ->
           let var1 = Var.color var in
           let cls1 = Cls.color cls in
           let ty1 = CodeEnv.rename_cls_in_typ ty cenv in
           let cenv1 = CodeEnv.Var(var, var1) :: CodeEnv.Cls(cls, cls1) :: cenv in
           let conts1 = Cont.(Future(LetcsValf(var1, ty1, cls1, body, renv, cenv1))) :: conts in
           InProgress(Config.EvalTerm(lv, def, renv, cenv, conts1, store))
         | Term.Lift (cls, tm) ->
           let conts1 = Cont.(Future(Liftf(CodeEnv.rename_cls cls cenv))) :: conts in
           InProgress(Config.EvalTerm(lv, tm, renv, cenv, conts1, store))
        )
    | Config.ApplyCont0 (conts, v, store) ->
      (match conts with
       | [] -> Done(v, store)
       | (Cont.Runtime(head) :: rest) ->
         (match head with
          | Cont.BinOpL0(op, tm, renv, cenv) ->
            let conts1 = Cont.(Runtime(BinOpR0(op, v))) :: rest in
            InProgress(Config.EvalTerm(0, tm, renv, cenv, conts1, store))
          | Cont.BinOpR0(op, v2) ->
            let result = Primitives.performBinOp op v2 v in
            InProgress(Config.ApplyCont0(rest, result, store))
          | Cont.UniOp0(op) ->
            let result = Primitives.performUniOp op v in
            InProgress(Config.ApplyCont0(rest, result, store))
          | Cont.ShortCircuitOpL0(op, argr, renv, cenv) ->
            (match (op, v) with
             | (ShortCircuitOp.And, Value.Bool false) ->
               InProgress(Config.ApplyCont0(rest, Value.Bool(false), store))
             | (ShortCircuitOp.Or, Value.Bool true) ->
               InProgress(Config.ApplyCont0(rest, Value.Bool(true), store))
             | (ShortCircuitOp.And, Value.Bool true)
             | (ShortCircuitOp.Or, Value.Bool false) ->
               InProgress(Config.EvalTerm(0, argr, renv, cenv, rest, store))
             | _ -> failwith "Expected Bool"
            )
          | Cont.AppL0(tm, renv, cenv) ->
            let conts1 = Cont.(Runtime(AppR0 v)) :: rest in
            InProgress(Config.EvalTerm(0, tm, renv, cenv, conts1, store))
          | Cont.AppR0(func) ->
            (match func with
             | Value.Clos(renv1, cenv1, Term.Lam(var, _, ty, body)) ->
               let renv2 = (var, ty, v) :: renv1 in
               InProgress(Config.EvalTerm(0, body, renv2, cenv1, rest, store))
             | _ -> failwith "expected closure")
          | Cont.RuntimeEval0(renv, cenv) ->
            (match v with
             | Value.Code (Term.Quo(_, body)) ->
               InProgress(Config.EvalTerm(0, body, renv, cenv, rest, store))
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
               let cenv1 = (CodeEnv.Cls(cls1, cls)) :: cenv in
               InProgress(Config.EvalTerm(0, body, renv, cenv1, rest, store))
             | _ -> failwith "expected polycls"
            )
          | Cont.IfCond0(thenn, elsee, renv, cenv) ->
            (match v with
             | (Value.Bool b) ->
               let branch = if b then thenn else elsee in
               InProgress(Config.EvalTerm(0, branch, renv, cenv, rest, store))
             | _ -> failwith "expected boolean")
          | Cont.Fix0 ->
            (match v with
             | Clos(renv1, cenv1, (Lam(self, _, clss, Lam(v, cls, typ, body)) as fixed)) ->
               let eta = Value.Clos(renv1, cenv1, Lam(v, cls, typ, App(Fix fixed, Var(v)))) in
               let renv2 = (self, clss, eta) :: renv1 in
               InProgress(Config.ApplyCont0(rest, (Value.Clos(renv2, cenv1, Lam(v, cls, typ, body))), store))
             | Clos(renv1, cenv1, (Lam(self, _, clss, PolyCls(cls, base, body)) as fixed)) ->
               let eta = Value.Clos(renv1, cenv1, PolyCls(cls, base, AppCls(Fix fixed, cls))) in
               let renv2 = (self, clss, eta) :: renv1 in
               InProgress(Config.ApplyCont0(rest, (Value.Clos(renv2, cenv1, PolyCls(cls, base, body))), store))
             | _ -> failwith "unexpected form of fix")
          | Cont.LetcsVal0(var, ty, cls, def, body, renv, cenv) ->
            let conts1 = Cont.(Runtime(LetcsBody0(var, ty, cls, def, RuntimeEnv.current renv))) :: rest in
            let renv1 = (var, cls, v) :: renv in
            InProgress(Config.EvalTerm(0, body, renv1, cenv, conts1, store))
          | Cont.LetcsBody0(var, ty, cls, def, current_cls) ->
            (match v with
             | Value.Code Term.Quo(_, body) ->
               let result = Value.Code(Term.Quo(current_cls, Term.Letcs(var, ty, cls, def, body))) in
               InProgress(Config.ApplyCont0(rest, result, store))
             | Value.Nil
             | Value.Bool _
             | Value.Int _ ->
               InProgress(Config.ApplyCont0(rest, v, store))
             | _ -> failwith "expected code or primitive values ")
          | Cont.Lift0 cls ->
            (match v with
             | Value.Int i ->
               let result = Value.Code (Term.Quo(cls, Term.Int i)) in
               InProgress(Config.ApplyCont0(rest, result, store))
             | Value.Bool b ->
               let result = Value.Code (Term.Quo(cls, Term.Bool b)) in
               InProgress(Config.ApplyCont0(rest, result, store))
             | _ -> failwith "expected liftable values")
          | Cont.Ref0 ->
            let newloc = Loc.alloc () in
            InProgress(Config.ApplyCont0(rest, Value.Loc newloc, (newloc, v) :: store))
          | Cont.Deref0 ->
            (match v with
             | Value.Loc(loc) ->
               let content = Store.lookup loc store in
               InProgress(Config.ApplyCont0(rest, content, store))
             | _ -> failwith "expected location")
          | Cont.AssignDest0(newval, renv, cenv) ->
            let conts1 = Cont.(Runtime(AssignNewVal0 v)) :: rest in
            InProgress(Config.EvalTerm(0, newval, renv, cenv, conts1, store))
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
       | Cont.Future(head) :: rest ->
         (match head with
          | Cont.BinOpLf(op, tm, renv, cenv) ->
            let conts1 = Cont.(Future(BinOpRf(op, v))) :: rest in
            InProgress(Config.EvalTerm(lv, tm, renv, cenv, conts1, store))
          | Cont.BinOpRf(op, vl) ->
            let result = Term.BinOp(op, vl, v) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
          | Cont.UniOpf(op) ->
            let result = Term.UniOp(op, v) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
          | Cont.ShortCircuitOpLf(op, argr, renv, cenv) ->
            let conts1 = Cont.(Future(ShortCircuitOpRf(op, v))) :: rest in
            InProgress(Config.EvalTerm(lv, argr, renv, cenv, conts1, store))
          | Cont.ShortCircuitOpRf(op, vl) ->
            let result = Term.ShortCircuitOp(op, vl, v) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
          | Cont.Lamf(var, ty, cls) ->
            let result = Term.Lam(var, ty, cls, v) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
          | Cont.AppLf(arg, renv, cenv) ->
            let conts1 = Cont.(Future(AppRf(v))) :: rest in
            InProgress(Config.EvalTerm(lv, arg, renv, cenv, conts1, store))
          | Cont.AppRf(vfunc) ->
            let result = Term.App(vfunc, v) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
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
            let result = Term.PolyCls(cls, base, v) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
          | Cont.AppClsf(cls) ->
            let result = Term.AppCls(v, cls) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
          | Cont.Fixf ->
            let result = Term.Fix v in
            InProgress(Config.ApplyContf(lv, rest, result, store))
          | Cont.IfCondf(thenn, elsee, renv, cenv) ->
            let conts1 = Cont.(Future(IfThenf(v, elsee, renv, cenv))) :: rest in
            InProgress(Config.EvalTerm(lv, thenn, renv, cenv, conts1, store))
          | Cont.IfThenf(condv, elsee, renv, cenv) ->
            let conts1 = Cont.(Future(IfElsef(condv, v))) :: rest in
            InProgress(Config.EvalTerm(lv, elsee, renv, cenv, conts1, store))
          | Cont.IfElsef(condv, thenv) ->
            let result = Term.If(condv, thenv, v) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
          | Cont.LetcsValf(var, ty, cls, body, renv, cenv) ->
            let conts1 = Cont.(Future(LetcsBodyf(var, ty, cls, v))) :: rest in
            InProgress(Config.EvalTerm(lv, body, renv, cenv, conts1, store))
          | Cont.LetcsBodyf(var, ty, cls, vval) ->
            let result = Term.Letcs (var, ty, cls, vval, v) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
          | Cont.Liftf(cls)->
            let result = Term.Lift(cls, v) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
          | Cont.Reff ->
            let result = Term.Ref(v) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
          | Cont.Dereff ->
            let result = Term.Deref(v) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
          | Cont.AssignDestf(newval, renv, cenv) ->
            let conts1 = Cont.(Future(AssignNewValf(v))) :: rest in
            InProgress(Config.EvalTerm(lv, newval, renv, cenv, conts1, store))
          | Cont.AssignNewValf(vdest) ->
            let result = Term.Assign(vdest, v) in
            InProgress(Config.ApplyContf(lv, rest, result, store))
         )
       | Cont.Runtime(_) :: _ ->
         failwith "Ill-formed configuraiton: future value being passed to current continutation"
       | [] ->
         failwith "Ill-formed configuraiton: machine can only exit at runtime"
      ) in
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
