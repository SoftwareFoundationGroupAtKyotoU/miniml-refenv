open Base
open Syntax

module RuntimeEnv = struct
  type 'a t = (Var.t * 'a) list

  let rec lookup_var(v:Var.t)(env:'a t): 'a =
    match env with
    | [] -> failwith "failed to lookup var"
    | (v1, value) :: rest ->
      if Var.equal v v1
      then value
      else rest |> lookup_var v
end

module CodeEnv = struct
  type elm =
    | Var of Var.t * Var.t
    | Cls of Cls.t * Cls.t

  type t = elm list

  let rec rename_var(v:Var.t)(env: t): Var.t =
    match env with
    | [] -> failwith "failed to look up"
    | Var(from, dest) :: rest ->
        if Var.equal v from
        then dest
        else rest |> rename_var v
    | _ :: rest -> rest |> rename_var v

  let rec rename_cls(cls:Cls.t)(env: t): Cls.t =
    match env with
    | [] -> cls
    | Cls(from, dest) :: rest ->
        if Cls.equal cls from
        then dest
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
      let cls' = Cls.alloc () in
      let base' = env |> rename_cls base in
      let ty' = ty |> Typ.rename_cls cls cls' in
      let ty' = env |> rename_cls_in_typ ty' in
      Typ.PolyCls (cls', base', ty')
end

module Value = struct
  type t =
    | Int of int
    | Bool of bool
    | Const of Const.t
    | Clos of t RuntimeEnv.t * Term.t
    | Code of Term.t
    | Fut of Term.t
end

let rec eval(lv:int)(renv:Value.t RuntimeEnv.t)(cenv: CodeEnv.t)(k:Value.t -> Value.t)(tm:Term.t): Value.t =
  (match (lv, tm) with
   | (0, Term.Int i) -> Value.Int i |> k
   | (0, Term.Bool b) -> Value.Bool b |> k
   | (0, Term.Const c) -> Value.Const c |> k
   | (0, Term.Var v) -> renv |> RuntimeEnv.lookup_var v |> k
   | (0, Term.Lam _) -> Value.Clos (renv, tm) |> k
   | (0, Term.App (func, arg)) ->
     func |> eval 0 renv cenv (fun funcv -> arg |> eval 0 renv cenv (fun argv ->
         match funcv with
         | Clos(env', Lam(var, _, _, body)) ->
           body |> eval 0 ((var, argv) :: env') cenv k
         | _ -> failwith "hoge 0 app"))
   | (0, Term.Quo (cls, body)) ->
     body |> eval 1 renv cenv (fun futv ->
         match futv with
         | Fut t -> Code (Quo(cenv |> CodeEnv.rename_cls cls, t))
         | _ -> failwith "fuga 0 quo"
       )
   | (0, Term.Unq (0, tm)) ->
     tm |> eval 0 renv cenv (fun v ->
         match v with
         | Code(Quo(_, body)) ->
           body |> eval 0 renv cenv k
         | _ -> failwith "fuga 0 unq"
       )
     | (0, Term.PolyCls (_, _, _)) -> Value.Clos (renv, tm) |> k
     | (0, Term.AppCls (tm, cls1)) ->
       tm |> eval 0 renv cenv (fun v -> match v with
           | Clos(renv', PolyCls(cls2, _, body)) ->
             body |> eval 0 renv' (CodeEnv.Cls(cls2, cls1)::cenv) k
           | _ -> failwith "hogege 0 appcls")
     | (0, Term.Fix f) ->
       Term.(App(f,(Fix f))) |> eval 0 renv cenv k
     | (0, Term.If (cond, thenn, elsee)) ->
       cond |> eval 0 renv cenv (fun condv ->
           (match condv with
           | Value.Bool(true) -> thenn
           | Value.Bool(false) -> elsee
           | _ -> failwith "hoge 0 if")
           |> eval 0 renv cenv k
         )
     | (_, Term.Int _) -> Value.Fut tm |> k
     | (_, Term.Bool _) -> Value.Fut tm |> k
     | (_, Term.Const _) -> Value.Fut tm |> k
     | (_, Term.Var v) -> Value.Fut (Term.Var(cenv |> CodeEnv.rename_var v)) |> k
     | (l, Term.Lam(v, typ, cls, body)) ->
       let v' = Var.alloc () in
       let cls' = Cls.alloc() in
       let typ' = cenv |> CodeEnv.rename_cls_in_typ typ in
       let cenv' = (CodeEnv.(Var(v, v') :: Cls(cls, cls') :: cenv)) in
       body |> eval l renv cenv' (fun v ->
           match v with
           | Fut body' -> Fut (Lam(v', typ', cls', body'))
           | _ -> failwith "hoge l lam")
     | (l, Term.App(func, arg)) ->
       func |> eval l renv cenv (fun funcv ->
           arg |> eval l renv cenv (fun argv ->
               match (funcv, argv) with
               | (Fut(fbody), Fut(abody)) -> Fut(Term.App(fbody, abody))
               | _ -> failwith "hoge l app"
             ))
     | (l, Term.Quo(base, body)) ->
       body |> eval (l+1) renv cenv (fun v ->
           let base' = cenv |> CodeEnv.rename_cls base in
           match v with
           | Fut(v) -> Fut(Quo(base', v))
           | _ -> failwith "hoge l quo")
     | (l, Term.Unq(diff, tm)) ->
       if equal l diff then
         tm |> eval 0 renv cenv (fun v ->
             (match v with
              | Code(Quo(_, body)) -> Fut(body)
              | _ -> failwith "hoge l=diff unq"))
       else
         tm |> eval (l - diff) renv cenv (fun v ->
             (match v with
              | Fut(body) -> Fut(Term.Unq(diff, body))
              | _ -> failwith "hoge l>diff unq"))
     | (l, Term.PolyCls(cls, base, body)) ->
       let cls' = Cls.alloc() in
       let base' = cenv |> CodeEnv.rename_cls base in
       let cenv' = (CodeEnv.(Cls(cls, cls') :: cenv)) in
       body |> eval l renv cenv' (fun v ->
           match v with
           | Fut(bodyv) -> Fut(Term.PolyCls(cls', base', bodyv))
           | _ -> failwith "hoge l polycls")
     | (l, Term.AppCls(tm, cls)) ->
       let cls' = cenv |> CodeEnv.rename_cls cls in
       tm |> eval l renv cenv (fun v ->
           match v with
           | Fut body -> Fut(AppCls(body, cls'))
           | _ -> failwith "hoge l appcls")
     | (l, Term.Fix(f)) ->
       f |> eval l renv cenv (fun v -> match v with
           | Fut body -> Fut(Fix body)
           | _ -> failwith "hoge l fix")
     | (l, Term.If(cond, thenn, elsee)) ->
       cond  |> eval l renv cenv (fun condv ->
           thenn |> eval l renv cenv (fun thenv ->
               elsee |> eval l renv cenv (fun elsev ->
                   match (condv, thenv, elsev) with
                   | (Fut(cbody), Fut(tbody), Fut(ebody)) ->
                     Fut(Term.If(cbody, tbody, ebody))
                   | _ -> failwith "hoge l if"
                 )))
  )
