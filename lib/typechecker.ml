open Base
open Syntax

let rec lookup_ctx_with_cls (ctx: Context.t) (cls: Cls.t): Context.t option =
  let open Option in
  match ctx with
  | Context.Init cls1 ->
    if Cls.equal cls1 cls
    then Some ctx
    else None
  | Context.Var (rest, _, _, cls1) ->
    if Cls.equal cls1 cls
    then Some ctx
    else lookup_ctx_with_cls rest cls
  | Context.Lock (rest, cls1, _) ->
    if Cls.equal cls1 cls
    then Some ctx
    else lookup_ctx_with_cls rest cls
  | Context.Unlock (rest, _) -> lookup_ctx_with_cls rest cls
  | Context.Cls (rest, cls1, _) ->
    if Cls.equal cls1 cls
    then Some ctx
    else lookup_ctx_with_cls rest cls

let rec reachable_intuitionistic (ctx: Context.t) (cls1: Cls.t) (cls2: Cls.t): bool =
  if Cls.equal cls1 cls2
  then true (* from reflexivity *)
  else
    let open Option in
    (lookup_ctx_with_cls ctx cls2 >>= fun ctx2 ->
     (match ctx2 with
      | Context.Init _ ->
        failwith "unreachable"
      | Context.Var (rest, _, _, _) ->
        return (reachable_intuitionistic rest cls1 (Context.current rest))
      | Context.Lock (rest, _, base) ->
        return (reachable_intuitionistic rest cls1 base)
      | Context.Unlock (_, _) ->
        failwith "unreachable"
      | Context.Cls (rest, _, base) ->
        return (reachable_intuitionistic rest cls1 base)))
    |> value ~default:false

let rec typeinfer (ctx: Context.t) (tm: Term.t): Typ.t option =
  let open Option in
  (match tm with
   | Term.Var v ->
     Context.lookup_var ctx v >>= fun (ty, cls) ->
     ty |> some_if (reachable_intuitionistic ctx cls (Context.current ctx))
   | Term.Lam (v, ty, cls, body) ->
     let ctx2 = Context.Var(ctx, v, ty, cls) in
     typeinfer ctx2 body >>= fun ineferred ->
     return (Typ.Func(ty, ineferred))
   | Term.App (func, arg) ->
     typeinfer ctx func >>= fun tyfunc ->
     typeinfer ctx arg >>= fun tyarg ->
     (match tyfunc with
      | Func(tyfunc1, tyfunc2) ->
        if Typ.equal tyfunc1 tyarg then
          return tyfunc2
        else
          None
      | _ -> None)
   | Term.Quo (cls, base, body) ->
     let ctx2 = Context.Lock(ctx, cls, base) in
     typeinfer ctx2 body >>= fun inferred ->
     return (Typ.Code(base, inferred))
   | Term.Unq (diff, body) ->
     let ctx2 = Context.Unlock(ctx, diff) in
     typeinfer ctx2 body >>= fun inferred ->
     (match inferred with
      | Code(base, ty2) ->
        if reachable_intuitionistic ctx base (Context.current ctx) then
          return ty2
        else
          None
      | _ -> None)
   | Term.PolyCls (cls, base, body) ->
     let ctx2 = Context.Cls(ctx, cls, base) in
     typeinfer ctx2 body >>= fun inferred ->
     return (Typ.PolyCls(cls, base, inferred))
   | Term.AppCls (tm, cls) ->
     if cls |> List.mem (Context.domain_cls ctx) ~equal:Cls.equal then
       typeinfer ctx tm >>= fun inferred ->
       (match inferred with
        | PolyCls(cls1, base, ty1) ->
          if reachable_intuitionistic ctx base cls then
            return (ty1 |> Typ.subst_cls cls1 cls)
          else
            None
        | _ -> None)
     else
       None
  )

let typecheck (ctx: Context.t) (tm: Term.t) (ty: Typ.t): bool =
  let open Option in
  (typeinfer ctx tm >>= fun inferred ->
   return (Typ.equal inferred ty))
  |> Option.value ~default:false

let rec well_formed_context (ctx: Context.t): bool =
  (match ctx with
   | Init _ -> true
   | Var (ctx, var, ty, cls) ->
     well_formed_context ctx &&
     not (var |> List.mem (Context.domain_var ctx) ~equal:Var.equal) &&
     not (cls |> List.mem (Context.domain_cls ctx) ~equal:Cls.equal) &&
     well_formed_type ctx ty
   | Lock (ctx, cls, base) ->
     let dom_cls = Context.domain_cls ctx in
     well_formed_context ctx &&
     (base |> List.mem dom_cls ~equal:Cls.equal) &&
     not (cls |> List.mem dom_cls ~equal:Cls.equal)
   | Unlock (ctx, diff) ->
     well_formed_context ctx &&
     diff <= (Context.depth ctx)
   | Cls (ctx, cls, base) ->
     let dom_cls = Context.domain_cls ctx in
     well_formed_context ctx &&
     (base |> List.mem dom_cls ~equal:Cls.equal) &&
     not (cls |> List.mem dom_cls ~equal:Cls.equal))

and well_formed_type (ctx: Context.t) (ty: Typ.t): bool =
  (match ty with
   | BaseInt -> true
   | BaseStr -> true
   | Func (ty1, ty2) ->
     well_formed_type ctx ty1 &&
     well_formed_type ctx ty2
   | Code (cls, ty1) ->
     (cls |> List.mem (Context.domain_cls ctx) ~equal:Cls.equal) &&
     well_formed_type ctx ty1
   | PolyCls (cls, base, ty1) ->
     well_formed_type (Cls(ctx, cls, base)) ty1)
