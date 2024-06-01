open Base
open Syntax

let rec lookup_ctx_with_cls (ctx: Context.t) (cls: Cls.t): Context.t option =
  match ctx with
  | Context.Init cls1 :: _ ->
    if Cls.equal cls1 cls
    then Some ctx
    else None
  | Context.Var (_, _, cls1) :: rest
  | Context.Lock (cls1, _) :: rest
  | Context.Cls (cls1, _) :: rest ->
    if Cls.equal cls1 cls
    then Some ctx
    else lookup_ctx_with_cls rest cls
  | Context.Unlock (_) :: rest -> lookup_ctx_with_cls rest cls
  | [] -> failwith "unreachable"

let rec reachable_intuitionistic (ctx: Context.t) (cls1: Cls.t) (cls2: Cls.t): bool =
  if Cls.equal cls1 cls2
  then true (* from reflexivity *)
  else
    Option.(
      lookup_ctx_with_cls ctx cls2 >>= fun ctx2 ->
      (match ctx2 with
       | Context.Var (_, _, _) :: rest ->
         return (reachable_intuitionistic rest cls1 (Context.current rest))
       | Context.Lock (_, base) :: rest
       | Context.Cls (_, base) :: rest ->
         return (reachable_intuitionistic rest cls1 base)
       | _ -> failwith "unreachable")
    ) |> Option.value ~default:false

let rec typeinfer (ctx: Context.t) (tm: Term.t): Typ.t option =
  let open Option in
  (match tm with
   | Term.Var v ->
     Context.lookup_var ctx v >>= fun (ty, cls) ->
     ty |> some_if (reachable_intuitionistic ctx cls (Context.current ctx))
   | Term.Lam (v, ty, cls, body) ->
     let ctx2 = Context.Var(v, ty, cls) :: ctx in
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
     let ctx2 = Context.Lock(cls, base) :: ctx in
     typeinfer ctx2 body >>= fun inferred ->
     return (Typ.Code(base, inferred))
   | Term.Unq (diff, body) ->
     let ctx2 = Context.Unlock(diff) :: ctx in
     typeinfer ctx2 body >>= fun inferred ->
     (match inferred with
      | Code(base, ty2) ->
        if reachable_intuitionistic ctx base (Context.current ctx) then
          return ty2
        else
          None
      | _ -> None)
   | Term.PolyCls (cls, base, body) ->
     let ctx2 = Context.Cls(cls, base) :: ctx in
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
  Option.(
    typeinfer ctx tm >>= fun inferred ->
    return (Typ.equal inferred ty)
  ) |> Option.value ~default:false

let rec well_formed_context (ctx: Context.t): bool =
  (match ctx with
   | [Context.Init _] -> true
   | Context.Var (var, ty, cls) :: ctx ->
     well_formed_context ctx &&
     not (var |> List.mem (Context.domain_var ctx) ~equal:Var.equal) &&
     not (cls |> List.mem (Context.domain_cls ctx) ~equal:Cls.equal) &&
     well_formed_type ctx ty
   | Context.Lock (cls, base) :: ctx ->
     let dom_cls = Context.domain_cls ctx in
     well_formed_context ctx &&
     (base |> List.mem dom_cls ~equal:Cls.equal) &&
     not (cls |> List.mem dom_cls ~equal:Cls.equal)
   | Context.Unlock (diff) :: ctx ->
     well_formed_context ctx &&
     diff >= 0 &&
     diff <= (Context.depth ctx)
   | Context.Cls (cls, base) :: ctx ->
     let dom_cls = Context.domain_cls ctx in
     well_formed_context ctx &&
     (base |> List.mem dom_cls ~equal:Cls.equal) &&
     not (cls |> List.mem dom_cls ~equal:Cls.equal)
   | _ -> false)

and well_formed_type (ctx: Context.t) (ty: Typ.t): bool =
  (match ty with
   | Typ.BaseInt -> true
   | Typ.BaseStr -> true
   | Typ.Func (ty1, ty2) ->
     well_formed_type ctx ty1 &&
     well_formed_type ctx ty2
   | Typ.Code (cls, ty1) ->
     (cls |> List.mem (Context.domain_cls ctx) ~equal:Cls.equal) &&
     well_formed_type ctx ty1
   | Typ.PolyCls (cls, base, ty1) ->
     well_formed_type (Cls(cls, base) :: ctx) ty1)

let%test_module "well_formed_context" = (module struct
  open Context

  let g1 = Cls.alloc ()
  let g2 = Cls.alloc ()
  let g3 = Cls.alloc ()

  let v1 = Var.alloc ()
  let v2 = Var.alloc ()

  let%test_unit "well-formed contexts" =
    assert (well_formed_context [Init g1]);
    assert (well_formed_context ([Init g1; Var(v1, BaseInt, g2)] |> List.rev));
    assert (well_formed_context ([Init g1; Var(v1, BaseInt, g2); Var(v2, BaseInt, g3)] |> List.rev));
    assert (well_formed_context ([Init g1; Lock(g2, g1); Var(v1, BaseInt, g3)] |> List.rev));
    assert (well_formed_context ([Init g1; Lock(g2, g1); Lock(g3, g1)] |> List.rev));
    assert (well_formed_context ([Init g1; Lock(g2, g1); Unlock(1)] |> List.rev));
    assert (well_formed_context ([Init g1; Lock(g2, g1); Unlock(0)] |> List.rev));
    assert (well_formed_context ([Init g1; Cls(g2, g1)] |> List.rev))

  let%test_unit "ill-formed contexts : case Init" =
    assert (not (well_formed_context []));
    assert (not (well_formed_context [Init g1; Init g2]))

  let%test_unit "ill-formed contexts : case Var" =
    assert (not (well_formed_context ([Init g1; Var(v1, BaseInt, g1)] |> List.rev)));
    assert (not (well_formed_context ([Init g1; Var(v1, Code(g2, BaseInt), g2)] |> List.rev)));
    assert (not (well_formed_context ([Init g1; Var(v1, BaseInt, g2); Var(v1, BaseInt, g3)] |> List.rev)));
    assert (not (well_formed_context ([Init g1; Var(v1, BaseInt, g2); Var(v2, BaseInt, g2)] |> List.rev)));
    assert (not (well_formed_context ([Init g1; Var(v1, BaseInt, g1); Var(v2, BaseInt, g2)] |> List.rev)))

  let%test_unit "ill-formed contexts : case Lock" =
    assert (not (well_formed_context ([Init g1; Lock(g2, g3)] |> List.rev)));
    assert (not (well_formed_context ([Init g1; Lock(g1, g1)] |> List.rev)));
    assert (not (well_formed_context ([Init g1; Lock(g2, g1); Lock(g3, g3)] |> List.rev)))

  let%test_unit "ill-formed contexts : case Unlock" =
    assert (not (well_formed_context ([Init g1; Lock(g2, g1); Unlock(2)] |> List.rev)));
    assert (not (well_formed_context ([Init g1; Lock(g2, g1); Unlock(44)] |> List.rev)));
    assert (not (well_formed_context ([Init g1; Lock(g2, g1); Unlock(-1)] |> List.rev)))

  let%test_unit "ill-formed contexts : case Cls" =
    assert (not (well_formed_context ([Init g1; Cls(g2, g2)] |> List.rev)));
    assert (not (well_formed_context ([Init g1; Cls(g1, g1)] |> List.rev)));
    assert (not (well_formed_context ([Init g1; Cls(g2, g1); Cls(g1, g2)] |> List.rev)));
end)
