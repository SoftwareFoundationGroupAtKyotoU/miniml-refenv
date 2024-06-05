open Base
open Syntax

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
  well_formed_context ctx &&
  (match ty with
   | Typ.BaseInt -> true
   | Typ.BaseBool -> true
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

  let%test_unit "empty context is ill-formed" =
    assert (not (well_formed_context []))

  let%test_unit "ill-formed contexts : case Init" =
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

let%test_module "well_formed_type" = (module struct
  let g1 = Cls.alloc ()
  let g2 = Cls.alloc ()
  let g3 = Cls.alloc ()
  let g4 = Cls.alloc ()
  let g5 = Cls.alloc ()
  let g6 = Cls.alloc ()

  let v1 = Var.alloc ()
  let v2 = Var.alloc ()

  let ctx = Context.[Init g1; Var(v1, BaseInt, g2); Lock(g3, g1); Var(v2, BaseBool, g4); Unlock(1)] |> List.rev

  let%test_unit "confirm that ctx is well-formed" =
    assert (well_formed_context ctx)

  let%test_unit "type is ill-formed under any ill-formed context" =
    assert (not (well_formed_type [] BaseInt))

  let%test_unit "well-formed types" =
    assert (well_formed_type ctx BaseInt);
    assert (well_formed_type ctx BaseBool);
    assert (well_formed_type ctx (Func(BaseBool, BaseInt)));
    assert (well_formed_type ctx (Code(g2, BaseInt)));
    assert (well_formed_type ctx (PolyCls(g5, g2, BaseInt)));
    assert (well_formed_type ctx (PolyCls(g5, g2, Code(g5, BaseBool))))

  let%test_unit "ill-formed types" =
    assert (not (well_formed_type ctx (Code(g5, BaseInt))));
    assert (not (well_formed_type ctx (PolyCls(g1, g2, BaseInt))));
    assert (not (well_formed_type ctx (PolyCls(g5, g2, Code(g6, BaseBool)))))
end)

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
  if not (well_formed_context ctx) then
    (* We might want to reduce calling well_formed_context *)
    false (* false under invalid context *)
  else if not (let dom = Context.domain_cls ctx in
               (cls1 |> List.mem dom ~equal:Cls.equal) &&
               (cls2 |> List.mem dom ~equal:Cls.equal)) then
    false
  else if Cls.equal cls1 cls2 then
    true (* from reflexivity *)
  else
    Option.(
      lookup_ctx_with_cls ctx cls2 >>= fun ctx2 ->
      (match ctx2 with
       | Context.Init _ :: _ -> return false
       | Context.Var (_, _, _) :: rest ->
         return (reachable_intuitionistic rest cls1 (Context.current rest))
       | Context.Lock (_, base) :: rest
       | Context.Cls (_, base) :: rest ->
         return (reachable_intuitionistic rest cls1 base)
       | _ -> failwith "unreachable")
    ) |> Option.value ~default:false

let%test_module "reachable_intuitionistic" = (module struct
  let g1 = Cls.alloc ()
  let g2 = Cls.alloc ()
  let g3 = Cls.alloc ()
  let g4 = Cls.alloc ()
  let g5 = Cls.alloc ()
  let g6 = Cls.alloc ()

  let v1 = Var.alloc ()
  let v2 = Var.alloc ()
  let v3 = Var.alloc ()

  let ctx = Context.[Init g1; Var(v1, BaseInt, g2); Lock(g3, g1); Var(v2, BaseBool, g4); Unlock(1); Var(v3, BaseInt, g5)] |> List.rev

  let%test_unit "confirm that ctx is well-formed" =
    assert (well_formed_context ctx)

  let%test_unit "always false under ill-formed context" =
    assert (not (reachable_intuitionistic [] g1 g1))

  let%test_unit "always false if classifiers are not in the context" =
    assert (not (reachable_intuitionistic ctx g6 g6))

  let%test_unit "reachable" =
    assert (reachable_intuitionistic ctx g1 g1);
    assert (reachable_intuitionistic ctx g2 g2);
    assert (reachable_intuitionistic ctx g3 g3);
    assert (reachable_intuitionistic ctx g1 g3);
    assert (reachable_intuitionistic ctx g1 g2);
    assert (reachable_intuitionistic ctx g2 g5);
    assert (reachable_intuitionistic ctx g3 g4);
    assert (reachable_intuitionistic ctx g1 g4);
    assert (reachable_intuitionistic ctx g1 g5)

  let%test_unit "not reachable" =
    assert (not (reachable_intuitionistic ctx g2 g1));
    assert (not (reachable_intuitionistic ctx g3 g1));
    assert (not (reachable_intuitionistic ctx g4 g3))
end)

let rec typeinfer (ctx: Context.t) (tm: Term.t): Typ.t option =
  if not (well_formed_context ctx) then
    Option.None
  else
    let open Option in
    (match tm with
     | Term.Int _ -> Option.some Typ.BaseInt
     | Term.Bool _ -> Option.some Typ.BaseBool
     | Term.Const c -> Option.some (Const.typeOf c)
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
     | Term.Fix (term) ->
       typeinfer ctx term >>= fun inferred ->
       (* Since this is call-by-value language, we want to restrict term to
          functions or classifier-functions
       *)
       (match inferred with
        | Typ.(Func(Func(targ1, tret1), Func(targ2, tret2))) ->
          if (Typ.equal targ1 targ2 && Typ.equal tret1 tret2) then
            return (Typ.Func(targ1, tret1))
          else
            Option.None
        | Typ.(Func(PolyCls(cls1, base1, tret1), PolyCls(cls2, base2, tret2))) ->
          if (Typ.equal (PolyCls(cls1, base1, tret1)) (PolyCls(cls2, base2, tret2))) then
            return (Typ.PolyCls(cls1, base1, tret1))
          else
            Option.None
        | _ -> Option.None
       ))

let%test_module "typeinfer" = (module struct
  let g1 = Cls.alloc ()
  let g2 = Cls.alloc ()
  let g3 = Cls.alloc ()
  let g4 = Cls.alloc ()
  let g5 = Cls.alloc ()
  let g6 = Cls.alloc ()

  let v1 = Var.alloc ()
  let v2 = Var.alloc ()
  let v3 = Var.alloc ()

  let%test_unit "failure on ill-formed context" =
    [%test_eq: Typ.t option]
      (typeinfer [] Term.(Lam(v1, BaseInt, g2, Var(v1))))
      Option.None

  let%test_unit "success" =
    [%test_eq: Typ.t option]
      (typeinfer
         Context.[Init g1]
         Term.(Int 1))
      (Option.Some(Typ.BaseInt));
    [%test_eq: Typ.t option]
      (typeinfer
         Context.[Init g1]
         Term.(Bool false))
      (Option.Some(Typ.BaseBool));
    [%test_eq: Typ.t option]
      (typeinfer
         Context.[Init g1]
         Term.(Const Const.Plus))
      (Option.Some(Typ.(Func(BaseInt, Func(BaseInt, BaseInt)))));
    [%test_eq: Typ.t option]
      (typeinfer
         (Context.[Init g1; Var(v1, BaseInt, g2)] |> List.rev)
         Term.(App(App(Const(Const.Plus), Var(v1)), Var(v1))))
      (Option.Some(Typ.BaseInt));
    [%test_eq: Typ.t option]
      (typeinfer
         Context.[Init g1]
         Term.(Lam(v1, BaseInt, g2, Var(v1))))
      (Option.Some(Typ.(Func(BaseInt, BaseInt))));
    [%test_eq: Typ.t option]
      (typeinfer
         (Context.[Init g1; Var(v1, BaseInt, g2)] |> List.rev)
         Term.(Quo(g3, g2, Var(v1))))
      (Option.Some(Typ.(Code(g2, BaseInt))));
    [%test_eq: Typ.t option]
      (typeinfer
         (Context.[Init g1; Var(v1, Code(g1, BaseInt), g2)] |> List.rev)
         Term.(Quo(g3, g1, Unq(1, Var(v1)))))
      (Option.Some(Typ.(Code(g1, BaseInt))));
    [%test_eq: Typ.t option]
      (typeinfer
         (Context.[Init g1; Var(v1, Code(g1, BaseInt), g2)] |> List.rev)
         Term.(Quo(g3, g2, Unq(0, Var(v1)))))
      (Option.Some(Typ.(Code(g2, BaseInt))));
    [%test_eq: Typ.t option] (* eta (\g2:>g1.<int@g2>-><int@g2>)-><int->int@g1> *)
      (typeinfer
         (Context.[Init g1] |> List.rev)
         Term.(Lam(v1, PolyCls(g2, g1, Func(Code(g2, BaseInt), Code(g2, BaseInt))), g2,
                   Quo(g3, g1, Lam(v2, BaseInt, g4,
                                   Unq(1, App(AppCls(Var(v1), g4), Quo(g5, g4, Var(v2)))))))))
      (Option.Some(Typ.(Func(
           PolyCls(g6, g1, Func(Code(g6, BaseInt), Code(g6, BaseInt))),
           Code(g1, Func(BaseInt, BaseInt))))));
    [%test_eq: Typ.t option] (* T-like axiom \g2:>g1.<<int@g2>g2>-><int@g2>*)
      (typeinfer
         (Context.[Init g1] |> List.rev)
         Term.(PolyCls(g2, g1, Lam(v1, Code(g2, Code(g1, BaseInt)), g3,
                                  Quo(g4, g2, Unq(0, Unq(1, Var(v1))))))))
      (Option.Some(Typ.(
           PolyCls(g2, g1, Func(Code(g2, Code(g1, BaseInt)), Code(g2, BaseInt))))));
    [%test_eq: Typ.t option] (* K4-like axiom \g2:>g1.\g6:>g1.<int@g2>-><<int@g2>@g6> *)
      (typeinfer
         (Context.[Init g1] |> List.rev)
         Term.(PolyCls(g2, g1, PolyCls(g6, g1,
                                       Lam(v1, Code(g2, BaseInt), g3,
                                           Quo(g4, g6, Quo(g5, g2, Unq(2, Var(v1)))))))))
      (Option.Some(Typ.(
           PolyCls(g2, g1, PolyCls(g6, g1, Func(Code(g2, BaseInt), Code(g6, Code(g2, BaseInt))))))));
    [%test_eq: Typ.t option]
      (typeinfer
         (Context.[Init g1; Var(v1, BaseInt, g2)] |> List.rev)
         Term.(Fix(Lam(v2, Func(BaseInt, BaseInt), g3,
                       Lam(v3, BaseInt, g4, App(Var(v2), Var(v3)))))))
      (Option.Some(Typ.(Func(BaseInt, BaseInt))));
    [%test_eq: Typ.t option]
      (typeinfer
         (Context.[Init g1; Var(v1, BaseInt, g2)] |> List.rev)
         Term.(Fix(Lam(v2, Func(BaseInt, BaseInt), g3,
                       Lam(v3, BaseInt, g4, App(Var(v2), Var(v3)))))))
      (Option.Some(Typ.(Func(BaseInt, BaseInt))));
    [%test_eq: Typ.t option]
      (typeinfer
         (Context.[Init g1; Var(v1, BaseInt, g2)] |> List.rev)
         Term.(Fix(Lam(v2, PolyCls(g3, g2, BaseInt), g4,
                       PolyCls(g5, g2, Var(v1))))))
      (Option.Some(Typ.(PolyCls(g6, g2, BaseInt))))


  let%test_unit "failure" =
    [%test_eq: Typ.t option]
      (typeinfer
         (Context.[Init g1; Var(v1, Code(g1, BaseInt), g2)] |> List.rev)
         Term.(Quo(g3, g1, Unq(0, Var(v1)))))
      Option.None;
    [%test_eq: Typ.t option]
      (typeinfer
         (Context.[Init g1; Var(v1, Code(g1, BaseInt), g2)] |> List.rev)
         Term.(Var(v2)))
      Option.None;
    [%test_eq: Typ.t option]
      (typeinfer
         (Context.[Init g1; Var(v1, Code(g1, BaseInt), g2)] |> List.rev)
         Term.(Unq(2, Var(v1))))
      Option.None;
    [%test_eq: Typ.t option]
      (typeinfer
         (Context.[Init g1] |> List.rev)
         Term.(Fix(Lam(v1, BaseInt, g1, Var(v1)))))
      Option.None

end)

let typecheck (ctx: Context.t) (tm: Term.t) (ty: Typ.t): bool =
  Option.(
    typeinfer ctx tm >>= fun inferred ->
    return (Typ.equal inferred ty)
  ) |> Option.value ~default:false
