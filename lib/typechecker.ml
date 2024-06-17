open Base
open Core
open Syntax

(* Memoize well_formed_context to improve performance *)
let wfc_memo = Hash_set.create (module Context)

let rec well_formed_context (ctx: Context.t): (unit, string) Result.t =
  let open Result in
  let open Result.Let_syntax in
  if Hash_set.mem wfc_memo ctx then
      return ()
  else
    (match ctx with
     | [Context.Init _] -> return ()
     | Context.Var (var, ty, cls) :: ctx ->
       let%bind () = well_formed_context ctx in
       if (var |> List.mem (Context.domain_var ctx) ~equal:Var.equal) then
         fail (Printf.sprintf !"Duplicate variable in the context: %{sexp:Context.t}" ctx)
       else if (cls |> List.mem (Context.domain_cls ctx) ~equal:Cls.equal) then
         fail (Printf.sprintf !"Duplicate variable in the context: %{sexp:Context.t}" ctx)
       else
         well_formed_type ctx ty
     | Context.Lock base :: ctx ->
       let dom_cls = Context.domain_cls ctx in
       let%bind () = well_formed_context ctx in
       Result.ok_if_true
         (base |> List.mem dom_cls ~equal:Cls.equal)
         ~error:(Printf.sprintf !"Undefined classifier %{sexp:Cls.t} in %{sexp:Context.t}" base ctx)
     | Context.Unlock (diff) :: ctx ->
       let%bind () = well_formed_context ctx in
       if diff < 0 then
         fail (Printf.sprintf !"Unlock must carry non-negative diff: %{sexp:Context.t}" ctx)
       else if diff > (Context.depth ctx) then
         fail (Printf.sprintf !"Unlock carries too-big diff: %{sexp:Context.t}" ctx)
       else
         return ()
     | Context.Cls (cls, base) :: ctx ->
       let dom_cls = Context.domain_cls ctx in
       let%bind () = well_formed_context ctx in
       if (cls |> List.mem dom_cls ~equal:Cls.equal) then
         fail (Printf.sprintf !"Duplicate binding classifier %{sexp:Cls.t} in the context: %{sexp:Context.t}" cls ctx)
       else if not (base |> List.mem dom_cls ~equal:Cls.equal) then
         fail (Printf.sprintf !"Reference to undefined classifier %{sexp:Cls.t} in the context: %{sexp:Context.t}" base ctx)
       else
         return ()
     | _ -> fail (Printf.sprintf !"Unexpected form of context: %{sexp:Context.t}" ctx))

    >>= fun ans ->
    Hash_set.add wfc_memo ctx;
    return ans

and well_formed_type (ctx: Context.t) (ty: Typ.t): (unit, string) Result.t =
  let open Result.Let_syntax in
  let%bind () = well_formed_context ctx in
  (match ty with
   | Typ.BaseInt -> return ()
   | Typ.BaseBool -> return ()
   | Typ.Func (ty1, ty2) ->
     let%bind () = well_formed_type ctx ty1 in
     well_formed_type ctx ty2
   | Typ.Code (cls, ty1) ->
     if cls |> List.mem (Context.domain_cls ctx) ~equal:Cls.equal then
       well_formed_type ctx ty1
    else
      Result.fail (Printf.sprintf !"Undefined classifier %{sexp:Cls.t} in the type:%{sexp:Typ.t}" cls ty)
   | Typ.PolyCls (cls, base, ty1) ->
     well_formed_type (Cls(cls, base) :: ctx) ty1
   | Typ.Unit -> return ()
   | Typ.Ref ty ->
     well_formed_type ctx ty
  )

let%test_module "well_formed_context" = (module struct
  open Context
  open Result

  let g1 = Cls.init
  let g2 = Cls.gen ()
  let g3 = Cls.gen ()

  let v1 = Var.gen ()
  let v2 = Var.gen ()

  let%test_unit "well-formed contexts" =
    assert (well_formed_context [Init g1] |> is_ok);
    assert (well_formed_context (from [Var(v1, BaseInt, g2)]) |> is_ok);
    assert (well_formed_context (from [Var(v1, BaseInt, g2); Var(v2, BaseInt, g3)]) |> is_ok);
    assert (well_formed_context (from [Lock g1; Var(v1, BaseInt, g3)]) |> is_ok);
    assert (well_formed_context (from [Lock g1; Lock g1]) |> is_ok);
    assert (well_formed_context (from [Lock g1; Unlock(1)]) |> is_ok);
    assert (well_formed_context (from [Lock g1; Unlock(0)]) |> is_ok);
    assert (well_formed_context (from [Cls(g2, g1)]) |> is_ok)

  let%test_unit "empty context is ill-formed" =
    assert (well_formed_context [] |> is_error)

  let%test_unit "ill-formed contexts : case Init" =
    assert (well_formed_context [Init g1; Init g2] |> is_error)

  let%test_unit "ill-formed contexts : case Var" =
    assert (well_formed_context (from [Var(v1, BaseInt, g1)]) |> is_error);
    assert (well_formed_context (from [Var(v1, Code(g2, BaseInt), g2)]) |> is_error);
    assert (well_formed_context (from [Var(v1, BaseInt, g2); Var(v1, BaseInt, g3)]) |> is_error);
    assert (well_formed_context (from [Var(v1, BaseInt, g2); Var(v2, BaseInt, g2)]) |> is_error);
    assert (well_formed_context (from [Var(v1, BaseInt, g1); Var(v2, BaseInt, g2)]) |> is_error)

  let%test_unit "ill-formed contexts : case Lock" =
    assert (well_formed_context (from [Lock g3]) |> is_error)

  let%test_unit "ill-formed contexts : case Unlock" =
    assert (well_formed_context (from [Lock g1; Unlock(2)]) |> is_error);
    assert (well_formed_context (from [Lock g1; Unlock(44)]) |> is_error);
    assert (well_formed_context (from [Lock g1; Unlock(-1)]) |> is_error)

  let%test_unit "ill-formed contexts : case Cls" =
    assert (well_formed_context (from [Cls(g2, g2)]) |> is_error);
    assert (well_formed_context (from [Cls(g1, g1)]) |> is_error);
    assert (well_formed_context (from [Cls(g2, g1); Cls(g1, g2)]) |> is_error);
end)

let%test_module "well_formed_type" = (module struct
  let g1 = Cls.init
  let g2 = Cls.gen ()
  let g4 = Cls.gen ()
  let g5 = Cls.gen ()
  let g6 = Cls.gen ()

  let v1 = Var.gen ()
  let v2 = Var.gen ()

  let ctx = Context.(from [
      Var(v1, BaseInt, g2);
      Lock g1;
      Var(v2, BaseBool, g4);
      Unlock(1)
    ])

  let%test_unit "confirm that ctx is well-formed" =
    assert (well_formed_context ctx |> is_ok)

  let%test_unit "type is ill-formed under any ill-formed context" =
    assert (well_formed_type [] BaseInt |> is_error)

  let%test_unit "well-formed types" =
    assert (well_formed_type ctx BaseInt |> is_ok);
    assert (well_formed_type ctx BaseBool |> is_ok);
    assert (well_formed_type ctx (Func(BaseBool, BaseInt)) |> is_ok);
    assert (well_formed_type ctx (Code(g2, BaseInt)) |> is_ok);
    assert (well_formed_type ctx (PolyCls(g5, g2, BaseInt)) |> is_ok);
    assert (well_formed_type ctx (PolyCls(g5, g2, Code(g5, BaseBool))) |> is_ok)

  let%test_unit "ill-formed types" =
    assert (well_formed_type ctx (Code(g5, BaseInt)) |> is_error);
    assert (well_formed_type ctx (PolyCls(g1, g2, BaseInt)) |> is_error);
    assert (well_formed_type ctx (PolyCls(g5, g2, Code(g6, BaseBool))) |> is_error)
end)

let rec lookup_ctx_with_cls (ctx: Context.t) (cls: Cls.t): Context.t option =
  match ctx with
  | Context.Init cls1 :: _ ->
    if Cls.equal cls1 cls
    then Some ctx
    else None
  | Context.Var (_, _, cls1) :: rest
  | Context.Cls (cls1, _) :: rest ->
    if Cls.equal cls1 cls
    then Some ctx
    else lookup_ctx_with_cls rest cls
  | Context.Lock _ :: rest
  | Context.Unlock _ :: rest ->
    lookup_ctx_with_cls rest cls
  | [] -> failwith "unreachable branch"

let rec reachable_intuitionistic (ctx: Context.t) (cls1: Cls.t) (cls2: Cls.t): bool =
  if well_formed_context ctx |> Result.is_error then
    (* We might want to reduce calling well_formed_context *)
    false (* false under invalid context *)
  else if not (let dom = Context.domain_cls ctx in
               (cls1 |> List.mem dom ~equal:Cls.equal) &&
               (cls2 |> List.mem dom ~equal:Cls.equal)) then
    false
  else if Cls.equal cls1 cls2 then
    true (* from reflexivity *)
  else
    let open Option.Let_syntax in
    (
      let%bind ctx2 = lookup_ctx_with_cls ctx cls2 in
      (match ctx2 with
       | [(Context.Init _)] -> return false
       | Context.Var (_, _, _) :: rest ->
         return (reachable_intuitionistic rest cls1 (Context.current rest))
       | Context.Cls (_, base) :: rest ->
         return (reachable_intuitionistic rest cls1 base)
       | _ -> failwith "unreachable branch")
    ) |> Option.value ~default:false

let%test_module "reachable_intuitionistic" = (module struct
  let g1 = Cls.init
  let g2 = Cls.gen ()
  let g3 = Cls.gen ()
  let g4 = Cls.gen ()
  let g5 = Cls.gen ()
  let g6 = Cls.gen ()

  let v1 = Var.gen ()
  let v2 = Var.gen ()
  let v3 = Var.gen ()

  let ctx = Context.(from [
      Var(v1, BaseInt, g2);
      Lock g1;
      Var(v2, BaseBool, g4);
      Unlock(1);
      Var(v3, BaseInt, g5)
    ])

  let%test_unit "confirm that ctx is well-formed" =
    assert (well_formed_context ctx |> is_ok)
  let%test_unit "always false under ill-formed context" =
    assert (not (reachable_intuitionistic [] g1 g1))

  let%test_unit "always false if classifiers are not in the context" =
    assert (not (reachable_intuitionistic ctx g6 g6))

  let%test_unit "reachable" =
    assert (reachable_intuitionistic ctx g1 g1);
    assert (reachable_intuitionistic ctx g2 g2);
    assert (reachable_intuitionistic ctx g1 g2);
    assert (reachable_intuitionistic ctx g2 g5);
    assert (reachable_intuitionistic ctx g1 g4);
    assert (reachable_intuitionistic ctx g1 g5)

  let%test_unit "not reachable" =
    assert (not (reachable_intuitionistic ctx g2 g1));
    assert (not (reachable_intuitionistic ctx g3 g1));
    assert (not (reachable_intuitionistic ctx g4 g3))
end)

let type_error (tm: Term.t)(expect: Typ.t)(got: Typ.t): ('a, string) Result.t =
  Result.fail (Printf.sprintf !"expected %{sexp:Term.t} to have type %{sexp:Typ.t}, but got %{sexp:Typ.t}" tm expect got)

let type_error_form (tm: Term.t)(expect: string)(got: Typ.t): ('a, string) Result.t =
  Result.fail (Printf.sprintf !"expected %{sexp:Term.t} to have type %s, but got %{sexp:Typ.t}" tm expect got)

let rec typeinfer (toplevel: bool) (ctx: Context.t) (tm: Term.t): (Typ.t, string) Result.t =
  let open Result in
  let open Result.Let_syntax in
  let%bind () = (well_formed_context ctx) in
  (match tm with
   | Term.Int _ -> return Typ.BaseInt
   | Term.Bool _ -> return Typ.BaseBool
   | Term.BinOp (op, tm1, tm2) ->
     let%bind inferred1 = typeinfer false ctx tm1 in
     let%bind inferred2 = typeinfer false ctx tm2 in
     (match op with
      | BinOp.Plus
      | BinOp.Mult
      | BinOp.Minus
      | BinOp.Div
      | BinOp.Mod ->
        (match (inferred1, inferred2) with
         | (Typ.BaseInt, Typ.BaseInt) -> return Typ.BaseInt
         | (_, Typ.BaseInt) ->
           type_error tm1 Typ.BaseInt inferred1
         | _ ->
           type_error tm2 Typ.BaseInt inferred2)
      | BinOp.LT
      | BinOp.Equal ->
        (match (inferred1, inferred2) with
         | (Typ.BaseInt, Typ.BaseInt) -> return Typ.BaseBool
         | (_, Typ.BaseInt) ->
           type_error tm1 Typ.BaseInt inferred1
         | _ ->
           type_error tm2 Typ.BaseInt inferred2))
   | Term.UniOp (op, tm) ->
     let%bind inferred = typeinfer false ctx tm in
     (match op with
      | UniOp.Not ->
        match inferred with
        | Typ.BaseBool -> return Typ.BaseBool
        | _ ->
          type_error tm Typ.BaseInt inferred)
   | Term.ShortCircuitOp (op, tm1, tm2) ->
     let%bind inferred1 = typeinfer false ctx tm1 in
     let%bind inferred2 = typeinfer false ctx tm2 in
     (match op with
      | ShortCircuitOp.And
      | ShortCircuitOp.Or ->
        (match (inferred1, inferred2) with
         | (Typ.BaseBool, Typ.BaseBool) -> return Typ.BaseBool
         | (_, Typ.BaseBool) ->
           type_error tm1 Typ.BaseBool inferred1
         | _ ->
           type_error tm2 Typ.BaseBool inferred2)
     )
   | Term.Var v ->
     (match Context.lookup_var ctx v with
      | Some (ty, cls) ->
        if (reachable_intuitionistic ctx cls (Context.current ctx)) then
          return ty
        else
          fail (sprintf !"The variable %{sexp:Var.t} cannot be used because its classifier %{sexp:Cls.t} is not reachable from %{sexp:Cls.t}"
                  v cls (Context.current ctx))
      | None -> fail (sprintf !"Undefined variable: %{sexp:Var.t}" v))
   | Term.Lam (v, ty, cls, body) ->
     (* rename v and cls to fresh identifiers to avoid shadowing *)
     let v' = Var.color v in
     let cls' = Cls.color cls in
     let body' = body
                 |> Term.rename_var v v'
                 |> Term.rename_cls cls cls' in
     let ctx2 = Context.Var(v', ty, cls') :: ctx in
     let%bind inferred = typeinfer false ctx2 body' in
     if cls' |> Set.mem (Typ.free_cls inferred) then
       fail (sprintf !"Functions cannot return code with its own scope: %{sexp:Term.t}" tm)
     else
       return (Typ.Func(ty, inferred))
   | Term.App (func, arg) ->
     let%bind tyfunc = typeinfer false ctx func in
     let%bind tyarg = typeinfer false ctx arg in
     (match tyfunc with
      | Func(tyfunc1, tyfunc2) ->
        if Typ.equal tyfunc1 tyarg
        then return tyfunc2
        else type_error arg tyfunc1 tyarg
      | _ -> type_error_form func "function type" tyfunc)
   | Term.Quo (base, body) ->
     (* rename cls to avoid shadowing *)
     let ctx2 = Context.Lock base :: ctx in
     let%bind inferred = typeinfer toplevel ctx2 body in
     return (Typ.Code(base, inferred))
   | Term.Unq (diff, quot) ->
     let ctx2 = Context.Unlock(diff) :: ctx in
     let%bind inferred = typeinfer false ctx2 quot in
     (match inferred with
      | Code(base, ty2) ->
        if reachable_intuitionistic ctx base (Context.current ctx) then
          return ty2
        else
          fail (sprintf !"The quote %{sexp:Term.t} cannot be unquoted because its classifier %{sexp:Cls.t} is not reachable from %{sexp:Cls.t}"
                  tm base (Context.current ctx))
      | _ -> type_error_form quot "code type" inferred)
   | Term.PolyCls (cls, base, body) ->
     (* rename cls to avoid shadowing *)
     let cls' = Cls.color cls in
     let body' = body |> Term.rename_cls cls cls' in
     let ctx2 = Context.Cls(cls', base) :: ctx in
     let%bind inferred = typeinfer false ctx2 body' in
     return (Typ.PolyCls(cls', base, inferred))
   | Term.AppCls (quot, cls) ->
     if cls |> List.mem (Context.domain_cls ctx) ~equal:Cls.equal then
       let%bind inferred = typeinfer false ctx quot in
       (match inferred with
        | PolyCls(cls1, base, ty1) ->
          if reachable_intuitionistic ctx base cls then
            return (ty1 |> Typ.rename_cls cls1 cls)
          else
            fail (sprintf !"The classifier application %{sexp:Term.t} is invalid because %{sexp:Cls.t} is not reachable from %{sexp:Cls.t}"
                 tm cls base)
        | _ -> type_error_form quot "polymorphic classifier type" inferred)
     else
       fail (sprintf !"The term %{sexp:Term.t} uses an undefined classifier %{sexp:Cls.t}" tm cls)
   | Term.Fix (term) ->
     let%bind inferred = typeinfer false ctx term in
     (* Since this is call-by-value language, we want to restrict term to
        functions or classifier-functions
     *)
     (match inferred with
      | Typ.(Func(Func(targ1, tret1), Func(targ2, tret2))) ->
        if (Typ.equal targ1 targ2 && Typ.equal tret1 tret2) then
          return (Typ.Func(targ1, tret1))
        else
          type_error_form tm "Func(Func(a, b), Func(a, b))" inferred
      | Typ.(Func(PolyCls(cls1, base1, tret1), PolyCls(cls2, base2, tret2))) ->
        if (Typ.equal (PolyCls(cls1, base1, tret1)) (PolyCls(cls2, base2, tret2))) then
          return (Typ.PolyCls(cls1, base1, tret1))
        else
          type_error_form tm "Func(PolyCls(g1, g2, a), PolyCls(g1, g2, a))" inferred
      | _ -> type_error_form tm "Func(Func(a, b), Func(a, b)) or Func(PolyCls(g1, g2, a), PolyCls(g1, g2, a))" inferred
     )
   | Term.If(cond, thenn, elsee) ->
     let%bind tycond = typeinfer false ctx cond in
     let%bind tythen = typeinfer false ctx thenn in
     let%bind tyelse = typeinfer false ctx elsee in
     if Typ.equal tycond Typ.BaseBool && Typ.equal tythen tyelse then
       return tythen
     else
       type_error elsee tythen tyelse
   | Term.Nil -> return Typ.Unit
   | Term.Ref tm ->
     let%bind inferred = typeinfer false ctx tm in
     return (Typ.Ref inferred)
   | Term.Deref ref ->
     let%bind inferred = typeinfer false ctx ref in
     (match inferred with
      | Ref ty -> return ty
      | _ -> type_error_form ref "Ref(a)" inferred)
   | Term.Assign (loc, newv) ->
     let%bind locinf = typeinfer false ctx loc in
     let%bind newinf = typeinfer false ctx newv in
     (match (locinf, newinf) with
      | Ref ty1, ty2 ->
        if Typ.equal ty1 ty2
        then return Typ.Unit
        else type_error newv ty1 ty2
      | _ -> type_error_form loc "Ref(a)" locinf
     )
   | Term.Letcs (v, ty, cls, e1, e2) ->
     if not toplevel then
       fail (sprintf !"Non-toplevel cross-stage definitions are not allowed: %{sexp:Term.t}" tm)
     else
       let%bind e1inf = typeinfer false ctx e1 in
       let ctx2 = Context.Var(v, ty, cls) :: ctx in
       let%bind e2inf = typeinfer true ctx2 e2 in
       if Typ.equal e1inf ty then
         return (e2inf |> Typ.rename_cls cls (Context.current ctx))
       else
         type_error e1 ty e1inf
  )

let%test_module "typeinfer" = (module struct
  open Result

  let g1 = Cls.init
  let g2 = Cls.gen ()
  let g3 = Cls.gen ()
  let g4 = Cls.gen ()
  let g5 = Cls.gen ()
  let g6 = Cls.gen ()

  let v1 = Var.gen ()
  let v2 = Var.gen ()
  let v3 = Var.gen ()

  let%test_unit "failure on ill-formed context" =
    assert (is_error
      (typeinfer true [] Term.(Lam(v1, BaseInt, g2, Var(v1)))))

  let%test_unit "literals" =
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.[Init g1]
         Term.(Int 1))
      ~expect:(return Typ.BaseInt);
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.[Init g1]
         Term.(Bool false))
      ~expect:(return Typ.BaseBool)

  let%test_unit "Binary operators" =
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.(from [Var(v1, BaseInt, g2)])
         Term.(BinOp(BinOp.Plus, Var(v1), Var(v1))))
      ~expect:(return Typ.BaseInt);
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.(from [Var(v1, BaseInt, g2)])
         Term.(BinOp(BinOp.LT, Var(v1), Var(v1))))
      ~expect:(return Typ.BaseBool)

  let%test_unit "Unary operators" =
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.(from [Var(v1, BaseBool, g2)])
         Term.(UniOp(UniOp.Not, Var(v1))))
      ~expect:(return Typ.BaseBool)

    let%test_unit "Shortcircuit operators" =
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.(from [Var(v1, BaseBool, g2)])
         Term.(ShortCircuitOp(ShortCircuitOp.And, Var(v1), Var(v1))))
      ~expect:(return Typ.BaseBool)

  let%test_unit "variables" =
    assert (is_error
      (typeinfer true
         Context.(from [Var(v1, Code(g1, BaseInt), g2)])
         Term.(Var(v2))));
    assert (is_error
      (typeinfer true
         Context.(from [Var(v1, Code(g1, BaseInt), g2)])
         Term.(Unq(2, Var(v1)))))

  let%test_unit "lambda" =
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.empty
         Term.(Lam(v1, BaseInt, g2, Var(v1))))
      ~expect:(return Typ.(Func(BaseInt, BaseInt)));
    (* classifier of lambda cannot appear freely in the resulting type *)
    assert (is_error
      (typeinfer true
         Context.empty
         Term.(Lam(v1, BaseInt, g2, Quo(g2, Var(v1))))));
    (* lambda cannot carry an ill-formed type *)
    assert (is_error
      (typeinfer true
         Context.empty
         Term.(Lam(v1, Code(g3, BaseInt) (* This type is ill-formed *), g2,
                   Var(v1)))))

  let%test_unit "quo and unq" =
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.(from [Var(v1, BaseInt, g2)])
         Term.(Quo(g2, Var(v1))))
      ~expect:(return Typ.(Code(g2, BaseInt)));
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.(from [Var(v1, Code(g1, BaseInt), g2)])
         Term.(Quo(g1, Unq(1, Var(v1)))))
      ~expect:(return Typ.(Code(g1, BaseInt)));
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.(from [Var(v1, Code(g1, BaseInt), g2)])
         Term.(Quo(g2, Unq(0, Var(v1)))))
      ~expect:(return Typ.(Code(g2, BaseInt)));
    assert (is_error
      (typeinfer true
         Context.(from [Var(v1, Code(g1, BaseInt), g2)])
         Term.(Quo(g1, Unq(0, Var(v1))))))

  let%test_unit "polymorphic contexts" =
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.empty
         Term.(PolyCls(g2, g1, Quo(g2, Int(1)))))
      ~expect:(return Typ.(PolyCls(g4, g1, Code(g4, BaseInt))));
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.empty
         Term.(PolyCls(g1, g1, Quo(g1, Int(1)))))
      ~expect:(return Typ.(PolyCls(g4, g1, Code(g4, BaseInt))));
    assert (is_error
      (typeinfer true
         Context.empty
         Term.(PolyCls(g2, g3, Quo(g1, Int(1))))))

    let%test_unit "context applications" =
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.(from [Var(v1, PolyCls(g2, g1, Code(g2, BaseInt)), g3); Cls(g4, g3)])
           Term.(AppCls(Var(v1), g4)))
        ~expect:(return Typ.(Code(g4, BaseInt)));
      assert (is_error
        (typeinfer true
           Context.(from [Var(v1, BaseInt, g2); Var(v2, PolyCls(g3, g2, Code(g3, BaseInt)), g4)])
           Term.(AppCls(Var(v2), g1))))

  let%test_unit "fix" =
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.(from [Var(v1, BaseInt, g2)])
         Term.(Fix(Lam(v2, Func(BaseInt, BaseInt), g3,
                       Lam(v3, BaseInt, g4, App(Var(v2), Var(v3)))))))
      ~expect:(return Typ.(Func(BaseInt, BaseInt)));
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.(from [Var(v1, BaseInt, g2)])
         Term.(Fix(Lam(v2, Func(BaseInt, BaseInt), g3,
                       Lam(v3, BaseInt, g4, App(Var(v2), Var(v3)))))))
      ~expect:(return Typ.(Func(BaseInt, BaseInt)));
    [%test_result: (Typ.t, string) Result.t]
      (typeinfer true
         Context.(from [Var(v1, BaseInt, g2)])
         Term.(Fix(Lam(v2, PolyCls(g3, g2, BaseInt), g4,
                       PolyCls(g5, g2, Var(v1))))))
      ~expect:(return Typ.(PolyCls(g6, g2, BaseInt)));
    (assert (is_error
      (typeinfer true
         Context.empty
         Term.(Fix(Lam(v1, BaseInt, g1, Var(v1)))))))

    let%test_unit "if-statement" =
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.empty
           Term.(If(Bool(true), Int(1), Int(2))))
        ~expect:(return Typ.(BaseInt));
      assert (is_error
        (typeinfer true
           Context.empty
           Term.(If(Bool(true), Int(1), Bool(false)))));
      assert (is_error
        (typeinfer true
           Context.empty
           Term.(If(Int(1), Int(1), Int(2)))))

    let%test_unit "unit" =
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.empty
           Term.Nil)
        ~expect:(return Typ.Unit);
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.(from [Var (v1, Typ.(Func(Unit, BaseInt)), g2)])
           Term.(App(Var v1, Nil)))
        ~expect:(return Typ.BaseInt)

    let%test_unit "ref" =
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.empty
           Term.(Ref (Int 10)))
        ~expect:(return Typ.(Ref BaseInt));
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.empty
           Term.(Ref (Quo(Cls.init, Int 1))))
        ~expect:(return Typ.(Ref (Code(Cls.init, BaseInt))));
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.empty
           Term.(Deref (Ref (Int 10))))
        ~expect:(return Typ.BaseInt);
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.empty
           Term.(Deref (Ref (Int 10))))
        ~expect:(return Typ.BaseInt);
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.(from [Var (v1, Typ.(Ref BaseInt), g2)])
           Term.(Assign (Var v1, Int 10)))
        ~expect:(return Typ.Unit)

    let%test_unit "cross stage definitions" =
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.empty
           Term.(Letcs(v1, Typ.BaseInt, g2, Int(10), Quo(g2, Var(v1)))))
        ~expect:(return Typ.(Code(g1, BaseInt)));
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.empty
           Term.(Letcs(v1, Typ.BaseInt, g2, Int(10), Quo(g1, Int(0)))))
        ~expect:(return Typ.(Code(g1, BaseInt)));
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.empty
           Term.(Letcs(v1, Typ.BaseInt, g2, Int(10),
                      Letcs(v2, Typ.BaseInt, g3, Int(11), Quo(g3, Var(v2))))))
        ~expect:(return Typ.(Code(g1, BaseInt)))


    let%test_unit "shadowing" =
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.empty
           Term.(Lam(v1, BaseInt, g2, Lam(v1, BaseInt, g2, Var(v1)))))
        ~expect:(return Typ.(Func(BaseInt, Func(BaseInt, BaseInt))));
      [%test_result: (Typ.t, string) Result.t]
        (typeinfer true
           Context.empty
           Term.(Lam(v1, BaseInt, g2, PolyCls(g2, Cls.init, Int(1)))))
        ~expect:(return Typ.(Func(BaseInt, PolyCls(g3, Cls.init, BaseInt))))

    let%test_unit "complex cases: axioms" =
    [%test_result: (Typ.t, string) Result.t] (* eta (\g2:>g1.<int@g2>-><int@g2>)-><int->int@g1> *)
      (typeinfer true
         Context.empty
         Term.(Lam(v1, PolyCls(g2, g1, Func(Code(g2, BaseInt), Code(g2, BaseInt))), g2,
                   Quo(g1, Lam(v2, BaseInt, g4,
                               Unq(1, App(AppCls(Var(v1), g4), Quo(g4, Var(v2)))))))))
      ~expect:(return Typ.(Func(
          PolyCls(g6, g1, Func(Code(g6, BaseInt), Code(g6, BaseInt))),
          Code(g1, Func(BaseInt, BaseInt)))));
    [%test_result: (Typ.t, string) Result.t] (* T-like axiom \g2:>g1.<<int@g2>g2>-><int@g2>*)
      (typeinfer true
         Context.empty
         Term.(PolyCls(g2, g1, Lam(v1, Code(g2, Code(g1, BaseInt)), g3,
                                   Quo(g2, Unq(0, Unq(1, Var(v1))))))))
      ~expect:(return Typ.(
          PolyCls(g2, g1, Func(Code(g2, Code(g1, BaseInt)), Code(g2, BaseInt)))));
    [%test_result: (Typ.t, string) Result.t] (* K4-like axiom \g2:>g1.\g6:>g1.<int@g2>-><<int@g2>@g6> *)
      (typeinfer true
         Context.empty
         Term.(PolyCls(g2, g1, PolyCls(g6, g1,
                                       Lam(v1, Code(g2, BaseInt), g3,
                                           Quo(g6, Quo(g2, Unq(2, Var(v1)))))))))
      ~expect:(return Typ.(
          PolyCls(g2, g1, PolyCls(g6, g1, Func(Code(g2, BaseInt), Code(g6, Code(g2, BaseInt)))))))

end)

let typecheck (toplevel: bool) (ctx: Context.t) (tm: Term.t) (ty: Typ.t): (unit, string) Result.t =
  let open Result.Let_syntax in
  let%bind inferred = typeinfer toplevel ctx tm in
  if Typ.equal inferred ty then
    return ()
  else
    type_error tm ty inferred
