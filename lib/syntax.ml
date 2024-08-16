open Core

module Cls = struct
  module T = struct
    type t =
      | Init
      | Gen of int
      | Raw of string
      | Colored of string * int
    [@@deriving compare, equal, sexp, hash]
  end

  include T
  include Base.Comparator.Make(T)

  type set = (t, comparator_witness) Set.t

  let init = Init

  let counter = Ref.create 0

  let from_string name =
    Raw name

  let gen () =
    let count = !counter in
    counter := count + 1;
    Gen(count)

  let color (orig:t) =
    let count = !counter in
    counter := count + 1;
    (match orig with
     | Init | Gen _ -> Gen(count)
     | Raw name | Colored (name, _) -> Colored(name, count))

  let rename_cls(from:t)(dest:t)(cls:t):t =
    if equal from cls then dest else cls

end

let%test_unit "alloc generate different classifiers" =
  let cls1 = Cls.gen () in
  let cls2 = Cls.gen () in
  assert (Cls.equal cls1 cls1);
  assert (not (Cls.equal cls1 cls2))

module Typ = struct
  module T = struct
    type t =
      | BaseInt
      | BaseBool
      | Func of t * t
      | Code of Cls.t * t
      | PolyCls of Cls.t * Cls.t * t
      | Unit
      | Ref of t
    [@@deriving compare, sexp, hash]
  end

  include T
  include Hashable.Make(T)

  let rec rename_cls (from: Cls.t) (dest: Cls.t) (ty: t) =
    match ty with
    | BaseInt -> BaseInt
    | BaseBool -> BaseBool
    | Func (ty1, ty2) -> Func(ty1 |> rename_cls from dest, ty2 |> rename_cls from dest)
    | Code (base, ty1) ->
      if Cls.equal from base then
        Code(dest, ty1 |> rename_cls from dest)
      else
        Code (base, ty1 |> rename_cls from dest)
    | PolyCls (cls, base, ty1) ->
      if Cls.equal cls from || Cls.equal cls dest then
        failwith "unreachable: cls should be fresh"
      else if Cls.equal from base then
        PolyCls(cls, dest, ty1 |> rename_cls from dest)
      else
        PolyCls(cls, base, ty1 |> rename_cls from dest)
    | Unit -> Unit
    | Ref ty -> Ref (ty |> rename_cls from dest)

  let rec free_cls (typ: t): Cls.set =
    (match typ with
     | BaseInt -> Set.empty (module Cls)
     | BaseBool -> Set.empty (module Cls)
     | Func (ty1, ty2) -> Set.union (free_cls ty1) (free_cls ty2)
     | Code (cls, ty) -> Set.add (free_cls ty) cls
     | PolyCls (cls, base, ty) ->
       (Set.remove (Set.add (free_cls ty) base) cls)
     | Ref ty -> free_cls ty
     | Unit -> Set.empty (module Cls))

  let rec equal (ty1: t) (ty2: t) =
    match (ty1, ty2) with
    | BaseInt, BaseInt -> true
    | BaseBool, BaseBool -> true
    | Func(targ1, tret1), Func(targ2, tret2) -> (equal targ1 targ2) && (equal tret1 tret2)
    | Code(cls1, tbody1), Code(cls2, tbody2) -> (Cls.equal cls1 cls2) && (equal tbody1 tbody2)
    | PolyCls(cls1, base1, tbody1), PolyCls(cls2, base2, tbody2) ->
      (Cls.equal base1 base2) &&
      let clsfresh = Cls.gen () in
      equal (tbody1 |> rename_cls cls1 clsfresh) (tbody2 |> rename_cls cls2 clsfresh)
    | Ref ty1, Ref ty2 -> equal ty1 ty2
    | Unit, Unit -> true
    | _ -> false

  let compare (ty1: t) (ty2: t) =
    if equal ty1 ty2 then 0 else 1
end

let%test_module "subst classifiers in a type" = (module struct
  let cls1 = Cls.gen ()
  let cls2 = Cls.gen ()
  let cls3 = Cls.gen ()

  let%test_unit "equal simple types" =
    [%test_eq: Typ.t] Typ.BaseInt Typ.BaseInt;
    [%test_eq: Typ.t] Typ.BaseBool Typ.BaseBool;
    [%test_eq: Typ.t] Typ.(Func(BaseInt, BaseBool)) Typ.(Func(BaseInt, BaseBool));
    [%test_eq: Typ.t] Typ.(Code(cls1, BaseInt)) Typ.(Code(cls1, BaseInt))

  let%test_unit "different simple types" =
    assert (not (Typ.equal Typ.BaseInt Typ.BaseBool));
    assert (not (Typ.equal Typ.(Func(BaseInt, BaseBool)) Typ.(Func(BaseInt, BaseInt))));
    assert (not (Typ.equal Typ.(Code(cls1, BaseInt)) Typ.(Code(cls2, BaseInt))))

  let%test_unit "equal polymorphic classifier types" =
    [%test_eq: Typ.t] Typ.(PolyCls(cls1, cls2, BaseInt)) Typ.(PolyCls(cls1, cls2, BaseInt));
    [%test_eq: Typ.t] Typ.(PolyCls(cls1, cls2, BaseInt)) Typ.(PolyCls(cls3, cls2, BaseInt));
    [%test_eq: Typ.t]
      Typ.(PolyCls(cls1, cls2, Code(cls1, BaseInt)))
      Typ.(PolyCls(cls3, cls2, Code(cls3, BaseInt)))

  let%test_unit "different polymorphic classifier types" =
    assert (not (Typ.equal
                   Typ.(PolyCls(cls1, cls2, BaseInt))
                   Typ.(PolyCls(cls1, cls3, BaseInt))));
    assert (not (Typ.equal
                   Typ.(PolyCls(cls1, cls2, Code(cls1, BaseInt)))
                   Typ.(PolyCls(cls3, cls2, Code(cls1, BaseInt)))))

end)


let%test_module "subst classifiers in a type" = (module struct
  let g1 = Cls.gen ()
  let g2 = Cls.gen ()
  let g3 = Cls.gen ()

  let%test_unit "case 1" =
    let ty = Typ.(Func(Code(g1, BaseInt), Code(g1, BaseBool))) in
    let sbj = ty |> Typ.rename_cls g1 g2 in
    [%test_eq: Typ.t] sbj Typ.(Func(Code(g2, BaseInt), Code(g2, BaseBool)))

  let%test_unit "case 2" =
    let ty = Typ.(Func(Code(g1, BaseInt), Code(g1, BaseBool))) in
    let sbj = ty |> Typ.rename_cls g2 g3 in
    [%test_eq: Typ.t] sbj Typ.(Func(Code(g1, BaseInt), Code(g1, BaseBool)))

  let%test_unit "case 3" =
    let ty = Typ.(PolyCls(g1, g2, Code(g2, BaseInt))) in
    let sbj = ty |> Typ.rename_cls g2 g3 in
    [%test_eq: Typ.t] sbj Typ.(PolyCls(g1, g3, Code(g3, BaseInt)))
end)

module Var = struct
  type t = Gen of int | Raw of string | Colored of string * int
  [@@deriving compare, equal, sexp, hash]

  let from_string name =
    Raw(name)

  let counter = Ref.create 0

  let gen () =
    let count = !counter in
    counter := count + 1;
    Gen(count)

  let color (orig:t): t =
    let count = !counter in
    counter := count + 1;
    match (orig : t) with
    | Gen _ -> Gen(count)
    | Raw name
    | Colored (name, _) -> Colored(name, count)
end

let%test_unit "alloc generate different variables" =
  let v1 = Var.gen () in
  let v2 = Var.gen () in
  assert (Var.equal v1 v1);
  assert (not (Var.equal v1 v2))

module BinOp = struct
  type t =
    | Plus
    | Mult
    | Minus
    | Div
    | Mod
    | LT
    | Equal
  [@@deriving compare, equal, sexp]
end

module UniOp = struct
  type t =
    | Not
  [@@deriving compare, equal, sexp]
end

module ShortCircuitOp = struct
  type t =
    | And
    | Or
  [@@deriving compare, equal, sexp]
end

module Term = struct
  type t =
    | Int of int
    | Bool of bool
    | BinOp of BinOp.t * t * t
    | UniOp of UniOp.t * t
    | ShortCircuitOp of ShortCircuitOp.t * t * t
    | Var of Var.t
    | Lam of Var.t * Typ.t * Cls.t * t
    | App of t * t
    | Quo of Cls.t * t
    | Unq of int * t
    | PolyCls of Cls.t * Cls.t * t
    | AppCls of t * Cls.t
    | Fix of Var.t * Typ.t * Cls.t * t
    | If of t * t * t
    | Nil
    | Ref of t
    | Deref of t
    | Assign of t * t
    | Letcs of Var.t * Typ.t * Cls.t * t * t
    | Lift of Cls.t * t
  [@@deriving compare, equal, sexp]

  let rec rename_var(from:Var.t)(dest:Var.t)(tm:t): t =
    match (tm : t) with
    | Int _ -> tm
    | Bool _ -> tm
    | BinOp (op, tm1, tm2) ->
      let tm1' = tm1 |> rename_var from dest in
      let tm2' = tm2 |> rename_var from dest in
      BinOp (op, tm1', tm2')
    | UniOp (op, tm1) ->
      let tm1' = tm1 |> rename_var from dest in
      UniOp (op, tm1')
    | ShortCircuitOp (op, tm1, tm2) ->
      let tm1' = tm1 |> rename_var from dest in
      let tm2' = tm2 |> rename_var from dest in
      ShortCircuitOp (op, tm1', tm2')
    | Var v -> if Var.equal from v then Var(dest) else tm
    | Lam (v, typ, cls, body) ->
      if Var.equal from v
      then tm
      else Lam(v, typ, cls, body |> rename_var from dest)
    | App (func, arg) ->
      App (func |> rename_var from dest,
           arg |> rename_var from dest)
    | Quo (base, body) ->
      Quo (base, body |> rename_var from dest)
    | Unq (diff, body) ->
      Unq (diff, body |> rename_var from dest)
    | PolyCls (cls, base, body) ->
      PolyCls (cls, base, body |> rename_var from dest)
    | AppCls (tm, cls) ->
      AppCls (tm |> rename_var from dest, cls)
    | Fix (v, typ, cls, body) ->
      if Var.equal from v
      then tm
      else Fix(v, typ, cls, body |> rename_var from dest)
    | If (cond, thenn, elsee) ->
      If (cond |> rename_var from dest,
          thenn |> rename_var from dest,
          elsee |> rename_var from dest)
    | Nil -> Nil
    | Ref tm -> Ref (tm |> rename_var from dest)
    | Deref tm -> Deref (tm |> rename_var from dest)
    | Assign (loc, newv) ->
      Assign (loc |> rename_var from dest, newv |> rename_var from dest)
    | Letcs (v, cls, ty, e1, e2) ->
      if Var.equal from v
      then tm
      else Letcs (v, cls, ty, e1, e2 |> rename_var from dest)
    | Lift(cls, t) ->
      Lift(cls, t |> rename_var from dest)

  let rec rename_cls(from:Cls.t)(dest:Cls.t)(tm:t): t =
    let apply = Cls.rename_cls from dest in
    match (tm : t) with
    | Int _ -> tm
    | Bool _ -> tm
    | BinOp (op, tm1, tm2) ->
      let tm1' = tm1 |> rename_cls from dest in
      let tm2' = tm2 |> rename_cls from dest in
      BinOp (op, tm1', tm2')
    | UniOp (op, tm1) ->
      let tm1' = tm1 |> rename_cls from dest in
      UniOp (op, tm1')
    | ShortCircuitOp (op, tm1, tm2) ->
      let tm1' = tm1 |> rename_cls from dest in
      let tm2' = tm2 |> rename_cls from dest in
      ShortCircuitOp (op, tm1', tm2')
    | Var _ -> tm
    | Lam (v, ty, cls, body) ->
      let ty2 = ty |> Typ.rename_cls from dest in
      if Cls.equal from cls
      then Lam(v, ty2, cls, body)
      else Lam(v, ty2, cls, body |> rename_cls from dest)
    | App (func, arg) ->
      App (func |> rename_cls from dest,
           arg |> rename_cls from dest)
    | Quo (base, body) ->
      Quo (apply base, body |> rename_cls from dest)
    | Unq (diff, body) ->
      Unq (diff, body |> rename_cls from dest)
    | PolyCls (cls, base, body) ->
      if Cls.equal from cls
      then PolyCls (cls, apply base, body)
      else PolyCls (cls, apply base, body |> rename_cls from dest)
    | AppCls (tm, cls) ->
      AppCls (tm |> rename_cls from dest, apply cls)
    | Fix (v, ty, cls, body) ->
      let ty2 = ty |> Typ.rename_cls from dest in
      if Cls.equal from cls
      then Fix(v, ty2, cls, body)
      else Fix(v, ty2, cls, body |> rename_cls from dest)
    | If (cond, thenn, elsee) ->
      If (cond |> rename_cls from dest,
          thenn |> rename_cls from dest,
          elsee |> rename_cls from dest)
    | Nil -> Nil
    | Ref tm -> Ref (tm |> rename_cls from dest)
    | Deref tm -> Deref (tm |> rename_cls from dest)
    | Assign (loc, newv) ->
      Assign (loc |> rename_cls from dest, newv |> rename_cls from dest)
    | Letcs (v, ty, cls, e1, e2) ->
      let ty2 = ty |> Typ.rename_cls from dest in
      let e1' = e1 |> rename_cls from dest in
      if Cls.equal from cls
      then Letcs (v, ty2, cls, e1', e2)
      else Letcs (v, ty2, cls, e1', e2 |> rename_cls from dest)
    | Lift(cls, t) ->
      if Cls.equal from cls
      then Lift(dest, t |> rename_cls from dest)
      else Lift(cls, t |> rename_cls from dest)

  let rec equal (a : t)(b : t): bool =
    match (a, b) with
    | (Int ai, Int bi) -> Int.equal ai bi
    | (Bool ab, Bool bb) -> Bool.equal ab bb
    | (BinOp(aop, a1, a2), BinOp(bop, b1, b2)) ->
      BinOp.equal aop bop
      && equal a1 b1
      && equal a2 b2
    | (UniOp(aop, a1), UniOp(bop, b1)) ->
      UniOp.equal aop bop
      && equal a1 b1
    | (ShortCircuitOp(aop, a1, a2), ShortCircuitOp(bop, b1, b2)) ->
      ShortCircuitOp.equal aop bop
      && equal a1 b1
      && equal a2 b2
    | (Var av, Var bv) ->
      Var.equal av bv
    | (Lam (av, aty, acls, abody), Lam(bv, bty, bcls, bbody)) ->
      let v' = Var.gen () in
      let cls' = Cls.gen () in
      let abody' = abody |> rename_var av v' |> rename_cls acls cls' in
      let bbody' = bbody |> rename_var bv v' |> rename_cls bcls cls' in
      Typ.equal aty bty && equal abody' bbody'
    | (App (af, aa), App(bf, ba)) ->
      equal af bf && equal aa ba
    | (Quo (acls, abody), Quo (bcls, bbody)) ->
      let cls' = Cls.gen () in
      let abody' = abody |> rename_cls acls cls' in
      let bbody' = bbody |> rename_cls bcls cls' in
      equal abody' bbody'
    | (Unq (adiff, atm), Unq (bdiff, btm)) ->
      Int.equal adiff bdiff && equal atm btm
    | (PolyCls (acls, abase, abody), PolyCls (bcls, bbase, bbody)) ->
      let cls' = Cls.gen () in
      let abody' = abody |> rename_cls acls cls' in
      let bbody' = bbody |> rename_cls bcls cls' in
      Cls.equal abase bbase && equal abody' bbody'
    | (AppCls (atm, abase), AppCls (btm, bbase)) ->
      equal atm btm && Cls.equal abase bbase
    | (Fix (av, aty, acls, abody), Fix(bv, bty, bcls, bbody)) ->
      let v' = Var.gen () in
      let cls' = Cls.gen () in
      let abody' = abody |> rename_var av v' |> rename_cls acls cls' in
      let bbody' = bbody |> rename_var bv v' |> rename_cls bcls cls' in
      Typ.equal aty bty && equal abody' bbody'
    | (If (acond, athen, aelse), If (bcond, bthen, belse)) ->
      equal acond bcond && equal athen bthen && equal aelse belse
    | Nil, Nil -> true
    | Ref a, Ref b -> equal a b
    | Deref a, Deref b -> equal a b
    | Assign (aloc, anew), Assign (bloc, bnew) ->
      equal aloc bloc && equal anew bnew
    | Letcs (va, tya, clsa, e1a, e2a), Letcs (vb, tyb, clsb, e1b, e2b) ->
      let v' = Var.gen () in
      let cls' = Cls.gen () in
      let e2a' = e2a |> rename_var va v' |> rename_cls clsa cls' in
      let e2b' = e2b |> rename_var vb v' |> rename_cls clsb cls' in
      Typ.equal tya tyb
      && equal e1a e1b
      && equal e2a' e2b'
    | Lift (acls, atm), Lift (bcls, btm) ->
      Cls.equal acls bcls && equal atm btm
    | _ -> false

  let compare (a : t)(b : t): int =
    if equal a b
    then 0
    else 1

end

module Context = struct
  module T = struct
    type elm =
      | Init of Cls.t
      | Var of Var.t * Typ.t * Cls.t
      | Lock of Cls.t
      | Unlock of int
      | Cls of Cls.t * Cls.t
    [@@deriving compare, equal, sexp, hash]

    type t = elm list
    [@@deriving compare, equal, sexp, hash]
  end

  include T
  include Hashable.Make(T)

  let empty = [Init(Cls.Init)]
  let from l = (Init(Cls.Init) :: l) |> List.rev

  let rec pop (ctx: t) (diff: int) =
    if diff < 0 then
      failwith "diff must be non-negative integer"
    else if diff = 0 then
      ctx
    else
      (match ctx with
       | Init _ :: _ -> failwith "diff too large"
       | Lock _ :: rest -> pop rest (diff - 1)
       | Unlock (diff2) :: rest -> pop rest (diff + diff2)
       | Var (_, _, _) :: rest
       | Cls (_, _) :: rest ->
         pop rest diff
       | [] -> failwith "unreachable")

  let rec current (ctx: t): Cls.t =
    (match ctx with
     | Init cls :: _ -> cls
     | Var (_, _, cls) :: _ -> cls
     | Lock base :: _ -> base
     | Unlock (diff) :: rest -> current (pop rest diff)
     | Cls (_, _) :: rest -> current rest
     | [] -> failwith "unreachable")

  let rec depth (ctx: t): int =
    (match ctx with
     | Init _ :: _ -> 0
     | Var (_, _, _) :: rest -> depth rest
     | Lock _ :: rest -> depth rest + 1
     | Unlock diff :: rest -> depth rest - diff
     | Cls (_, _) :: rest -> depth rest
     | [] -> failwith "unreachable")

  let domain_cls (ctx: t): Cls.t list =
    let rec recur ctx acc =
      (match ctx with
       | Init cls :: _ -> cls :: acc
       | Var (_, _, cls) :: rest
       | Cls (cls, _) :: rest -> recur rest (cls :: acc)
       | Lock _  :: rest
       | Unlock _ :: rest -> recur rest acc
       | [] -> failwith "unreachable") in
    recur ctx [] |> List.rev

  let domain_var (ctx: t): Var.t list =
    let rec recur ctx acc =
      (match ctx with
       | Init _ :: _ -> acc
       | Var (var, _, _) :: rest -> recur rest (var :: acc)
       | Lock _ :: rest
       | Unlock _ :: rest
       | Cls (_, _) :: rest -> recur rest acc
       | [] -> failwith "unreachable") in
    recur ctx [] |> List.rev

  let rec lookup_var (ctx: t) (v: Var.t): (Typ.t * Cls.t) option =
    (match ctx with
     | Init _ :: _ -> None
     | Var (v1, ty, cls) :: rest ->
       if Var.equal v1 v then Option.some (ty, cls) else lookup_var rest v
     | _ :: rest -> lookup_var rest v
     | [] -> failwith "unreachable")
end

let%test_module "context" = (module struct
  open Context

  let g1 = Cls.init
  let g2 = Cls.gen ()
  let g3 = Cls.gen ()
  let g4 = Cls.gen ()
  let g5 = Cls.gen ()
  let g7 = Cls.gen ()

  let v1 = Var.gen ()
  let v2 = Var.gen ()
  let v3 = Var.gen ()
  let v4 = Var.gen ()

  let ctx1 = Context.from []
  let ctx2 = Context.from [Var(v1, BaseBool, g2)]
  let ctx3 = Context.from [Var(v1, BaseInt, g2); Lock g1]
  let ctx4 = Context.from [Var(v1, BaseInt, g2); Lock g1; Unlock(0)]
  let ctx5 = Context.from [Var(v1, BaseInt, g2); Lock g1; Unlock(0); Unlock(1)]
  let ctx6 = Context.from [Var(v1, BaseInt, g2); Lock g1; Lock g2; Unlock(2)]
  let ctx7 = Context.from [Var(v1, BaseInt, g2); Lock g1; Lock g2; Unlock(1); Unlock(1)]
  let ctx8 = Context.from [Var(v1, BaseInt, g2); Cls(g3, g2)]
  let ctx9 = Context.from [Lock g1; Unlock(1); Lock g1; Unlock(1)]
  let ctx10 = Context.from [Var(v1, BaseInt, g2); Lock g1; Lock g2]
  let ctx11 = Context.from [Var(v1, BaseInt, g2); Var(v2, BaseBool, g3); Lock g1]
  let ctx12 = Context.from [Var(v1, BaseInt, g2); Lock g1; Var(v2, BaseBool, g4); Unlock(1); Var(v3, BaseInt, g5); Lock g2; Var(v4, BaseInt, g7); Unlock(1)]

  let%test_unit "get current classifier" =
    [%test_eq: Cls.t] (current ctx1) g1;
    [%test_eq: Cls.t] (current ctx2) g2;
    [%test_eq: Cls.t] (current ctx3) g1;
    [%test_eq: Cls.t] (current ctx4) g1;
    [%test_eq: Cls.t] (current ctx5) g2;
    [%test_eq: Cls.t] (current ctx6) g2;
    [%test_eq: Cls.t] (current ctx7) g2;
    [%test_eq: Cls.t] (current ctx8) g2;
    [%test_eq: Cls.t] (current ctx9) g1

  let%test_unit "get depth" =
    [%test_eq: int] (depth ctx1) 0;
    [%test_eq: int] (depth ctx2) 0;
    [%test_eq: int] (depth ctx3) 1;
    [%test_eq: int] (depth ctx4) 1;
    [%test_eq: int] (depth ctx5) 0;
    [%test_eq: int] (depth ctx6) 0;
    [%test_eq: int] (depth ctx7) 0;
    [%test_eq: int] (depth ctx8) 0;
    [%test_eq: int] (depth ctx9) 0;
    [%test_eq: int] (depth ctx10) 2

  let%test_unit "get cls domain" =
    [%test_eq: Cls.t list] (domain_cls ctx1) [g1];
    [%test_eq: Cls.t list] (domain_cls ctx2) [g2; g1];
    [%test_eq: Cls.t list] (domain_cls ctx3) [g2; g1];
    [%test_eq: Cls.t list] (domain_cls ctx5) [g2; g1];
    [%test_eq: Cls.t list] (domain_cls ctx8) [g3; g2; g1]

  let%test_unit "get var domain" =
    [%test_eq: Var.t list] (domain_var ctx1) [];
    [%test_eq: Var.t list] (domain_var ctx2) [v1];
    [%test_eq: Var.t list] (domain_var ctx11) [v2; v1];
    [%test_eq: Var.t list] (domain_var ctx12) [v4; v3; v2; v1]

  let%test_unit "lookup a variable" =
    [%test_eq: (Typ.t * Cls.t) option] (lookup_var ctx1 v1) None;
    [%test_eq: (Typ.t * Cls.t) option] (lookup_var ctx2 v1) (Option.some(Typ.BaseBool, g2));
    [%test_eq: (Typ.t * Cls.t) option] (lookup_var ctx2 v2) None;
    [%test_eq: (Typ.t * Cls.t) option] (lookup_var ctx12 v2) (Option.some(Typ.BaseBool, g4));
    [%test_eq: (Typ.t * Cls.t) option] (lookup_var ctx12 v3) (Option.some(Typ.BaseInt, g5));
end)
