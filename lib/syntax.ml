open Base

module Cls = struct
  type t = Cls of int
  [@@deriving compare, equal, sexp]

  let counter = Ref.create 0

  let alloc () =
    let count = !counter in
    counter := count + 1;
    Cls(count)
end

let%test_unit "alloc generate different classifiers" =
  let cls1 = Cls.alloc () in
  let cls2 = Cls.alloc () in
  assert (Cls.equal cls1 cls1);
  assert (not (Cls.equal cls1 cls2))

module Typ = struct
  type t =
    | BaseInt
    | BaseBool
    | Func of t * t
    | Code of Cls.t * t
    | PolyCls of Cls.t * Cls.t * t
  [@@deriving compare, sexp]

  let rec subst_cls (from: Cls.t) (dest: Cls.t) (ty: t) =
    match ty with
    | BaseInt -> BaseInt
    | BaseBool -> BaseBool
    | Func (ty1, ty2) -> Func(ty1 |> subst_cls from dest, ty2 |> subst_cls from dest)
    | Code (base, ty1) ->
      if Cls.equal from base then
        Code(dest, ty1 |> subst_cls from dest)
      else
        Code (base, ty1 |> subst_cls from dest)
    | PolyCls (cls, base, ty1) ->
      if Cls.equal cls from || Cls.equal cls dest then
        failwith "unreachable: cls should be fresh"
      else if Cls.equal from base then
        PolyCls(cls, dest, ty1 |> subst_cls from dest)
      else
        PolyCls(cls, base, ty1 |> subst_cls from dest)

  let rec equal (ty1: t) (ty2: t) =
    match (ty1, ty2) with
    | BaseInt, BaseInt -> true
    | BaseBool, BaseBool -> true
    | Func(targ1, tret1), Func(targ2, tret2) -> (equal targ1 targ2) && (equal tret1 tret2)
    | Code(cls1, tbody1), Code(cls2, tbody2) -> (Cls.equal cls1 cls2) && (equal tbody1 tbody2)
    | PolyCls(cls1, base1, tbody1), PolyCls(cls2, base2, tbody2) ->
      (Cls.equal base1 base2) &&
      let clsfresh = Cls.alloc () in
      equal (tbody1 |> subst_cls cls1 clsfresh) (tbody2 |> subst_cls cls2 clsfresh)
    | _ -> false

  let compare (ty1: t) (ty2: t) =
    if equal ty1 ty2 then 0 else 1
end

let%test_module "subst classifiers in a type" = (module struct
  let cls1 = Cls.alloc ()
  let cls2 = Cls.alloc ()
  let cls3 = Cls.alloc ()

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
  let g1 = Cls.alloc ()
  let g2 = Cls.alloc ()
  let g3 = Cls.alloc ()

  let%test_unit "case 1" =
    let ty = Typ.(Func(Code(g1, BaseInt), Code(g1, BaseBool))) in
    let sbj = ty |> Typ.subst_cls g1 g2 in
    [%test_eq: Typ.t] sbj Typ.(Func(Code(g2, BaseInt), Code(g2, BaseBool)))

  let%test_unit "case 2" =
    let ty = Typ.(Func(Code(g1, BaseInt), Code(g1, BaseBool))) in
    let sbj = ty |> Typ.subst_cls g2 g3 in
    [%test_eq: Typ.t] sbj Typ.(Func(Code(g1, BaseInt), Code(g1, BaseBool)))

  let%test_unit "case 3" =
    let ty = Typ.(PolyCls(g1, g2, Code(g2, BaseInt))) in
    let sbj = ty |> Typ.subst_cls g2 g3 in
    [%test_eq: Typ.t] sbj Typ.(PolyCls(g1, g3, Code(g3, BaseInt)))
end)

module Var = struct
  type t = Var of int
  [@@deriving compare, equal, sexp]

  let counter = Ref.create 0

  let alloc () =
    let count = !counter in
    counter := count + 1;
    Var(count)
end

let%test_unit "alloc generate different variables" =
  let v1 = Var.alloc () in
  let v2 = Var.alloc () in
  assert (Var.equal v1 v1);
  assert (not (Var.equal v1 v2))

module Const = struct
  type t =
    (* Arithmetic operators *)
    | Plus
    | Minus
    | Mult
    | GE
    (* Boolean operators *)
    | Neg
    | And
    | Or
  [@@deriving compare, equal, sexp]

  let typeOf (x : t) : Typ.t = match x with
    | Plus ->  Typ.Func(Typ.BaseInt, Typ.Func(Typ.BaseInt, Typ.BaseInt))
    | Minus -> Typ.Func(Typ.BaseInt, Typ.Func(Typ.BaseInt, Typ.BaseInt))
    | Mult ->  Typ.Func(Typ.BaseInt, Typ.Func(Typ.BaseInt, Typ.BaseInt))
    | GE ->    Typ.Func(Typ.BaseInt, Typ.Func(Typ.BaseInt, Typ.BaseBool))
    | Neg ->   Typ.Func(Typ.BaseBool, Typ.BaseBool)
    | And ->   Typ.Func(Typ.BaseBool, Typ.Func(Typ.BaseBool, Typ.BaseBool))
    | Or ->    Typ.Func(Typ.BaseBool, Typ.Func(Typ.BaseBool, Typ.BaseBool))
end

module Term = struct
  type t =
    | Int of int
    | Bool of bool
    | Const of Const.t
    | Var of Var.t
    | Lam of Var.t * Typ.t * Cls.t * t
    | App of t * t
    | Quo of Cls.t * Cls.t * t
    | Unq of int * t
    | PolyCls of Cls.t * Cls.t * t
    | AppCls of t * Cls.t
    | Fix of t
    | If of t * t * t
  [@@deriving compare, equal, sexp]
end

module Context = struct
  type elm =
    | Init of Cls.t
    | Var of Var.t * Typ.t * Cls.t
    | Lock of Cls.t * Cls.t
    | Unlock of int
    | Cls of Cls.t * Cls.t
  [@@deriving compare, equal, sexp]

  type t = elm list
  [@@deriving compare, equal, sexp]

  let rec pop (ctx: t) (diff: int) =
    if diff < 0 then
      failwith "diff must be non-negative integer"
    else if diff = 0 then
      ctx
    else
      (match ctx with
       | Init _ :: _ -> failwith "diff too large"
       | Lock (_, _) :: rest -> pop rest (diff - 1)
       | Unlock (diff2) :: rest -> pop rest (diff + diff2)
       | Var (_, _, _) :: rest
       | Cls (_, _) :: rest ->
         pop rest diff
       | [] -> failwith "unreachable")

  let rec current (ctx: t): Cls.t =
    (match ctx with
     | Init cls :: _ -> cls
     | Var (_, _, cls) :: _ -> cls
     | Lock (cls, _) :: _ -> cls
     | Unlock (diff) :: rest -> current (pop rest diff)
     | Cls (_, _) :: rest -> current rest
     | [] -> failwith "unreachable")

  let rec depth (ctx: t): int =
    (match ctx with
     | Init _ :: _ -> 0
     | Var (_, _, _) :: rest -> depth rest
     | Lock (_, _) :: rest -> depth rest + 1
     | Unlock (diff) :: rest -> depth rest - diff
     | Cls (_, _) :: rest -> depth rest
     | [] -> failwith "unreachable")

  let domain_cls (ctx: t): Cls.t list =
    let rec recur ctx acc =
      (match ctx with
       | Init cls :: _ -> cls :: acc
       | Var (_, _, cls) :: rest
       | Lock (cls, _) :: rest
       | Cls (cls, _) :: rest -> recur rest (cls :: acc)
       | Unlock (_) :: rest -> recur rest acc
       | [] -> failwith "unreachable") in
    recur ctx [] |> List.rev

  let domain_var (ctx: t): Var.t list =
    let rec recur ctx acc =
      (match ctx with
       | Init _ :: _ -> acc
       | Var (var, _, _) :: rest -> recur rest (var :: acc)
       | Lock (_, _) :: rest
       | Unlock (_) :: rest
       | Cls (_, _) :: rest -> recur rest acc
       | [] -> failwith "unreachable") in
    recur ctx [] |> List.rev

  let rec lookup_var (ctx: t) (v: Var.t): (Typ.t * Cls.t) option =
    (match ctx with
     | Init _ :: _ -> Option.None
     | Var (v1, ty, cls) :: rest ->
       if Var.equal v1 v then Option.some (ty, cls) else lookup_var rest v
     | _ :: rest -> lookup_var rest v
     | [] -> failwith "unreachable")
end

let%test_module "context" = (module struct
  open Context

  let g1 = Cls.alloc ()
  let g2 = Cls.alloc ()
  let g3 = Cls.alloc ()
  let g4 = Cls.alloc ()
  let g5 = Cls.alloc ()
  let g6 = Cls.alloc ()
  let g7 = Cls.alloc ()

  let v1 = Var.alloc ()
  let v2 = Var.alloc ()
  let v3 = Var.alloc ()
  let v4 = Var.alloc ()

  let ctx1 = [Init g1]
  let ctx2 = [Init g1; Var(v1, BaseBool, g2)] |> List.rev
  let ctx3 = [Init g1; Var(v1, BaseInt, g2); Lock(g3, g1)] |> List.rev
  let ctx4 = [Init g1; Var(v1, BaseInt, g2); Lock(g3, g1); Unlock(0)] |> List.rev
  let ctx5 = [Init g1; Var(v1, BaseInt, g2); Lock(g3, g1); Unlock(0); Unlock(1)] |> List.rev
  let ctx6 = [Init g1; Var(v1, BaseInt, g2); Lock(g3, g1); Lock(g4, g2); Unlock(2)] |> List.rev
  let ctx7 = [Init g1; Var(v1, BaseInt, g2); Lock(g3, g1); Lock(g4, g2); Unlock(1); Unlock(1)] |> List.rev
  let ctx8 = [Init g1; Var(v1, BaseInt, g2); Cls(g3, g2)] |> List.rev
  let ctx9 = [Init g1; Lock(g2, g1); Unlock(1); Lock(g3, g2); Unlock(1)] |> List.rev
  let ctx10 = [Init g1; Var(v1, BaseInt, g2); Lock(g3, g1); Lock(g4, g2)] |> List.rev
  let ctx11 = [Init g1; Var(v1, BaseInt, g2); Var(v2, BaseBool, g3); Lock(g4, g1)] |> List.rev
  let ctx12 = [Init g1; Var(v1, BaseInt, g2); Lock(g3, g1); Var(v2, BaseBool, g4); Unlock(1); Var(v3, BaseInt, g5); Lock(g6, g2); Var(v4, BaseInt, g7); Unlock(1)] |> List.rev

  let%test_unit "get current classifier" =
    [%test_eq: Cls.t] (current ctx1) g1;
    [%test_eq: Cls.t] (current ctx2) g2;
    [%test_eq: Cls.t] (current ctx3) g3;
    [%test_eq: Cls.t] (current ctx4) g3;
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
    [%test_eq: Cls.t list] (domain_cls ctx3) [g3; g2; g1];
    [%test_eq: Cls.t list] (domain_cls ctx4) [g3; g2; g1];
    [%test_eq: Cls.t list] (domain_cls ctx5) [g3; g2; g1];
    [%test_eq: Cls.t list] (domain_cls ctx6) [g4; g3; g2; g1];
    [%test_eq: Cls.t list] (domain_cls ctx8) [g3; g2; g1];
    [%test_eq: Cls.t list] (domain_cls ctx9) [g3; g2; g1];
    [%test_eq: Cls.t list] (domain_cls ctx10) [g4; g3; g2; g1]

  let%test_unit "get var domain" =
    [%test_eq: Var.t list] (domain_var ctx1) [];
    [%test_eq: Var.t list] (domain_var ctx2) [v1];
    [%test_eq: Var.t list] (domain_var ctx11) [v2; v1];
    [%test_eq: Var.t list] (domain_var ctx12) [v4; v3; v2; v1]

  let%test_unit "lookup a variable" =
    [%test_eq: (Typ.t * Cls.t) option] (lookup_var ctx1 v1) Option.None;
    [%test_eq: (Typ.t * Cls.t) option] (lookup_var ctx2 v1) (Option.Some(BaseBool, g2));
    [%test_eq: (Typ.t * Cls.t) option] (lookup_var ctx2 v2) Option.None;
    [%test_eq: (Typ.t * Cls.t) option] (lookup_var ctx12 v2) (Option.Some(BaseBool, g4));
    [%test_eq: (Typ.t * Cls.t) option] (lookup_var ctx12 v3) (Option.Some(BaseInt, g5));
end)
