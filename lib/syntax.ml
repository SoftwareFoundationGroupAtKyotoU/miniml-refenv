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

let%test "alloc generate different classifiers" =
  let cls1 = Cls.alloc () in
  let cls2 = Cls.alloc () in
  Cls.equal cls1 cls1 &&
  not (Cls.equal cls1 cls2)

module Typ = struct
  type t =
    | BaseInt
    | BaseStr
    | Func of t * t
    | Code of Cls.t * t
    | PolyCls of Cls.t * Cls.t * t
  [@@deriving compare, equal, sexp]

  let rec subst_cls (from: Cls.t) (dest: Cls.t) (ty: t) =
    match ty with
    | BaseInt -> BaseInt
    | BaseStr -> BaseStr
    | Func (ty1, ty2) -> Func(ty1 |> subst_cls from dest, ty2 |> subst_cls from dest)
    | Code (base, ty1) ->
      if Cls.equal from base then
        Code(dest, ty1 |> subst_cls from dest)
      else
        Code (base, ty1 |> subst_cls from dest)
    | PolyCls (cls, base, ty1) ->
      if Cls.equal from base then
        PolyCls(cls, dest, ty1 |> subst_cls from dest)
      else
        PolyCls(cls, base, ty1 |> subst_cls from dest)
end

module Var = struct
  type t = int
  [@@deriving compare, equal, sexp]
end

module Term = struct
  type t =
    | Var of Var.t
    | Lam of Var.t * Typ.t * Cls.t * t
    | App of t * t
    | Quo of Cls.t * Cls.t * t
    | Unq of int * t
    | PolyCls of Cls.t * Cls.t * t
    | AppCls of t * Cls.t
  [@@deriving compare, equal, sexp]
end

module Context = struct
  type t =
    | Init of Cls.t
    | Var of t * Var.t * Typ.t * Cls.t
    | Lock of t * Cls.t * Cls.t
    | Unlock of t * int
    | Cls of t * Cls.t * Cls.t
  [@@deriving compare, equal, sexp]

  let rec pop (ctx: t) (diff: int) =
    if diff < 0 then
      failwith "diff must be non-negative integer"
    else if diff = 0 then
      ctx
    else
      (match ctx with
       | Init _ -> failwith "diff too large"
       | Var (rest, _, _, _) -> pop rest diff
       | Lock (rest, _, _) -> pop rest (diff - 1)
       | Unlock (rest, diff2) -> pop rest (diff + diff2)
       | Cls (rest, _, _) -> pop rest diff)

  let rec current (ctx: t): Cls.t =
    (match ctx with
     | Init cls -> cls
     | Var (_, _, _, cls) -> cls
     | Lock (_, cls, _) -> cls
     | Unlock (rest, diff) -> current (pop rest diff)
     | Cls (rest, _, _) -> current rest)

  let rec depth (ctx: t): int =
    (match ctx with
     | Init _ -> 0
     | Var (rest, _, _, _) -> depth rest
     | Lock (rest, _, _) -> depth rest + 1
     | Unlock (rest, diff) -> depth rest - diff
     | Cls (rest, _, _) -> depth rest)

  let domain_cls (ctx: t): Cls.t list =
    let rec recur ctx acc =
      (match ctx with
       | Init cls -> cls :: acc
       | Var (rest, _, _, cls) -> recur rest (cls :: acc)
       | Lock (rest, cls, _) -> recur rest (cls :: acc)
       | Unlock (rest, _) -> recur rest acc
       | Cls (rest, cls, _) -> recur rest (cls :: acc)) in
    recur ctx [] |> List.rev

  let domain_var (ctx: t): Var.t list =
    let rec recur ctx acc =
      (match ctx with
       | Init _ -> []
       | Var (rest, var, _, _) -> recur rest (var :: acc)
       | Lock (rest, _, _) -> recur rest acc
       | Unlock (rest, _) -> recur rest acc
       | Cls (rest, _, _) -> recur rest acc) in
    recur ctx [] |> List.rev

  let rec lookup_var (ctx: t) (v: Var.t): (Typ.t * Cls.t) option =
    (match ctx with
     | Init _ -> Option.None
     | Var (rest, v1, ty, cls) ->
       if Var.equal v1 v then Option.some (ty, cls) else lookup_var rest v
     | Lock (rest, _, _) -> lookup_var rest v
     | Unlock (rest, _) -> lookup_var rest v
     | Cls (rest, _, _) -> lookup_var rest v)
end

