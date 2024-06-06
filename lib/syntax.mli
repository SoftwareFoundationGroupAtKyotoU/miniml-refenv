open Base

module Cls: sig
  type t
  [@@deriving compare, equal, sexp]

  val init: t
  val from_string: string -> t
  val alloc: unit -> t
end

module Typ: sig
  type t =
    | BaseInt
    | BaseBool
    | Func of t * t
    | Code of Cls.t * t
    | PolyCls of Cls.t * Cls.t * t
  [@@deriving sexp]

  val equal: t -> t -> bool
  val compare: t -> t -> int
  val subst_cls: Cls.t -> Cls.t -> t -> t
end

module Var: sig
  type t
  [@@deriving compare, equal, sexp]

  val from_string: string -> t
  val alloc: unit -> t
end

module Const : sig

  type t =
    (* Arithmetic operators *)
    | Plus
    | Minus
    | Mult
    | LT
    (* Boolean operators *)
    | Neg
    | And
    | Or
  [@@deriving compare, equal, sexp]

  val typeOf: t -> Typ.t

end

module Term: sig
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

module Context: sig
  type elm =
    | Init of Cls.t
    | Var of Var.t * Typ.t * Cls.t
    | Lock of Cls.t * Cls.t
    | Unlock of int
    | Cls of Cls.t * Cls.t
  [@@deriving compare, equal, sexp]

  type t = elm list
  [@@deriving compare, equal, sexp]
  (* Note that elements are listed in reverse order compared to the
     notation in the paper. If you want to align the order, use from or List.rev
  *)

  val empty: t
  val from: elm list -> t
  val current: t -> Cls.t
  val depth: t -> int
  val domain_cls: t -> Cls.t list
  val domain_var: t -> Var.t list
  val lookup_var: t -> Var.t -> (Typ.t * Cls.t) option
end
