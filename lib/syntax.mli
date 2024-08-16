open Core

module Cls: sig
  type t
  [@@deriving compare, equal, sexp, hash]

  val init: t
  val from_string: string -> t
  val gen: unit -> t
  val color: t -> t
  val rename_cls: t -> t -> t -> t

  include Comparator.S with type t := t
  type set = (t, comparator_witness) Set.t

end

module Typ: sig
  type t =
    | BaseInt
    | BaseBool
    | Func of t * t
    | Code of Cls.t * t
    | PolyCls of Cls.t * Cls.t * t
    | Unit
    | Ref of t
  [@@deriving sexp, hash]

  include Hashable with type t := t

  val equal: t -> t -> bool
  val compare: t -> t -> int
  val rename_cls: Cls.t -> Cls.t -> t -> t
  val free_cls: t -> Cls.set
end

module Var: sig
  type t
  [@@deriving compare, equal, sexp, hash]

  val from_string: string -> t
  val gen: unit -> t
  val color: t -> t
end

module BinOp : sig
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

module UniOp : sig
  type t =
    | Not
  [@@deriving compare, equal, sexp]
end

module ShortCircuitOp : sig
  type t =
    | And
    | Or
  [@@deriving compare, equal, sexp]
end

module Term: sig
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
  [@@deriving sexp]

  val equal: t -> t -> bool
  val compare: t -> t -> int
  val rename_var: Var.t -> Var.t -> t -> t
  val rename_cls: Cls.t -> Cls.t -> t -> t
end

module Context: sig
  type elm =
    | Init of Cls.t
    | Var of Var.t * Typ.t * Cls.t
    | Lock of Cls.t
    | Unlock of int
    | Cls of Cls.t * Cls.t
  [@@deriving compare, equal, sexp, hash]

  type t = elm list
  [@@deriving compare, equal, sexp, hash]

  include Hashable with type t := t

  val empty: t
  val from: elm list -> t
  val current: t -> Cls.t
  val depth: t -> int
  val domain_cls: t -> Cls.t list
  val domain_var: t -> Var.t list
  val lookup_var: t -> Var.t -> (Typ.t * Cls.t) option
end
