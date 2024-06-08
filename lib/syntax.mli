open Base

module Cls: sig
  type t
  [@@deriving compare, equal, sexp]

  val init: t
  val from_string: string -> t
  val alloc: unit -> t
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
  [@@deriving sexp]

  val equal: t -> t -> bool
  val compare: t -> t -> int
  val rename_cls: Cls.t -> Cls.t -> t -> t
  val free_cls: t -> Cls.set
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
    | Equal
    | Div
    | Mod
    (* Boolean operators *)
    | Not
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
    | Quo of Cls.t * t
    | Unq of int * t
    | PolyCls of Cls.t * Cls.t * t
    | AppCls of t * Cls.t
    | Fix of t
    | If of t * t * t
  [@@deriving compare, equal, sexp]

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
  [@@deriving compare, equal, sexp]

  type t = elm list
  [@@deriving compare, equal, sexp]

  val empty: t
  val from: elm list -> t
  val current: t -> Cls.t
  val depth: t -> int
  val domain_cls: t -> Cls.t list
  val domain_var: t -> Var.t list
  val lookup_var: t -> Var.t -> (Typ.t * Cls.t) option
end
