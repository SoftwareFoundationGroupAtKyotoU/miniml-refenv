open Base

module Cls: sig
  type t
  [@@deriving compare, equal, sexp]

  val alloc: unit -> t
end

module Typ: sig
  type t =
    | BaseInt
    | BaseBool
    | Func of t * t
    | Code of Cls.t * t
    | PolyCls of Cls.t * Cls.t * t
  [@@deriving compare, equal, sexp]

  val subst_cls: Cls.t -> Cls.t -> t -> t
end

module Var: sig
  type t
  [@@deriving compare, equal, sexp]

  val alloc: unit -> t
end

module Const : sig

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

  val typeOf: t -> Typ.t

end

module Term: sig
  type t =
    | Const of Const.t
    | Var of Var.t
    | Lam of Var.t * Typ.t * Cls.t * t
    | App of t * t
    | Quo of Cls.t * Cls.t * t
    | Unq of int * t
    | PolyCls of Cls.t * Cls.t * t
    | AppCls of t * Cls.t
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
     notation in the paper. If you want to align the order, use List.rev
  *)

  val current: t -> Cls.t
  val depth: t -> int
  val domain_cls: t -> Cls.t list
  val domain_var: t -> Var.t list
  val lookup_var: t -> Var.t -> (Typ.t * Cls.t) option
end
