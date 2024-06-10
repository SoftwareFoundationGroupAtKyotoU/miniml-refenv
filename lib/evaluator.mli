open Base
open Syntax

module RuntimeEnv : sig
  type 'a t = (Var.t * 'a) list
  [@@deriving compare, equal, sexp]

  val lookup_var: Var.t -> 'a t -> 'a
end

module CodeEnv : sig
  type elm =
    | Var of Var.t * Var.t
    | Cls of Cls.t * Cls.t
  [@@deriving compare, equal, sexp]

  type t = elm list
  [@@deriving compare, equal, sexp]

  val rename_var: Var.t -> t -> Var.t
  val rename_cls: Cls.t -> t -> Cls.t
  val rename_cls_in_typ: Typ.t -> t -> Typ.t
end

module Loc : sig
  type t = int
  [@@deriving compare, equal, sexp]

  val alloc : unit -> t
end

module Value : sig
  type t =
    | Int of int
    | Bool of bool
    | Clos of t RuntimeEnv.t * CodeEnv.t * Term.t
    | Fix of t RuntimeEnv.t * CodeEnv.t * Term.t
    | Code of Term.t
    | Fut of Term.t
    | Loc of Loc.t
    | Nil
  [@@deriving compare, equal, sexp]
end

module Store : sig
  type t = (Loc.t * Value.t) list
  [@@deriving compare, equal, sexp]

  val lookup : Loc.t -> t -> Value.t

  val update : Loc.t -> Value.t -> t -> t
end

val eval:
  ?debug:bool ->
  int ->
  Value.t RuntimeEnv.t ->
  CodeEnv.t ->
  Store.t ->
  ((Value.t * Store.t) -> (Value.t * Store.t)) ->
  Term.t ->
  Value.t * Store.t

val eval_v: ?debug:bool -> Term.t -> Value.t
val eval_vs: ?debug:bool -> Term.t -> Value.t * Store.t
