open Base
open Syntax

module RuntimeEnv : sig
  type 'a t = (Var.t * Cls.t * 'a) list
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

module Continuation : sig
  type t =
    (* Continuation that takes run-time values *)
    | BinOpL0 of BinOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | BinOpR0 of BinOp.t * Value.t
    | UniOp0 of UniOp.t
    | ShortCircuitOpL0 of ShortCircuitOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | ShortCircuitOpR0 of ShortCircuitOp.t * Value.t
    | AppL0 of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppR0 of Value.t
    | RuntimeEval0 of Value.t RuntimeEnv.t * CodeEnv.t
    | Unq0 of int
    | ClsApp0 of Cls.t
    (* Continuation that takes future-stage values *)
    | Lamf of Var.t * Cls.t * Typ.t
    | AppLf of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppRf of Value.t
    | Quof of Cls.t
    | Unqf of int
    | ClsAbsf of Cls.t * Cls.t
    | ClsAppf of Cls.t
end

module State : sig
  type t =
    | EvalTerm of int * Term.t * Value.t RuntimeEnv.t * CodeEnv.t * (Continuation.t list) * Store.t
    | ApplyCont of int * (Continuation.t list) * Value.t * Store.t

  val init: Term.t -> t
end

val run:
  ?debug:bool ->
  State.t ->
  Value.t * Store.t
