open Base
open Syntax
open Evalcommon

module Continuation : sig
  type t =
    (* Continuation that takes run-time values *)
    | BinOpL0 of BinOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | BinOpR0 of BinOp.t * Value.t
    | UniOp0 of UniOp.t
    | ShortCircuitOpL0 of ShortCircuitOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppL0 of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppR0 of Value.t
    | RuntimeEval0 of Value.t RuntimeEnv.t * CodeEnv.t
    | Unq0 of int
    | ClsApp0 of Cls.t
    | IfCond0 of Term.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    (* Continuation that takes future-stage values *)
    | Lamf of Var.t * Cls.t * Typ.t
    | AppLf of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppRf of Value.t
    | Quof of Cls.t
    | Unqf of int
    | ClsAbsf of Cls.t * Cls.t
    | ClsAppf of Cls.t
  [@@deriving compare, equal, sexp]
end

module State : sig
  type t =
    | EvalTerm of int * Term.t * Value.t RuntimeEnv.t * CodeEnv.t * (Continuation.t list) * Store.t
    | ApplyCont of int * (Continuation.t list) * Value.t * Store.t
  [@@deriving compare, equal, sexp]

  val init: Term.t -> t
end

val run:
  ?debug:bool ->
  State.t ->
  Value.t * Store.t
