open Base
open Syntax
open Evalcommon

module Cont : sig
  type t_0 =
    (* Continutation that takes run-time values *)
    | BinOpL0 of BinOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | BinOpR0 of BinOp.t * Value.t
    | UniOp0 of UniOp.t
    | ShortCircuitOpL0 of ShortCircuitOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppL0 of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppR0 of Value.t
    | RuntimeEval0 of Value.t RuntimeEnv.t * CodeEnv.t
    | Unq0 of int
    | AppCls0 of Cls.t
    | IfCond0 of Term.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | Fix0
    | LetcsVal0 of Var.t * Typ.t * Cls.t * Term.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | LetcsBody0 of Var.t * Typ.t * Cls.t * Term.t * Cls.t
    | Lift0 of Cls.t
    | Ref0
    | Deref0
    | AssignDest0 of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AssignNewVal0 of Value.t
  [@@deriving compare, equal, sexp]

  type t_f =
    (* Continuation that takes future-stage values *)
    | BinOpLf of BinOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | BinOpRf of BinOp.t * Term.t
    | UniOpf of UniOp.t
    | ShortCircuitOpLf of ShortCircuitOp.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | ShortCircuitOpRf of ShortCircuitOp.t * Term.t
    | Lamf of Var.t * Typ.t * Cls.t
    | AppLf of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AppRf of Term.t
    | Quof of Cls.t
    | Unqf of int
    | PolyClsf of Cls.t * Cls.t
    | AppClsf of Cls.t
    | Fixf
    | IfCondf of Term.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | IfThenf of Term.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | IfElsef of Term.t * Term.t
    | LetcsValf of Var.t * Typ.t * Cls.t * Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | LetcsBodyf of Var.t * Typ.t * Cls.t * Term.t
    | Liftf of Cls.t
    | Reff
    | Dereff
    | AssignDestf of Term.t * Value.t RuntimeEnv.t * CodeEnv.t
    | AssignNewValf of Term.t
  [@@deriving compare, equal, sexp]

  type t =
    | Runtime of t_0
    | Future of t_f
  [@@deriving compare, equal, sexp]
end

module Config : sig
  type t =
    | EvalTerm of int * Term.t * Value.t RuntimeEnv.t * CodeEnv.t * (Cont.t list) * Store.t
    | ApplyCont0 of (Cont.t list) * Value.t * Store.t
    | ApplyContf of int * (Cont.t list) * Term.t * Store.t
  [@@deriving compare, equal, sexp]

  val init: Term.t -> t
end

val run:
  ?debug:bool ->
  Config.t ->
  Value.t * Store.t

val eval_v: ?debug:bool -> Term.t -> Value.t
