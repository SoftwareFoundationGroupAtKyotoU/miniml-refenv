open Base
open Syntax

val well_formed_context: Context.t -> (unit, string) Result.t
val well_formed_type: Context.t -> Typ.t -> (unit, string) Result.t
val reachable_intuitionistic: Context.t -> Cls.t -> Cls.t -> bool
val typeinfer: Context.t -> Term.t -> (Typ.t, string) Result.t
val typecheck: Context.t -> Term.t -> Typ.t -> (unit, string) Result.t

