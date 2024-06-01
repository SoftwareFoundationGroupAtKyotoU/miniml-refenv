open Base
open Syntax

val well_formed_context: Context.t -> bool
val well_formed_type: Context.t -> Typ.t -> bool
val reachable_intuitionistic: Context.t -> Cls.t -> Cls.t -> bool
val typeinfer: Context.t -> Term.t -> Typ.t option
val typecheck: Context.t -> Term.t -> Typ.t -> bool

