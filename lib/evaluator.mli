open Base
open Syntax
open Evalcommon

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
