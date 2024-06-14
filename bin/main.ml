open Lib
open Lib.Syntax

let term = (Cui.read_term_from_channel Stdio.In_channel.stdin);;

let inferredtype = Typechecker.typeinfer Context.empty term;;

match inferredtype with
| None ->
  Stdio.print_endline "Failed to infer type";
  exit(1)
| Some ty ->
  Stdio.print_endline "Inferred type is:";
  ty |> Typ.sexp_of_t |> Stdio.print_s;

let v = Evaluator.eval_v term in

Stdio.print_endline "evaluated value is:";
v |> Evaluator.Value.sexp_of_t |> Stdio.print_s
