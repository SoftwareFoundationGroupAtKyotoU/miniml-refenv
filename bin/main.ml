open Lib
open Lib.Syntax

let one_iter(tm:Term.t) =
  let inferredtype = Typechecker.typeinfer Context.empty tm in
  match inferredtype with
  | None ->
    Stdio.print_endline "Failed to infer type";
    exit(1)
  | Some ty ->
    Stdio.print_endline "Inferred type is:";
    ty |> Typ.sexp_of_t |> Stdio.print_s;

    let v = Evaluator.eval_v tm in
    Stdio.print_endline "evaluated value is:";
    v |> Evaluator.Value.sexp_of_t |> Stdio.print_s;
    v

let term = (Cui.read_term_from_channel Stdio.In_channel.stdin);;

let rec loop(tm:Term.t) =
  (match one_iter tm with
   | Evaluator.Value.Code(Term.Quo(cls, body)) when Cls.equal Cls.init cls ->
     Stdio.print_endline "Going to next stage";
     loop body
   | _ -> Stdio.print_endline "Fin"
  ) in
loop term
