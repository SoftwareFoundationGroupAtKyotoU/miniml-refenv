open Lib
open Lib.Syntax

let one_iter(tm:Term.t) =
  let inferredtype = Typechecker.typeinfer true Context.empty tm in
  match inferredtype with
  | Result.Error(msg) ->
    Stdio.printf "Type error:%s\n" msg;
    exit(1)
  | Result.Ok ty ->
    Stdio.print_endline "Inferred type is:";
    ty |> Typ.display |> Stdio.print_endline;

    let v = Cekmachine.eval ~debug:true tm in
    Stdio.print_endline "evaluated value is:";
    v |> Evalcommon.Value.display |> Stdio.print_endline;
    v

let term = (Cui.read_term_from_channel Stdio.In_channel.stdin);;

let rec loop(tm:Term.t) =
  (match one_iter tm with
   | Evalcommon.Value.Code(Term.Quo(cls, body)) when Cls.equal Cls.init cls ->
     Stdio.print_endline "vvvvv Going to next stage vvvvv";
     Stdio.print_endline "";
     loop body
   | _ -> Stdio.print_endline "Fin"
  ) in
loop term
