(*
  !        : initial classifier (for empty environment)
  <int@!>  : code type that evaluates to integer, annotated with !
  `{@! 1 } : a quote where content is valid under !
*)
let x : <int@!> = `{@! 1 } in
let y : <int@!> = `{@! 2 } in

(* one can generate bigger code fragment using unquote ~
   type checker can check scope-safety via classifiers
 *)
`{@! ~x + ~y }
(* evaluates to `{@! 1 + 2 } *)
