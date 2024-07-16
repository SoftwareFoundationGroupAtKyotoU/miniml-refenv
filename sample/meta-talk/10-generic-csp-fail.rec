(* Generic CSP is not allowed.
 * What if one writes funciton like this? *)
fun (x:int@g) -> `{@g x }

(* This is ill-staged and should be rejectd.
 * This code fails to type in fact. how?
 * Typechecker confirms that classifier of arguments
 * does not appear in the returnd value
 *
 *                         v THIS CONDITION MATTERS
 *  G, x:A@g |- M : B    g not in FC(B)
 * --------------------------------------
 *      G |- fun (x:A@g) -> M : A->B
 *
 * This simple side-condition seems working really well
 *)