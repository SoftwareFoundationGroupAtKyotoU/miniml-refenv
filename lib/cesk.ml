open Base
open Syntax

module RuntimeEnv = struct
  type 'a t = (Var.t * 'a) list
  [@@deriving compare, equal, sexp]

  let rec lookup_var(v:Var.t)(env:'a t): 'a =
    match env with
    | [] -> failwith "failed to lookup var"
    | (v1, value) :: rest ->
      if Var.equal v v1
      then value
      else rest |> lookup_var v
end

module CodeEnv = struct
  type elm =
    | Var of Var.t * Var.t
    | Cls of Cls.t * Cls.t
  [@@deriving compare, equal, sexp]

  type t = elm list
  [@@deriving compare, equal, sexp]

  let rec rename_var(v:Var.t)(env: t): Var.t =
    match env with
    | [] -> v
    | Var(from, dest) :: rest ->
        if Var.equal v from
        then dest
        else rest |> rename_var v
    | _ :: rest -> rest |> rename_var v

  let rec rename_cls(cls:Cls.t)(env: t): Cls.t =
    match env with
    | [] -> cls
    | Cls(from, dest) :: rest ->
        if Cls.equal cls from
        then dest
        else rest |> rename_cls cls
    | _ :: rest -> rest |> rename_cls cls

  let rec rename_cls_in_typ(typ: Typ.t)(env: t): Typ.t =
    match (typ : Typ.t) with
    | Typ.BaseInt
    | Typ.BaseBool -> typ
    | Typ.Func (func, arg) ->
      let func' = env |> rename_cls_in_typ func in
      let arg' = env |> rename_cls_in_typ arg in
      Typ.Func(func', arg')
    | Typ.Code (base, ty) ->
      let base' = env |> rename_cls base in
      let ty' = env |> rename_cls_in_typ ty in
      Typ.Code(base', ty')
    | Typ.PolyCls (cls, base, ty) ->
      let cls' = Cls.alloc () in
      let base' = env |> rename_cls base in
      let ty' = ty |> Typ.rename_cls cls cls' in
      let ty' = env |> rename_cls_in_typ ty' in
      Typ.PolyCls (cls', base', ty')
    | Typ.Unit -> Typ.Unit
    | Typ.Ref ty -> Typ.Ref(env |> rename_cls_in_typ ty)
end

module Loc = struct
  type t = int
  [@@deriving compare, equal, sexp]

  let counter = ref 0

  let alloc () =
    let ret = !counter in
    counter := ret + 1;
    ret
end

module Value = struct
  type t =
    | Int of int
    | Bool of bool
    | Clos of t RuntimeEnv.t * CodeEnv.t * Term.t
    | Fix of t RuntimeEnv.t * CodeEnv.t * Term.t
    | Code of Term.t
    | Fut of Term.t
    | Loc of Loc.t
    | Nil
  [@@deriving compare, equal, sexp]
end

module Store = struct
  type t = (Loc.t * Value.t) list
  [@@deriving compare, equal, sexp]

  let rec lookup loc store =
    match store with
    | [] -> failwith "failed to lookup store"
    | (loc1, v) :: rest ->
      if Loc.equal loc loc1
      then v
      else lookup loc rest

  let rec update loc newv store =
    match store with
    | [] -> failwith "failed to lookup store"
    | (loc1, v) :: rest ->
      if Loc.equal loc loc1
      then (loc1, newv) :: rest
      else (loc1, v) :: update loc newv rest
end

let performBinOp(op:BinOp.t)(a:Value.t)(b:Value.t): Value.t =
  (match op with
   | BinOp.Plus -> (match (a, b) with
       | (Int ai, Int bi) -> Int (ai + bi)
       | _ -> failwith "type mismatch: binop plus")
   | BinOp.Mult -> (match (a, b) with
       | (Int ai, Int bi) -> Int (ai * bi)
       | _ -> failwith "type mismatch: binop mult")
   | BinOp.Minus -> (match (a, b) with
       | (Int ai, Int bi) -> Int (ai - bi)
       | _ -> failwith "type mismatch: binop minus")
   | BinOp.Div -> (match (a, b) with
       | (Int ai, Int bi) -> Int (ai / bi)
       | _ -> failwith "type mismatch: binop div")
   | BinOp.Mod -> (match (a, b) with
       | (Int ai, Int bi) -> Int (Int.rem ai bi)
       | _ -> failwith "type mismatch: binop mod")
   | BinOp.LT -> (match (a, b) with
       | (Int ai, Int bi) -> Bool (ai < bi)
       | _ -> failwith "type mismatch: binop lt")
   | BinOp.Equal -> (match (a, b) with
       | (Int ai, Int bi) -> Bool (Int.equal ai bi)
       | _ -> failwith "type mismatch: binop eq"))

let performUniOp(op:UniOp.t)(a:Value.t): Value.t =
  match (op, a) with
  | (UniOp.Not, Bool(b)) -> Bool(not b)
  | _ -> failwith "type mismatch: uniop not"

let describe
    (lv:int)(renv:Value.t RuntimeEnv.t)(cenv: CodeEnv.t)
    (store: Store.t)(tm:Term.t): unit =
  Printf.sprintf "lv is %d\n" lv |> Stdio.prerr_endline;
  Stdio.prerr_endline "evaluating term:";
  Stdio.eprint_s (Term.sexp_of_t tm);
  Stdio.prerr_endline "renv is:";
  Stdio.eprint_s (RuntimeEnv.sexp_of_t Value.sexp_of_t renv);
  Stdio.prerr_endline "cenv is:";
  Stdio.eprint_s (CodeEnv.sexp_of_t cenv);
  Stdio.prerr_endline "store is:";
  Stdio.eprint_s (Store.sexp_of_t store)

module Cont = struct
  type t =
    | Exit
    | BinLeft of BinOp.t * Term.t * (Value.t RuntimeEnv.t) * CodeEnv.t * t
    | BinRight of BinOp.t * Value.t * t
    | UniOp of UniOp.t * t
    | ShortCircuitLeft of ShortCircuitOp.t * Term.t * (Value.t RuntimeEnv.t) * CodeEnv.t * t
    | AppL of Term.t * (Value.t RuntimeEnv.t) * CodeEnv.t * t
    | AppR of Value.t * t
    | Quo of Cls.t * CodeEnv.t * t
    | Unq of (Value.t RuntimeEnv.t) * CodeEnv.t * t
    | AppCls of Cls.t * t
    | Fix of t
    | If of Term.t * Term.t * (Value.t RuntimeEnv.t) * CodeEnv.t * t
    | Ref of t
    | Deref of t
    | AssignL of Term.t * (Value.t RuntimeEnv.t) * CodeEnv.t * t
    | AssignR of Value.t * t
    | BinLeftFut of int * BinOp.t * Term.t * (Value.t RuntimeEnv.t) * CodeEnv.t * t
    | BinRightFut of BinOp.t * Value.t * t
    | UniOpFut of UniOp.t * t
    | ShortCircuitLeftFut of int * ShortCircuitOp.t * Term.t * (Value.t RuntimeEnv.t) * CodeEnv.t * t
    | ShortCircuitRightFut of ShortCircuitOp.t * Value.t * t
    | LamFut of Var.t * Cls.t * Typ.t * t
    | AppLeftFut of int * Term.t * (Value.t RuntimeEnv.t) * CodeEnv.t * t
    | AppRightFut of Value.t * t

  [@@deriving compare, equal, sexp]
end

let rec apply_cont (k:Cont.t)((v, store): Value.t * Store.t): Value.t * Store.t =
  match k with
  | Exit -> (v, store)
  | BinLeft (op, r, renv, cenv, k1) -> r |> eval 0 renv cenv store (BinRight(op, v, k1))
  | BinRight (op, l, k) -> (performBinOp op l v, store) |> apply_cont k
  | UniOp (op, k1) -> (performUniOp op v, store) |> apply_cont k1
  | ShortCircuitLeft(op, b, renv, cenv, k1) ->
    (match (op, v) with
     | (ShortCircuitOp.And, Bool(ab)) ->
       if ab
       then b |> eval 0 renv cenv store k1
       else (Bool(false), store) |> apply_cont k1
     | (ShortCircuitOp.Or, Bool(ab)) ->
       if ab
       then (Bool(true), store) |> apply_cont k1
       else b |> eval 0 renv cenv store k1
     | _ -> failwith "typemismatch: shortcircuitop"
    )
  | AppL (arg, renv, cenv, k1) -> arg |> eval 0 renv cenv store (AppR(v, k1))
  | AppR (funcv, k1) ->
    (match funcv with
     | Clos(renv', cenv', Lam(var, _, _, body)) ->
       body |> eval 0 ((var, v) :: renv') cenv' store k1
     | Fix(renv', cenv', Lam(self, _, _, Lam(var, _, _, body))) ->
       body |> eval 0 ((var, v) :: (self, funcv) :: renv') cenv' store k1
     | _ -> failwith "hoge 0 app")
  | Quo (cls, cenv, k1) -> (match v with
      | Fut t -> (Code (Quo(cenv |> CodeEnv.rename_cls cls, t)), store) |> apply_cont k1
      | _ -> failwith "fuga 0 quo")
  | Unq (renv, cenv, k1) -> (match v with
      | Code(Quo(_, body)) -> body |> eval 0 renv cenv store k1
      | _ -> failwith "fuga 0 unq")
  | AppCls (cls1, k1) -> (match v with
      | Clos(renv', cenv', PolyCls(cls2, _, body)) ->
        body |> eval 0 renv' (CodeEnv.Cls(cls2, cls1)::cenv') store k1
      | Fix(renv', cenv', Lam(self, _, _, PolyCls(cls2, _, body))) ->
        body |> eval 0 ((self, v) :: renv') (CodeEnv.Cls(cls2, cls1)::cenv') store k1
      | _ -> failwith "hogege 0 appcls")
  | Fix (k1) -> (match v with
      | Clos(renv', cenv', lam) -> (Value.Fix (renv', cenv', lam), store) |> apply_cont k1
      | _ -> failwith "hogehoge 0 fix")
  | If (thenn, elsee, renv, cenv, k1) ->
      (match v with
       | Value.Bool(true) -> thenn
       | Value.Bool(false) -> elsee
       | _ -> failwith "hoge 0 if")
      |> eval 0 renv cenv store k1
  | Ref (k1) ->
    let loc = Loc.alloc () in
    let newstore = (loc, v) :: store in
    (Value.Loc loc, newstore) |> apply_cont k1
  | Deref (k1) -> (match v with
      | Value.Loc loc -> (store |> Store.lookup loc, store) |> apply_cont k1
      | _ -> failwith "hogee 0 deref")
  | AssignL (newtm, renv, cenv, k1) ->
    newtm |> eval 0 renv cenv store (Cont.AssignR(v, k1))
  | AssignR (locv, k1) ->
    (match locv with
     | Value.Loc loc ->
       let newstore = store |> Store.update loc v in
       (Value.Nil, newstore) |> apply_cont k1
     | _ -> failwith "hogee 0 deref")
  | BinLeftFut (l, op, b, renv, cenv, k1) ->
    b|> eval l renv cenv store (Cont.BinRightFut(op, v, k1))
  | BinRightFut (op, a, k1) -> (match (a, v) with
    | (Fut av1, Fut bv1) ->
      (Value.Fut (Term.BinOp(op, av1, bv1)), store) |> apply_cont k1
    | _ -> failwith "hogehoge 0 binop")
  | UniOpFut (op, k1) -> (match v with
      | Fut av1  ->
        (Value.Fut (Term.UniOp(op, av1)), store) |> apply_cont k1
      | _ -> failwith "hogehoge 0 uniop")
  | ShortCircuitLeftFut (l, op, b, renv, cenv, k1) -> (
      b |> eval l renv cenv store (Cont.ShortCircuitRightFut(op, v, k1)))
  | ShortCircuitRightFut (op, a, k1) -> (match (a, v) with
      | (Fut av1, Fut bv1) ->
        (Value.Fut (Term.ShortCircuitOp(op, av1, bv1)), store) |> apply_cont k1
      | _ -> failwith "hogehoge 0 shortcircuitop")
  | LamFut (v', cls', typ', k1) -> (match v with
      | Fut body' -> (Fut (Lam(v', typ', cls', body')), store) |> apply_cont k1
      | _ -> failwith "hoge l lam")
  | AppLeftFut (l, arg, renv, cenv, k1) ->
    arg |> eval l renv cenv store (Cont.AppRightFut(v, k1))
  | AppRightFut (funcv, k1) -> (match (funcv, v) with
      | (Fut(fbody), Fut(abody)) ->
        (Fut(Term.App(fbody, abody)), store) |> apply_cont k1
      | _ -> failwith "hoge l app")


and eval?(debug=false)(lv:int)(renv:Value.t RuntimeEnv.t)(cenv: CodeEnv.t)
    (store: Store.t)(k:Cont.t)(tm:Term.t): Value.t * Store.t =
  if debug
  then describe lv renv cenv store tm
  else ();
  (match (lv, tm) with
   | (0, Term.Int i) -> (Value.Int i, store) |> apply_cont k
   | (0, Term.Bool b) -> (Value.Bool b, store) |> apply_cont k
   | (0, Term.BinOp(op, a, b)) ->
     a |> eval 0 renv cenv store (Cont.BinLeft(op, b, renv, cenv, k))
   | (0, Term.UniOp(op, a)) ->
     a |> eval 0 renv cenv store (Cont.UniOp(op, k))
   | (0, Term.ShortCircuitOp(op, a, b)) ->
     a |> eval 0 renv cenv store (Cont.ShortCircuitLeft(op, b, renv, cenv, k))
   | (0, Term.Var v) -> (renv |> RuntimeEnv.lookup_var v, store) |> apply_cont k
   | (0, Term.Lam _) -> (Value.Clos (renv, cenv, tm), store) |> apply_cont k
   | (0, Term.App (func, arg)) ->
     func |> eval 0 renv cenv store (Cont.AppL(arg, renv, cenv, k))
   | (0, Term.Quo (cls, body)) ->
     body |> eval 1 renv cenv store (Cont.Quo(cls, cenv, k))
   | (0, Term.Unq (0, tm)) ->
     tm |> eval 0 renv cenv store (Cont.Unq(renv, cenv, k))
   | (0, Term.PolyCls (_, _, _)) ->
     (Value.Clos (renv, cenv, tm), store) |> apply_cont k
   | (0, Term.AppCls (tm, cls1)) ->
     tm |> eval 0 renv cenv store (Cont.AppCls(cls1, k))
   | (0, Term.Fix f) ->
     f |> eval 0 renv cenv store (Cont.Fix(k))
   | (0, Term.If (cond, thenn, elsee)) ->
     cond |> eval 0 renv cenv store (Cont.If(thenn, elsee, renv, cenv, k))
   | (0, Term.Nil) -> (Value.Nil, store) |> apply_cont k
   | (0, Term.Ref tm) ->
     tm |> eval 0 renv cenv store (Cont.Ref(k))
   | (0, Term.Deref tm) ->
     tm |> eval 0 renv cenv store (Cont.Deref(k))
   | (0, Term.Assign (loctm, newtm)) ->
     loctm |> eval 0 renv cenv store (Cont.AssignL(newtm, renv, cenv, k))
   | (_, Term.Int _) -> (Value.Fut tm, store) |> apply_cont k
   | (_, Term.Bool _) -> (Value.Fut tm, store) |> apply_cont k
   | (l, Term.BinOp(op, a, b)) ->
     a |> eval l renv cenv store (Cont.BinLeftFut(l, op, b, renv, cenv, k))
   | (l, Term.UniOp(op, a)) ->
       a |> eval l renv cenv store (Cont.UniOpFut(op, k))
   | (l, Term.ShortCircuitOp(op, a, b)) ->
     a |> eval l renv cenv store (Cont.ShortCircuitLeftFut(l, op, b, renv, cenv, k))
   | (_, Term.Var v) ->
     (Value.Fut (Term.Var(cenv |> CodeEnv.rename_var v)), store) |> apply_cont k
   | (l, Term.Lam(v, typ, cls, body)) ->
       let v' = Var.alloc () in
       let cls' = Cls.alloc() in
       let typ' = cenv |> CodeEnv.rename_cls_in_typ typ in
       let cenv' = (CodeEnv.(Var(v, v') :: Cls(cls, cls') :: cenv)) in
       body |> eval l renv cenv' store (Cont.LamFut (v', cls', typ', k))
   | (l, Term.App(func, arg)) ->
       func |> eval l renv cenv store (Cont.AppLeftFut(l, arg, renv, cenv, k))
   | (l, Term.Quo(base, body)) ->
       body |> eval (l+1) renv cenv store (fun (v, store) ->
           let base' = cenv |> CodeEnv.rename_cls base in
           match v with
           | Fut(v) -> (Fut(Quo(base', v)), store) |> k
           | _ -> failwith "hoge l quo")
     | (l, Term.Unq(diff, tm)) ->
       if Int.equal l diff then
         tm |> eval 0 renv cenv store (fun (v, store) ->
             (match v with
              | Code(Quo(_, body)) -> (Fut(body), store) |> k
              | _ -> failwith "hoge l=diff unq"))
       else
         tm |> eval (l - diff) renv cenv store (fun (v, store) ->
             (match v with
              | Fut(body) -> (Fut(Term.Unq(diff, body)), store) |> k
              | _ -> failwith "hoge l>diff unq"))
     | (l, Term.PolyCls(cls, base, body)) ->
       let cls' = Cls.alloc() in
       let base' = cenv |> CodeEnv.rename_cls base in
       let cenv' = (CodeEnv.(Cls(cls, cls') :: cenv)) in
       body |> eval l renv cenv' store (fun (v, store) ->
           match v with
           | Fut(bodyv) -> (Fut(Term.PolyCls(cls', base', bodyv)), store) |> k
           | _ -> failwith "hoge l polycls")
     | (l, Term.AppCls(tm, cls)) ->
       let cls' = cenv |> CodeEnv.rename_cls cls in
       tm |> eval l renv cenv store (fun (v, store) ->
           match v with
           | Fut body -> (Fut(AppCls(body, cls')), store) |> k
           | _ -> failwith "hoge l appcls")
     | (l, Term.Fix(f)) ->
       f |> eval l renv cenv store (fun (v, store) -> match v with
           | Fut body -> (Fut(Fix body), store) |> k
           | _ -> failwith "hoge l fix")
     | (l, Term.If(cond, thenn, elsee)) ->
       cond  |> eval l renv cenv store (fun (condv, store) ->
           thenn |> eval l renv cenv store (fun (thenv, store) ->
               elsee |> eval l renv cenv store (fun (elsev, store) ->
                   match (condv, thenv, elsev) with
                   | (Fut(cbody), Fut(tbody), Fut(ebody)) ->
                     (Fut(Term.If(cbody, tbody, ebody)), store) |> k
                   | _ -> failwith "hoge l if"
                 )))
     | (_, Term.Nil) -> (Fut Term.Nil, store) |> k
     | (l, Term.Ref init) ->
       init |> eval l renv cenv store (fun (v, store) -> match v with
           | Fut body -> (Fut(Term.Ref body), store) |> k
           | _ -> failwith "hoge l ref")
     | (l, Term.Deref loc) ->
       loc |> eval l renv cenv store (fun (v, store) -> match v with
           | Fut body -> (Fut(Term.Deref body), store) |> k
           | _ -> failwith "hoge l deref")
     | (l, Term.Assign(loc, newv)) ->
       loc |> eval l renv cenv store (fun (locv, store) ->
           newv |> eval l renv cenv store (fun (newvv, store) ->
               match (locv, newvv) with
               | (Fut locb, Fut newb) -> (Fut(Term.Assign(locb, newb)), store) |> k
               | _ -> failwith "hoge l assign"))
  )

let eval_v ?(debug=false) tm =
  let (v, _) = tm |> eval ~debug:debug 0 [] [] [] (fun x -> x) in
  v

let eval_vs ?(debug=false) tm =
  tm |> eval ~debug:debug 0 [] [] [] (fun x -> x)

let%test_unit "hoge" =
  [%test_result: Value.t]
    ("1"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Int 1);
  [%test_result: Value.t]
    ("true"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Bool true);
  [%test_result: Value.t]
    ("1 + 2"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Int 3);
  [%test_result: Value.t]
    ("not (1 < 2)"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Bool false);
  [%test_result: Value.t]
    ("(1 < 2) && (2 < 3)"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Bool true);
  [%test_result: Value.t]
    ("if true then 1 else 0"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Int 1);
  [%test_result: Value.t]
    ("let x:int = 1 in x"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Int 1);
  [%test_result: Value.t]
    ("let x:int = 1 in x"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Int 1)

let%test_unit "recursion" =
  [%test_result: Value.t]
    ({|
       let rec f(x:int):int =
         if x < 1
         then 0
         else x + f(x - 1) in
       f 10
      |}
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Int 55)

let%test_unit "code generation" =
  [%test_result: Value.t]
    ("`{@! 1 }"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Code(Term.(Quo(Cls.init, Int 1))));
  [%test_result: Value.t]
    ("`{@! 1 + 1 }"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Code(Term.(Quo(Cls.init, BinOp(BinOp.Plus, Int 1, Int 1)))));
  [%test_result: Value.t]
    ("`{@! fun (x:int@g) -> ~{ `{@g x } }  }"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Code ("`{@! fun (x:int@g) -> x}" |> Cui.read_term));
  [%test_result: Value.t]
    ({|
        `{@!
          let x:int@g1 = 1 in
          ~{
            let f (y:int):<int@g1> = `{@g1 x} in
            `{@g1
              let x:int = 2 in
              ~{ f 0 } + x
            }
          }
        }

     |}
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Code (
        {|
           `{@!
             let x1:int = 1 in
             let x2:int = 2 in
             x1 + x2
           }
         |} |> Cui.read_term
      ))

let%test_unit "unquote with different levels" =
  [%test_result: Value.t]
    ("~0{`{@! 2 }}"
     |> Cui.read_term
     |> eval_v)
    ~expect:(Int 2);
  [%test_result: Value.t]
    ({|
        let x:<int@!> = `{@! 1 } in
        `{@! `{@! ~2{ x } } }
     |}
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Code (
        "`{@! `{@! 1 } }" |> Cui.read_term
      ))

let%test_unit "polymorphic context" =
  [%test_result: Value.t]
    ({|
        let f[g1:>!](x:<int@g1>) : <int@g1>
          = `{@g1 1 + ~x } in
        `{@! fun (y:int@g2) -> ~{ f@@g2 `{@g2 y } }}
     |}
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Code (
        "`{@! fun (y:int@g2) -> 1 + y }" |> Cui.read_term
      ))

let%test_unit "ref" =
  [%test_result: Value.t]
    ({|
        let r: ref int = ref 1 in
        let () = r := 2 in
        !r
     |}
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Int 2);
  [%test_result: Value.t]
    ({|
        let r: ref int = ref 0 in
        let rec loop (n:int): unit =
          if n < 1 then
            ()
          else
            let c: int = !r in
            let () = r := (c + n) in
            loop (n - 1) in
        let () = loop 10 in
        !r
     |}
     |> Cui.read_term
     |> eval_v)
    ~expect:(Value.Int 55)
