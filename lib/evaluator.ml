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

  let rec rename_cls(cls: Cls.t)(env: t): Cls.t =
    match env with
    | [] -> cls
    | Cls(from, dest) :: rest ->
      if Cls.equal cls from
      then
        rest |> rename_cls dest
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

let rec eval?(debug=false)(lv:int)(renv:Value.t RuntimeEnv.t)(cenv: CodeEnv.t)
    (store: Store.t)(k:(Value.t * Store.t) -> (Value.t * Store.t))(tm:Term.t): Value.t * Store.t =
  if debug
  then describe lv renv cenv store tm
  else ();
  (match (lv, tm) with
   | (0, Term.Int i) -> (Value.Int i, store) |> k
   | (0, Term.Bool b) -> (Value.Bool b, store) |> k
   | (0, Term.BinOp(op, a, b)) ->
     a |> eval 0 renv cenv store (fun (av, store) ->
         b |> eval 0 renv cenv store (fun (bv, store) ->
             (performBinOp op av bv, store) |> k))
   | (0, Term.UniOp(op, a)) ->
     a |> eval 0 renv cenv store (fun (av, store) ->
         (performUniOp op av, store) |> k)
   | (0, Term.ShortCircuitOp(op, a, b)) ->
     a |> eval 0 renv cenv store (fun (av, store) ->
         match (op, av) with
         | (ShortCircuitOp.And, Bool(ab)) ->
           if ab
           then b |> eval 0 renv cenv store k
           else (Bool(false), store) |> k
         | (ShortCircuitOp.Or, Bool(ab)) ->
           if ab
           then (Bool(true), store) |> k
           else b |> eval 0 renv cenv store k
         | _ -> failwith "typemismatch: shortcircuitop"
       )
   | (0, Term.Var v) -> (renv |> RuntimeEnv.lookup_var v, store) |> k
   | (0, Term.Lam _) -> (Value.Clos (renv, cenv, tm), store) |> k
   | (0, Term.App (func, arg)) ->
     func |> eval 0 renv cenv store (fun (funcv, store) ->
         arg |> eval 0 renv cenv store (fun (argv, store) ->
         match funcv with
         | Clos(renv', cenv', Lam(var, _, _, body)) ->
           body |> eval 0 ((var, argv) :: renv') cenv' store k
         | _ -> failwith "hoge 0 app"))
   | (0, Term.Quo (cls, body)) ->
     body |> eval 1 renv cenv store (fun (futv, store) ->
         match futv with
         | Fut t -> (Code (Quo(cenv |> CodeEnv.rename_cls cls, t)), store) |> k
         | _ -> failwith "fuga 0 quo"
       )
   | (0, Term.Unq (0, tm)) ->
     tm |> eval 0 renv cenv store (fun (v, store) ->
         match v with
         | Code(Quo(_, body)) ->
           body |> eval 0 renv cenv store k
         | _ -> failwith "fuga 0 unq"
       )
   | (0, Term.PolyCls (_, _, _)) -> (Value.Clos (renv, cenv, tm), store) |> k
   | (0, Term.AppCls (tm, cls1)) ->
     tm |> eval 0 renv cenv store (fun (v, store) -> match v with
         | Clos(renv', cenv', PolyCls(cls2, _, body)) ->
           body |> eval 0 renv' (CodeEnv.Cls(cls2, cenv |> CodeEnv.rename_cls cls1)::cenv') store k
         | _ -> failwith "hogege 0 appcls")
   | (0, Term.Fix f) ->
     f |> eval 0 renv cenv store (fun (fv, store) ->
         match fv with
         | Clos(renv', cenv', (Lam(self, _, _, Lam(v, cls, typ, body)) as fixed)) ->
           let eta = Value.Clos(renv', cenv', Lam(v, cls, typ, App(Fix fixed, Var(v)))) in
           (Clos(((self, eta) :: renv'), cenv', Lam(v, cls, typ, body)), store) |> k
         | Clos(renv', cenv', (Lam(self, _, _, PolyCls(cls, base, body)) as fixed)) ->
           let eta = Value.Clos(renv', cenv', PolyCls(cls, base, AppCls(Fix fixed, cls))) in
           (Clos(((self, eta) :: renv'), cenv', PolyCls(cls, base, body)), store) |> k
         | _ -> failwith "hogehoge 0 fix"
       )
   | (0, Term.If (cond, thenn, elsee)) ->
     cond |> eval 0 renv cenv store (fun (condv, store) ->
         (match condv with
          | Value.Bool(true) -> thenn
          | Value.Bool(false) -> elsee
          | _ -> failwith "hoge 0 if")
         |> eval 0 renv cenv store k
       )
   | (0, Term.Nil) -> (Value.Nil, store) |> k
   | (0, Term.Ref tm) ->
     tm |> eval 0 renv cenv store (fun (init, store) ->
         let loc = Loc.alloc () in
         let newstore = (loc, init) :: store in
         (Value.Loc loc, newstore) |> k
       )
   | (0, Term.Deref tm) ->
     tm |> eval 0 renv cenv store (fun (locv, store) ->
         (match locv with
          | Value.Loc loc -> (store |> Store.lookup loc, store) |> k
          | _ -> failwith "hogee 0 deref"))
   | (0, Term.Assign (loctm, newtm)) ->
     loctm |> eval 0 renv cenv store (fun (locv, store) ->
         newtm |> eval 0 renv cenv store (fun (newv, store) ->
             match locv with
             | Value.Loc loc ->
               let newstore = store |> Store.update loc newv in
               (Value.Nil, newstore) |> k
             | _ -> failwith "hogee 0 deref"))
   | (_, Term.Int _) -> (Value.Fut tm, store) |> k
   | (_, Term.Bool _) -> (Value.Fut tm, store) |> k
   | (l, Term.BinOp(op, a, b)) ->
     a |> eval l renv cenv store (fun (av, store) ->
         b|> eval l renv cenv store (fun (bv, store) ->
             match (av, bv) with
             | (Fut av1, Fut bv1) ->
               (Value.Fut (Term.BinOp(op, av1, bv1)), store) |> k
             | _ -> failwith "hogehoge 0 binop"))
   | (l, Term.UniOp(op, a)) ->
       a |> eval l renv cenv store (fun (av, store) ->
               match av with
               | Fut av1  ->
                 (Value.Fut (Term.UniOp(op, av1)), store) |> k
               | _ -> failwith "hogehoge 0 uniop")
     | (l, Term.ShortCircuitOp(op, a, b)) ->
       a |> eval l renv cenv store (fun (av, store) ->
           b|> eval l renv cenv store (fun (bv, store) ->
               match (av, bv) with
               | (Fut av1, Fut bv1) ->
                 (Value.Fut (Term.ShortCircuitOp(op, av1, bv1)), store) |> k
               | _ -> failwith "hogehoge 0 shortcircuitop"))
     | (_, Term.Var v) ->
       (Value.Fut (Term.Var(cenv |> CodeEnv.rename_var v)), store) |> k
     | (l, Term.Lam(v, typ, cls, body)) ->
       let v' = Var.alloc () in
       let cls' = Cls.alloc() in
       let typ' = cenv |> CodeEnv.rename_cls_in_typ typ in
       let cenv' = (CodeEnv.(Var(v, v') :: Cls(cls, cls') :: cenv)) in
       body |> eval l renv cenv' store (fun (v, store) ->
           match v with
           | Fut body' -> (Fut (Lam(v', typ', cls', body')), store) |> k
           | _ -> failwith "hoge l lam")
     | (l, Term.App(func, arg)) ->
       func |> eval l renv cenv store (fun (funcv, store) ->
           arg |> eval l renv cenv store (fun (argv, store) ->
               match (funcv, argv) with
               | (Fut(fbody), Fut(abody)) ->
                 (Fut(Term.App(fbody, abody)), store) |> k
               | _ -> failwith "hoge l app"
             ))
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
