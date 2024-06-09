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
    | [] -> failwith "failed to look up"
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
end

module Value = struct
  type t =
    | Int of int
    | Bool of bool
    | Clos of t RuntimeEnv.t * CodeEnv.t * Term.t
    | Code of Term.t
    | Fut of Term.t
  [@@deriving compare, equal, sexp]
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

let rec eval(lv:int)(renv:Value.t RuntimeEnv.t)(cenv: CodeEnv.t)(k:Value.t -> Value.t)(tm:Term.t): Value.t =
  (match (lv, tm) with
   | (0, Term.Int i) -> Value.Int i |> k
   | (0, Term.Bool b) -> Value.Bool b |> k
   | (0, Term.BinOp(op, a, b)) ->
     a |> eval 0 renv cenv (fun av ->
         b |> eval 0 renv cenv (fun bv ->
             performBinOp op av bv |> k))
   | (0, Term.UniOp(op, a)) ->
     a |> eval 0 renv cenv (fun av ->
         performUniOp op av |> k)
   | (0, Term.ShortCircuitOp(op, a, b)) ->
     a |> eval 0 renv cenv (fun av ->
         match (op, av) with
         | (ShortCircuitOp.And, Bool(ab)) ->
           if ab
           then b |> eval 0 renv cenv k
           else Bool(false) |> k
         | (ShortCircuitOp.Or, Bool(ab)) ->
           if ab
           then Bool(true) |> k
           else b |> eval 0 renv cenv k
         | _ -> failwith "typemismatch: shortcircuitop"
       )
   | (0, Term.Var v) -> renv |> RuntimeEnv.lookup_var v |> k
   | (0, Term.Lam _) -> Value.Clos (renv, cenv, tm) |> k
   | (0, Term.App (func, arg)) ->
     func |> eval 0 renv cenv (fun funcv -> arg |> eval 0 renv cenv (fun argv ->
         match funcv with
         | Clos(renv', cenv', Lam(var, _, _, body)) ->
           body |> eval 0 ((var, argv) :: renv') cenv' k
         | _ -> failwith "hoge 0 app"))
   | (0, Term.Quo (cls, body)) ->
     body |> eval 1 renv cenv (fun futv ->
         match futv with
         | Fut t -> Code (Quo(cenv |> CodeEnv.rename_cls cls, t)) |> k
         | _ -> failwith "fuga 0 quo"
       )
   | (0, Term.Unq (0, tm)) ->
     tm |> eval 0 renv cenv (fun v ->
         match v with
         | Code(Quo(_, body)) ->
           body |> eval 0 renv cenv k
         | _ -> failwith "fuga 0 unq"
       )
     | (0, Term.PolyCls (_, _, _)) -> Value.Clos (renv, cenv, tm) |> k
     | (0, Term.AppCls (tm, cls1)) ->
       tm |> eval 0 renv cenv (fun v -> match v with
           | Clos(renv', cenv', PolyCls(cls2, _, body)) ->
             body |> eval 0 renv' (CodeEnv.Cls(cls2, cls1)::cenv') k
           | _ -> failwith "hogege 0 appcls")
     | (0, Term.Fix f) ->
       Term.(App(f,(Fix f))) |> eval 0 renv cenv k
     | (0, Term.If (cond, thenn, elsee)) ->
       cond |> eval 0 renv cenv (fun condv ->
           (match condv with
           | Value.Bool(true) -> thenn
           | Value.Bool(false) -> elsee
           | _ -> failwith "hoge 0 if")
           |> eval 0 renv cenv k
         )
     | (_, Term.Int _) -> Value.Fut tm |> k
     | (_, Term.Bool _) -> Value.Fut tm |> k
     | (l, Term.BinOp(op, a, b)) ->
       a |> eval l renv cenv (fun av ->
           b|> eval l renv cenv (fun bv ->
               match (av, bv) with
               | (Fut av1, Fut bv1) ->
                 Value.Fut (Term.BinOp(op, av1, bv1)) |> k
               | _ -> failwith "hogehoge 0 binop"))
     | (l, Term.UniOp(op, a)) ->
       a |> eval l renv cenv (fun av ->
               match av with
               | Fut av1  ->
                 Value.Fut (Term.UniOp(op, av1)) |> k
               | _ -> failwith "hogehoge 0 uniop")
     | (l, Term.ShortCircuitOp(op, a, b)) ->
       a |> eval l renv cenv (fun av ->
           b|> eval l renv cenv (fun bv ->
               match (av, bv) with
               | (Fut av1, Fut bv1) ->
                 Value.Fut (Term.ShortCircuitOp(op, av1, bv1)) |> k
               | _ -> failwith "hogehoge 0 shortcircuitop"))
     | (_, Term.Var v) ->
       Value.Fut (Term.Var(cenv |> CodeEnv.rename_var v)) |> k
     | (l, Term.Lam(v, typ, cls, body)) ->
       let v' = Var.alloc () in
       let cls' = Cls.alloc() in
       let typ' = cenv |> CodeEnv.rename_cls_in_typ typ in
       let cenv' = (CodeEnv.(Var(v, v') :: Cls(cls, cls') :: cenv)) in
       body |> eval l renv cenv' (fun v ->
           match v with
           | Fut body' -> Fut (Lam(v', typ', cls', body')) |> k
           | _ -> failwith "hoge l lam")
     | (l, Term.App(func, arg)) ->
       func |> eval l renv cenv (fun funcv ->
           arg |> eval l renv cenv (fun argv ->
               match (funcv, argv) with
               | (Fut(fbody), Fut(abody)) -> Fut(Term.App(fbody, abody)) |> k
               | _ -> failwith "hoge l app"
             ))
     | (l, Term.Quo(base, body)) ->
       body |> eval (l+1) renv cenv (fun v ->
           let base' = cenv |> CodeEnv.rename_cls base in
           match v with
           | Fut(v) -> Fut(Quo(base', v)) |> k
           | _ -> failwith "hoge l quo")
     | (l, Term.Unq(diff, tm)) ->
       if Int.equal l diff then
         tm |> eval 0 renv cenv (fun v ->
             (match v with
              | Code(Quo(_, body)) -> Fut(body) |> k
              | _ -> failwith "hoge l=diff unq"))
       else
         tm |> eval (l - diff) renv cenv (fun v ->
             (match v with
              | Fut(body) -> Fut(Term.Unq(diff, body)) |> k
              | _ -> failwith "hoge l>diff unq"))
     | (l, Term.PolyCls(cls, base, body)) ->
       let cls' = Cls.alloc() in
       let base' = cenv |> CodeEnv.rename_cls base in
       let cenv' = (CodeEnv.(Cls(cls, cls') :: cenv)) in
       body |> eval l renv cenv' (fun v ->
           match v with
           | Fut(bodyv) -> Fut(Term.PolyCls(cls', base', bodyv)) |> k
           | _ -> failwith "hoge l polycls")
     | (l, Term.AppCls(tm, cls)) ->
       let cls' = cenv |> CodeEnv.rename_cls cls in
       tm |> eval l renv cenv (fun v ->
           match v with
           | Fut body -> Fut(AppCls(body, cls')) |> k
           | _ -> failwith "hoge l appcls")
     | (l, Term.Fix(f)) ->
       f |> eval l renv cenv (fun v -> match v with
           | Fut body -> Fut(Fix body) |> k
           | _ -> failwith "hoge l fix")
     | (l, Term.If(cond, thenn, elsee)) ->
       cond  |> eval l renv cenv (fun condv ->
           thenn |> eval l renv cenv (fun thenv ->
               elsee |> eval l renv cenv (fun elsev ->
                   match (condv, thenv, elsev) with
                   | (Fut(cbody), Fut(tbody), Fut(ebody)) ->
                     Fut(Term.If(cbody, tbody, ebody)) |> k
                   | _ -> failwith "hoge l if"
                 )))
  )


let%test_unit "hoge" =
  [%test_result: Value.t]
    ("1"
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Int 1);
  [%test_result: Value.t]
    ("true"
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Bool true);
  [%test_result: Value.t]
    ("1 + 2"
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Int 3);
  [%test_result: Value.t]
    ("not (1 < 2)"
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Bool false);
  [%test_result: Value.t]
    ("(1 < 2) && (2 < 3)"
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Bool true);
  [%test_result: Value.t]
    ("if true then 1 else 0"
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Int 1);
  [%test_result: Value.t]
    ("let x:int = 1 in x"
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Int 1);
  [%test_result: Value.t]
    ("let x:int = 1 in x"
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Int 1)

let%test_unit "code generation" =
  [%test_result: Value.t]
    ("`{@! 1 }"
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Code(Term.(Quo(Cls.init, Int 1))));
  [%test_result: Value.t]
    ("`{@! 1 + 1 }"
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Code(Term.(Quo(Cls.init, BinOp(BinOp.Plus, Int 1, Int 1)))));
  [%test_result: Value.t]
    ("`{@! fun (x:int@g) -> ~{ `{@g x } }  }"
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Code(Term.(Quo(Cls.init, BinOp(BinOp.Plus, Int 1, Int 1)))));
  [%test_result: Value.t]
    ("`{@! fun (f:int->int)(x:int) -> f x }"
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Code(Term.(Quo(Cls.init, BinOp(BinOp.Plus, Int 1, Int 1)))))

let%test_unit "do we need clousre for cenv?"  =
  [%test_result: Value.t]
    ({|
        `{@!
          let x:int@g1 = 1 in
          ~{
            let f (y:int):<int@g1> = `{@g1 x} in
            `{@g1
              let x:int = 2 in
              x + ~{ f 0 }
            }
          }
        }

     |}
     |> Cui.read_term
     |> eval 0 [] [] (fun x -> x))
    ~expect:(Value.Code (
        {|
           `{@!
             let x1:int = 1 in
             let x2:int = 2 in
             x1 + x2
           }
         |} |> Cui.read_term
      ));
