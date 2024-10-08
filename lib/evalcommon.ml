open Base
open Syntax

module RuntimeEnv = struct
  type 'a t = (Var.t * Cls.t * 'a) list
  [@@deriving compare, equal, sexp]

  let rec lookup_var(v:Var.t)(env:'a t): 'a =
    match env with
    | [] -> failwith "failed to lookup var"
    | (v1, _, value) :: rest ->
      if Var.equal v v1
      then value
      else rest |> lookup_var v

  let current(env: 'a t): Cls.t =
    match env with
    | [] -> Cls.init
    | (_, g, _) :: _ -> g

  let display (env: 'a t)(display_elm: 'a -> string)(indent: int): string =
    let spc = (String.make indent ' ') in
    let rec hoge env1 = (match env1 with
        | [] -> ""
        | (var, cls, elm) :: tail ->
          spc ^ "  " ^
          Printf.sprintf "%s@%s := %s\n" (Var.display var) (Cls.display cls) (display_elm elm)
          ^ hoge tail
      )

    in
    "{\n" ^ hoge env ^ spc ^ "}"

  let display_abbr (env: 'a t): string =
    let hoge = env |> List.map ~f:(fun (var, _, _) -> Var.display var)
               |> String.concat ~sep:", " in
    "{r| " ^ hoge ^ " }"

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
      let cls' = Cls.color cls in
      let base' = env |> rename_cls base in
      let ty' = ty |> Typ.rename_cls cls cls' in
      let ty' = env |> rename_cls_in_typ ty' in
      Typ.PolyCls (cls', base', ty')
    | Typ.Unit -> Typ.Unit
    | Typ.Ref ty -> Typ.Ref(env |> rename_cls_in_typ ty)

  let display (env:t)(indent:int): string =
    let spc = (String.make indent ' ') in
    let rec hoge env1 = (match env1 with
        | [] -> ""
        | Var(var, var1) :: tail ->
          spc ^ "  " ^
          (Printf.sprintf "%s := %s\n" (Var.display var) (Var.display var1)) ^
          hoge tail
        | Cls(cls, cls1) :: tail ->
          spc ^ "  " ^
          (Printf.sprintf "%s := %s\n" (Cls.display cls) (Cls.display cls1)) ^
          hoge tail
      ) in
    "{\n" ^ hoge env ^ spc ^ "}"

  let display_abbr (env: t): string =
    let hoge = env
               |> List.map ~f:(fun elm -> (match elm with
                   | Var (var, _) -> Var.display var
                   | Cls (cls, _) -> Cls.display cls))
               |> String.concat ~sep:", " in
    "{c| " ^ hoge ^ " }"

end

module Loc = struct
  type t = int
  [@@deriving compare, equal, sexp]

  let counter = ref 0

  let alloc () =
    let ret = !counter in
    counter := ret + 1;
    ret

  let display (loc : t) =
    Printf.sprintf "[loc %d]" loc
end

module Value = struct
  type t =
    | Int of int
    | Bool of bool
    | Clos of t RuntimeEnv.t * CodeEnv.t * Term.t
    | Code of Term.t
    | Loc of Loc.t
    | Nil
  [@@deriving compare, equal, sexp]

  let display (v : t) : string =
    (match v with
     | Int i -> Int.to_string i
     | Bool b -> Bool.to_string b
     | Clos (_renv, _cenv, body) ->
       Printf.sprintf "Clos(..., %s)" (Term.display body)
     | Code body ->
       (Term.display body)
     | Loc loc ->
       (Loc.display loc)
     | Nil -> "()")
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

module Primitives = struct

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

end
