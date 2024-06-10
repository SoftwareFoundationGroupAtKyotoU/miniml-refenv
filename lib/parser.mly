%{
    open Syntax

    type argument =
      | VarArg of Var.t * Typ.t * Cls.t
      | ClsArg of Cls.t * Cls.t

    let rec expand_arglist arglist body =
      match arglist with
      | [] -> body
      | VarArg(v, typ, cls) :: rest ->
         expand_arglist rest (Term.Lam(v, typ, cls, body))
      | ClsArg(cls, base) :: rest ->
         expand_arglist rest (Term.PolyCls(cls, base, body))

    let rec expand_functype arglist result_typ =
      match arglist with
      | [] -> result_typ
      | VarArg(_, typ, _) :: rest ->
         expand_functype rest (Typ.Func(typ, result_typ))
      | ClsArg(cls, base) :: rest ->
         expand_functype rest (Typ.PolyCls(cls, base, result_typ))

%}

%token <int> INTLIT
%token TRUE FALSE
%token <string> ID

%token LPAREN RPAREN
%token PLUS MINUS MULT LT EQUAL DIV MOD
%token NOT AND OR
%token IF THEN ELSE
%token FUN COLON AT RARROW
%token BANG
%token LET REC EQ IN UNDERSCORE
%token BACKQUOTE TILDE
%token FIX
%token LBRACE RBRACE LBRACKET RBRACKET ATAT
%token REF ASSIGN
%token EOF

%token GT CLSBOUND
%token BASEINT BASEBOOL UNIT

%right prec_let
%right prec_if
%left prec_fun
%right ASSIGN
%left OR
%left AND
%left EQUAL
%left LT
%left PLUS MINUS
%left MULT DIV MOD
%nonassoc NOT BANG
%nonassoc ATAT
%nonassoc TRUE
%nonassoc FALSE
%nonassoc INTLIT
%nonassoc ID
%nonassoc LPAREN
%nonassoc BACKQUOTE
%nonassoc TILDE
%nonassoc prec_polyctxtyp
%right RARROW
%nonassoc REF

%start <Term.t> toplevel
%start <Typ.t> toplevel_typ

%%

toplevel:
  | expr EOF { $1 }

toplevel_typ:
  | typ EOF { $1 }

bindingcls:
  | ID { Cls.from_string $1 }
  | UNDERSCORE { Cls.alloc () }

referringcls:
  | ID { Cls.from_string $1 }
  | BANG { Cls.init }

simple_expr: (* Expressions that can be used as an argument as-is *)
  | LPAREN expr RPAREN { $2 }
  | LPAREN RPAREN { Term.Nil }
  | INTLIT { Term.Int($1) }
  | TRUE { Term.Bool(true) }
  | FALSE { Term.Bool(false) }
  | referringvar { Term.Var($1) }
(* Quote *)
  | BACKQUOTE LBRACE AT referringcls expr RBRACE
    { Term.Quo($4, $5) }
(* Unquote *)
  | TILDE INTLIT block
    { Term.(Unq($2, $3)) }
  | TILDE block
    { Term.(Unq(1, $2)) }
  | TILDE INTLIT referringvar
    { Term.(Unq($2, Var($3))) }
  | TILDE referringvar
    { Term.(Unq(1, Var($2))) }

referringvar:
  | ID { Var.from_string($1) }

bindingvar:
  | ID { Var.from_string($1) }
  | UNDERSCORE { Var.alloc() }

expr:
  (* Literals *)
  | simple_expr { $1 }
  (* Arithmetic operators *)
  | expr PLUS expr  { Term.BinOp(BinOp.Plus, $1, $3) }
  | expr MINUS expr { Term.BinOp(BinOp.Minus, $1, $3) }
  | expr MULT expr  { Term.BinOp(BinOp.Mult, $1, $3) }
  | expr DIV expr   { Term.BinOp(BinOp.Div, $1, $3) }
  | expr MOD expr   { Term.BinOp(BinOp.Mod, $1, $3) }
(* Comparison operator *)
  | expr EQUAL expr { Term.BinOp(BinOp.Equal, $1, $3) }
  | expr LT expr    { Term.BinOp(BinOp.LT, $1, $3) }
(* Logical operator *)
  | NOT expr      { Term.UniOp(UniOp.Not, $2) }
  | expr AND expr { Term.ShortCircuitOp(ShortCircuitOp.And, $1, $3) }
  | expr OR expr  { Term.ShortCircuitOp(ShortCircuitOp.Or, $1, $3) }
(* If statement *)
  | IF expr THEN expr ELSE expr %prec prec_if { Term.If($2, $4, $6) }
(* Function / Context abstraction *)
  | FUN arglist RARROW expr %prec prec_fun
    { expand_arglist $2 $4 }
(* Application *)
  | expr simple_expr { Term.App($1, $2) }
(* Classifier application *)
  | expr ATAT referringcls
    { Term.(AppCls($1, $3)) }
(* Let expression *)
  | LET bindingvar COLON typ EQ expr IN expr %prec prec_let
    { Term.(App(Lam($2, $4, Cls.alloc(), $8), $6)) }
  | LET bindingvar COLON typ AT referringcls EQ expr IN expr %prec prec_let
    { Term.(App(Lam($2, $4, $6, $10), $8)) }
  | LET bindingvar arglist COLON typ EQ expr IN expr %prec prec_let
    {
      let f = expand_arglist $3 $7 in
      let ftyp = expand_functype $3 $5 in
      Term.(App(Lam($2, ftyp, Cls.alloc(), $9), f))
    }
  | LET bindingvar arglist COLON typ AT referringcls EQ expr IN expr %prec prec_let
    {
      let f = expand_arglist $3 $9 in
      let ftyp = expand_functype $3 $5 in
      Term.(App(Lam($2, ftyp, $7, $11), f))
    }
(* Let rec expression *)
  | LET REC bindingvar arglist COLON typ EQ expr IN expr %prec prec_let
    {
      let f = expand_arglist $4 $8 in
      let ftyp = expand_functype $4 $6 in
      Term.(App(Lam($3, ftyp, Cls.alloc(), $10),
            Fix(Lam($3, ftyp, Cls.alloc(), f))))
    }
  | LET REC bindingvar arglist COLON typ AT referringcls EQ expr IN expr %prec prec_let
    {
      let f = expand_arglist $4 $10 in
      let ftyp = expand_functype $4 $6 in
      Term.(App(Lam($3, ftyp, $8, $12),
            Fix(Lam($3, ftyp, $8, f))))
    }
(* Let expression for unit *)
  | LET LPAREN RPAREN EQ expr IN expr %prec prec_let
    { Term.(App(Lam(Var.alloc(), Typ.Unit, Cls.alloc(), $7), $5)) }
(* ref *)
  | REF expr
    { Term.Ref $2 }
  | BANG expr
    { Term.Deref $2 }
  | expr ASSIGN expr
    { Term.Assign($1, $3) }

arg:
  | LPAREN bindingvar COLON typ AT referringcls RPAREN
    { VarArg($2, $4, $6) }
  | LPAREN bindingvar COLON typ RPAREN
    { VarArg($2, $4, Cls.alloc()) }
  | LBRACKET bindingcls CLSBOUND referringcls RBRACKET
    { ClsArg($2, $4) }

arglist:
  | arg { [$1] }
  | arglist arg { $2 :: $1 }

block:
  | LBRACE expr RBRACE { $2 }

typ:
  | LPAREN typ RPAREN { $2 }
  | BASEINT { Typ.BaseInt }
  | BASEBOOL { Typ.BaseBool }
  | typ RARROW typ { Typ.Func($1, $3) }
  | LT typ AT referringcls GT { Typ.Code($4, $2) }
  | LBRACKET bindingcls CLSBOUND referringcls RBRACKET typ %prec prec_polyctxtyp
    { Typ.(PolyCls($2,$4,$6)) }
  | REF typ { Typ.Ref($2) }
  | UNIT { Typ.Unit }
