%{
    open Syntax

    let makeop opcst a b = Term.(App(App(Const(opcst), a), b))
%}

%token <int> INTLIT
%token TRUE FALSE
%token <string> ID

%token LPAREN RPAREN
%token PLUS MINUS MULT LT
%token NOT AND OR
%token IF THEN ELSE
%token FUN COLON AT RARROW
%token BANG
%token LET REC EQ IN UNDERSCORE
%token BACKQUOTE TILDE
%token FIX
%token LBRACE RBRACE LBRACKET RBRACKET ATAT
%token EOF

%token GT CLSBOUND
%token BASEINT BASEBOOL

%right prec_if
%left prec_fun
%left OR
%left AND
%left LT
%left PLUS MINUS
%left MULT
%right NOT
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
  | INTLIT { Term.Int($1) }
  | TRUE { Term.Bool(true) }
  | FALSE { Term.Bool(false) }
  | referringvar { Term.Var($1) }
(* Quote *)
  | BACKQUOTE LBRACKET bindingcls CLSBOUND referringcls RBRACKET block
    { Term.Quo($3, $5, $7) }
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
  | expr PLUS expr { makeop Const.Plus $1 $3 }
  | expr MINUS expr { makeop Const.Minus $1 $3 }
  | expr MULT expr { makeop Const.Mult $1 $3 }
  (* Comparison operator *)
  | expr LT expr { makeop Const.LT $1 $3 }
(* Logical operator *)
  | NOT expr { Term.(App(Const(Const.Not), $2))}
  | expr AND expr { makeop Const.And $1 $3 }
  | expr OR expr { makeop Const.Or $1 $3 }
  (* If statement *)
  | IF expr THEN expr ELSE expr %prec prec_if { Term.If($2, $4, $6) }
  (* Function *)
  | FUN LPAREN bindingvar COLON typ AT bindingcls RPAREN RARROW expr %prec prec_fun { Term.Lam($3, $5, $7, $10) }
  | FUN LPAREN bindingvar COLON typ RPAREN RARROW expr %prec prec_fun { Term.Lam($3, $5, Cls.alloc(), $8) }
  (* Application *)
  | expr simple_expr { Term.App($1, $2) }
(* Classifier abstraction *)
  | LBRACKET bindingcls CLSBOUND referringcls RBRACKET RARROW expr %prec prec_fun
    { Term.(PolyCls($2, $4, $7)) }
(* Classifier application *)
  | expr ATAT referringcls
    { Term.(AppCls($1, $3)) }

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
