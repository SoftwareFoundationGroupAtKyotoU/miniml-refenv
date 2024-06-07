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
%token LET REC EQ IN UNDERSCORE
%token FIX
%token LBRACE RBRACE LBRACKET RBRACKET ATAT
%token EOF

%token GT CLSBOUND
%token BASEINT BASEBOOL

%right prec_if
%left OR
%left AND
%left LT
%left PLUS MINUS
%left MULT
%right RARROW
%nonassoc TRUE
%nonassoc FALSE
%nonassoc INTLIT
%nonassoc ID
%nonassoc LPAREN

%start <Term.t> toplevel
%start <Typ.t> toplevel_typ

%%

toplevel:
  | expr EOF { $1 }

toplevel_typ:
  | typ EOF { $1 }

cls:
  | ID { Cls.from_string $1 }

simple_expr: (* Expressions that can be used as an argument as-is *)
  | LPAREN expr RPAREN { $2 }
  | INTLIT { Term.Int($1) }
  | TRUE { Term.Bool(true) }
  | FALSE { Term.Bool(false) }
(* Variables *)
  | ID { Term.Var(Var.from_string($1)) }

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
  | expr AND expr { makeop Const.And $1 $3 }
  | expr OR expr { makeop Const.Or $1 $3 }
  (* If statement *)
  | IF expr THEN expr ELSE expr %prec prec_if { Term.If($2, $4, $6) }
  (* Function *)
  | FUN LPAREN bindingvar COLON typ AT cls RPAREN RARROW block { Term.Lam($3, $5, $7, $10) }
  | FUN LPAREN bindingvar COLON typ RPAREN RARROW block { Term.Lam($3, $5, Cls.alloc(), $8) }
  (* Application *)
  | expr simple_expr { Term.App($1, $2) }

block:
  | LBRACE expr RBRACE { $2 }

typ:
  | BASEINT { Typ.BaseInt }
  | BASEBOOL { Typ.BaseBool }
  | typ RARROW typ { Typ.Func($1, $3) }
