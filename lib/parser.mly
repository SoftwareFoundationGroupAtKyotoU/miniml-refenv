%{
    open Syntax

    let makeop opcst a b = Term.(App(App(Const(opcst), a), b))
%}

%token <int> INTLIT
%token TRUE FALSE
%token <string> VARID
%token <string> CLSID

%token LPAREN RPAREN
%token PLUS MINUS MULT LT
%token NOT AND OR
%token IF THEN ELSE
%token FUN COLON RARROW
%token LET REC EQ IN
%token FIX
%token GT CLSBOUND
%token BASEINT BASEBOOL
%token LBRACE RBRACE LBRACKET RBRACKET ATAT
%token EOF

%right prec_if
%left OR
%left AND
%left LT
%left PLUS MINUS
%left MULT

%start <Term.t> toplevel

%%

toplevel:
  | expr EOF { $1 }

expr:
(* Literals *)
  | INTLIT { Term.Int($1) }
  | TRUE { Bool(true) }
  | FALSE { Bool(false) }
(* Arithmetic operators *)
  | expr PLUS expr { makeop Const.Plus $1 $3 }
  | expr MINUS expr { makeop Const.Minus $1 $3 }
  | expr MULT expr { makeop Const.Mult $1 $3 }
  | LPAREN expr RPAREN { $2 }
(* Comparison operator *)
  | expr LT expr { makeop Const.LT $1 $3 }
(* Logical operator *)
  | expr AND expr { makeop Const.And $1 $3 }
  | expr OR expr { makeop Const.Or $1 $3 }
(* primitive syntax *)
  | IF expr THEN expr ELSE expr %prec prec_if
    { Term.If($2, $4, $6) }

