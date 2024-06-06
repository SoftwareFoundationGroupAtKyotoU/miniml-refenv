%{
    open Syntax
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

%left PLUS MINUS
%left MULT

%start <Term.t> toplevel

%%

toplevel:
  | expr EOF { $1 }

expr:
  | expr PLUS expr { Term.(App(App(Const(Const.Plus), $1), $3)) }
  | expr MINUS expr { Term.(App(App(Const(Const.Minus), $1), $3)) }
  | expr MULT expr { Term.(App(App(Const(Const.Mult), $1), $3)) }
  | INTLIT { Term.Int($1) }
  | LPAREN expr RPAREN { $2 }

