{
let reservedWords = [
  (* Keywords *)
  ("else", Parser.ELSE);
  ("false", Parser.FALSE);
  ("if", Parser.IF);
  ("then", Parser.THEN);
  ("true", Parser.TRUE);
  ("fix", Parser.FIX);
  ("let", Parser.LET);
  ("rec", Parser.REC);
  ("cs", Parser.CS);
  ("in", Parser.IN);
  ("not", Parser.NOT);
  ("int", Parser.BASEINT);
  ("bool", Parser.BASEBOOL);
  ("mod", Parser.MOD);
  ("ref", Parser.REF);
  ("unit", Parser.UNIT)
]
}

rule main = parse
  (* ignore spacing and newline characters *)
  [' ' '\009' '\012' '\n']+     { main lexbuf }

| "-"? ['0'-'9']+
    { Parser.INTLIT (int_of_string (Lexing.lexeme lexbuf)) }

| "(" { Parser.LPAREN }
| ")" { Parser.RPAREN }
| "+" { Parser.PLUS }
| "-" { Parser.MINUS }
| "*" { Parser.MULT }
| "/" { Parser.DIV }
| "<" { Parser.LT }
| "==" { Parser.EQUAL }
| "&&" { Parser.AND }
| "||" { Parser.OR }

| "fun" { Parser.FUN }
| "->" { Parser.RARROW }
| ":" { Parser.COLON }
| "@" { Parser.AT }
| "=" { Parser.EQ }
| "!" { Parser.BANG }

| ":=" { Parser.ASSIGN }

| "`" { Parser.BACKQUOTE }
| ">" { Parser.GT }
| ":>" { Parser.CLSBOUND }
| "~" { Parser.TILDE }

| "{" { Parser.LBRACE }
| "}" { Parser.RBRACE }
| "[" { Parser.LBRACKET }
| "]" { Parser.RBRACKET }
| "@@" { Parser.ATAT}

| ['a'-'z'] ['a'-'z' '0'-'9' '_']*
    { let id = Lexing.lexeme lexbuf in
      try
        List.assoc id reservedWords
      with
      _ -> Parser.ID id
     }
| "_" { Parser.UNDERSCORE }
| eof { EOF }
| "(*" { comment 0 lexbuf }
and comment i = parse
| "*)" { if (i = 0) then main lexbuf else comment (i-1) lexbuf }
| "(*" { comment (i+1) lexbuf }
| _ { comment i lexbuf }
| eof { exit (0) }