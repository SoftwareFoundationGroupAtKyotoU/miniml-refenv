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
  ("rec", Parser.LET);
  ("in", Parser.IN);
  ("not", Parser.NOT);
  ("int", Parser.BASEINT);
  ("bool", Parser.BASEBOOL);
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
| "<" { Parser.LT }
| "&&" { Parser.AND }
| "||" { Parser.OR }

| "\\" { Parser.FUN }
| "->" { Parser.RARROW }
| ":" { Parser.COLON }
| "=" { Parser.EQ }

| ">" { Parser.GT }
| ":>" { Parser.CLSBOUND }

| "{" { Parser.LBRACE }
| "}" { Parser.RBRACE }
| "[" { Parser.LBRACKET }
| "]" { Parser.RBRACKET }
| "@@" { Parser.ATAT}

| ['a'-'z'] ['a'-'z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      try
        List.assoc id reservedWords
      with
      _ -> Parser.VARID id
     }
| '@' ['a'-'z' '0'-'9' '_' '\'']*
    { let id = Lexing.lexeme lexbuf in
      Parser.CLSID id
    }
| eof { EOF }

