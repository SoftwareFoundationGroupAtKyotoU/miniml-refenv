```
cls : \$[0-9]+
var : [a-z][a-z0-9]*

type ::=
  int
| bool
| type -> type
| < type @ cls >
| [ cls :> cls ] type
| ( type )

intlit : (-)?[1-9][0-9]*
boollit ::= true | false
diff : [1-9][0-9]*

expr ::=
  var
| expr + expr
| expr - expr
| expr * expr
| expr >= expr
| not expr
| expr and expr
| expr or expr
| intlit
| boollit
| if expr then expr else expr
| \ bar : type @ cls -> { expr }
| \ bar : type -> { expr }
| expr expr
| ` < cls :> cls > { expr }
| ` < cls > { expr }
| ~ var
| ~ diff var
| ~ { expr }
| ~ diff { expr }
| [ cls :> cls ] { expr }
| expr @@ cls
| let var : type @ cls = expr in expr
| let var : type = expr in expr
| let rec var : type @ cls = expr in expr
| let rec var : type = expr in expr
```
