let square(x:int):int@g1 = x * x in
let rec spower_[g2:>g1](n:int)(xq:<int@g2>):<int@g2> =
  if n == 0 then
   `{@g2 1 }
  else if n mod 2 == 1 then
   `{@g2 ~xq * ~{spower_@@g2 (n - 1) xq }}
  else
   `{@g2 square ~{spower_@@g2 (n / 2) xq} } in
let spower(n:int):<int->int@g1> =
  `{@g1 fun(x:int@g3) -> ~{spower_@@g3 n `{@g3 x }}} in
let pow11:int->int = ~0{spower 11} in
pow11 2

