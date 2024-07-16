let spower(n:int): <int->int@!> =
  `{@! fun (x:int@g1) -> ~{spower_@@g1 n `{@g1 x}}} in
spower 5
