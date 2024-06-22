let f(p:int)(y:<int@!>): int = ~0{
  let cs square(x:int):int@g = x * p in
  `{@g square ~y }
} in
f (1 + 1) `{@! 3 }
