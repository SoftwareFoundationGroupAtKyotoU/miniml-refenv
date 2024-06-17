let rec spower_[g:>!](n:int)(xq:<int@g>)(cont:[h:>g]<int@h>-><int@h>):<int@g> =
  if n == 0 then
    cont@@g `{@g 1 }
  else if n == 1 then
    cont@@g xq
  else if n mod 2 == 1 then
    spower_@@g (n - 1) xq
      (fun[g1:>g](yq:<int@g1>) -> cont@@g1 `{@g1 ~xq * ~yq})
  else
    `{@g
      let x2:int@g2 = ~xq * ~xq in
      ~{
        spower_@@g2 (n / 2) `{@g2 x2}
          (fun[g3:>g2](yq:<int@g3>) -> cont@@g3 yq)
      }
    } in

let spower(n:int):<int->int@!> =
  `{@!
     fun(x:int@g)->
       ~{ spower_@@g n `{@g x } (fun[g1:>g](y:<int@g1>) -> y) }
  } in

`{@!
  let power11(x:int):int = ~{spower 11} x in
  power11 2
}
