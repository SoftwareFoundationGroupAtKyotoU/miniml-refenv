let f[g1:>!](k : [g2:>g1]<int@g2> -> <int@g2>):<int@g1> = k@@g1 `{@g1 1 } in
f@@! (fun[g2:>!](x:<int@g2>) -> `{@g2 1 + ~x })

