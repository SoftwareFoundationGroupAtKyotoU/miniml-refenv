let x:int@g = 1 in
let f(y:<int@g>): int = ~0{ y } in
f `{@g x + x}

