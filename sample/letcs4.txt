let cs inc(n:int):int@g1 = n + 1 in
if inc 0 < inc (inc 0)
then `{@g1 inc 0 }
else `{@g1 0 }

