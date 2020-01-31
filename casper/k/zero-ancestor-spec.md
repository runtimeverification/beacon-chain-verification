Lemma `zero_ancestor`
=====================

```k
require "hash_nth_ancestor.k"

module ZERO-ANCESTOR-SPEC

    imports V
    
    rule
    <g> B1 <~[0] B2 => B1 <~* B2 </g>
    <p> .Map => _ </p>
    <k> apply("nth.e")
        ~> apply("<~*.i")
        => . </k>
 
endmodule    
    
module V
    imports HASH-NTH-ANCESTOR
endmodule
```
