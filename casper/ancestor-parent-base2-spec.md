Lemma `ancestor-parent` Base Case 2
===================================

```k
require "hash_ancestor.k"

module ANCESTOR-PARENT-BASE2-SPEC

    imports V
    
    rule
    <g> B1 <~ B2 and B2 <~ B3 => B1 <~* B3 </g>
    <p> .Map => _ </p>
    <k> store2("p1", "p2")
        ~> load("p2")
        ~> apply("<~*.i")
        ~> store1("p2")
        ~> load("p1")
        ~> load("p2")
        ~> apply("<~*.i")
        => . </k>
 
endmodule    
    
module V
    imports HASH-ANCESTOR
endmodule
```
