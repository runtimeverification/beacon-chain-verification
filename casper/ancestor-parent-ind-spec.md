Lemma `ancestor-parent` Inductive Case
======================================

```k
require "hash_ancestor.k"

module ANCESTOR-PARENT-IND-SPEC

    imports V
    
    rule
    <g> (B1 <~ B and B <~* B2) and B2 <~ B3 => B1 <~* B3 </g>
    <p> .Map => _ </p>
    <k> store2("p", "p3")
        ~> load("p")
        ~> store2("p1", "p2")
        ~> load("p2")
        ~> load("p3")
        ~> apply("ancestor-parent-ih")
        ~> store1("p4")
        ~> load("p1")
        ~> load("p4")
        ~> apply("<~*.i")
        => . </k>
 
    // induction hypothesis
    rule
    <k> apply("ancestor-parent-ih") => . ... </k>
    <g> B <~* B2 and B2 <~ B3 => B <~* B3 </g>
    [trusted]
 
endmodule    
    
module V
    imports HASH-ANCESTOR
endmodule
```
