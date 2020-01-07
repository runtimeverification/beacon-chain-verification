Model State
===========


```k

requires "proof-script.k"
requires "hash.k"

module VALSET

    imports PROOF-SCRIPT
    imports HASH
    
    syntax FinValSet
 // ----------------
 
    syntax Pred ::= SubsetP
                  | QuorumP
                  
    
    syntax SubsetP ::= FinValSet "<=" FinValSet
    
    
    // subset properties?
    // finite set assumption
    // membership predicate?
    
    syntax QuorumP ::= "most" FinValSet  // holds for sets containing "2/3" of all validators or more
                     | "some" FinValSet  // holds for sets containing "1/3" of all validators or more
    
    rule
    <k> apply("quorum_property") => . ... </k>
    <g> most VS1 and most VS2 => some ?VS3:FinValSet and (?VS3 <= VS1 and ?VS3 <= VS2) </g>
             
    
endmodule

module STATE

    imports VALSET
```

A Casper validator
```k
    syntax Validator ::= #val ( id : Int ) [klabel(#val), symbol]
 // -------------------------------------------------------------  
```

A Casper FFG vote 

```k
    syntax Vote ::= #vote( val : Validator, src : Hash , trgt : Hash , srcH : Int , trgtH : Int )  [klabel(#vote), symbol]
 // ------------------------------------------------------------------------------------------------------------------------ 
```

```k
endmodule

```
