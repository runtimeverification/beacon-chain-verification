Validators
==========

An abstract representation of validators and validator sets.

```k
requires "proof-script.k"
requires "hash.k"
```

```k
module VALIDATOR

    imports PROOF-SCRIPT
    imports HASH
```

A Casper validator

```k
    syntax Validator ::= #val ( id : Int ) [klabel(#val), symbol]
 // -------------------------------------------------------------  
```

A finite set of validators

```k
    syntax FinValSet
 // ----------------
```

Validator set predicates

```k
    syntax Pred ::= SubsetP
                  | QuorumP

    syntax SubsetP ::= FinValSet "<=" FinValSet
    
    syntax ValMemberP ::= Validator "in" FinValSet
   
    syntax ValEmptyP ::= "empty" FinValSet
    
    // subset properties?
    // finite set assumption
```

Quorum Predicates:

- `most`: defines sets of validators containing "2/3" of all validators or more 
- `some`: defines sets of validators containing "1/3" of all validators or more 

```k
    syntax QuorumP ::= "most" FinValSet  // holds for sets containing "2/3" of all validators or more
                     | "some" FinValSet  // holds for sets containing "1/3" of all validators or more
```

The main quorum property that is assumed to hold:

```k
    rule
    <k> apply("quorum_property") => . ... </k>
    <g> most VS1 and most VS2 => some ?VS3:FinValSet and (?VS3 <= VS1 and ?VS3 <= VS2) </g>
``` 

```k
endmodule
```
