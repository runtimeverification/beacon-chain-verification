Casper FFG Model
================

A model of Casper FFG based on previsouly developed models in Coq [here](https://github.com/runtimeverification/casper-proofs) 
and updated to accoommodate new justification and finalization rules. 

```k
module CASPER-SYNTAX

    imports INT

    syntax Hash ::= Int
    
    syntax Validator ::= #val ( id : Int )
```

A Casper FFG vote 
```k
    syntax Vote ::= #vote( val : Validator, src : Hash , trgt : Hash , srcH : Int , trgtH : Int )  [klabel(#vote), symbol]
 // ------------------------------------------------------------------------------------------------------------------------ 
```

### Predicates

```k
    syntax Pred ::= BlockP
                  | ParentP
                  | AncestorP
                  | NthAncestorP
```

- A predicate specifying valid block hashes
```k
    syntax BlockP ::= Block( Hash )
 // -------------------------------
```

- `b1 <~ b2` : Block `b1` is the parent block of block `b2`
```k
    syntax ParentP ::= Hash "<~"  Hash
 // ----------------------------------
```

- `b1 <~* b2`: Block `b1` is an ancestor block of block `b2`
```k
    syntax AncestorP ::= Hash "<~*" Hash
 // -----------------------------------
```

- `b1 <~[n] b2)`: Block `b1` is the `n`th ancestor of block `b2`
```k
    syntax NthAncestorP ::= Hash "<~" "[" Int "]" Hash
 // --------------------------------------------------
```

```k
endmodule
```
 
```k
module CASPER

    imports CASPER-SYNTAX
    imports PROOF-SCRIPT
    
    

endmodule

```
