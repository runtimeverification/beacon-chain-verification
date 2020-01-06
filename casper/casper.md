Casper FFG Model
================

A model of Casper FFG based on previsouly developed models in Coq [here](https://github.com/runtimeverification/casper-proofs) 
and updated to accoommodate new justification and finalization rules. 

```k

requires "proof-script.k"

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
    syntax BlockP ::= Block( Hash ) [klabel(#block), symbol]
 // -------------------------------------------------------
```

- A predicate specifying equality on block hashes

```k
    syntax BlockEqP ::= Hash "==" Hash
 // ----------------------------------
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
    
```

- A block has at most one parent

```k
   rule
   <k> apply("<~.e") => . ... </k>
   <g> B1 <~ B and B2 <~ B => B1 == B2 </g>
```

- Ancestor predicate `<~*` introduction rules:

```k
    rule
    <k> apply("<~*.i") => . ... </k>
    <g> B1 <~ B2 => B1 <~* B2 </g>
 
    rule
    <k> apply("<~*.i") => . ... </k>
    <g> B1 <~ B2 and B2 <~* B3 => B1 <~* B3 </g>

    rule
    <k> apply("<~*.i") => . ... </k>
    <g> B1 <~* B2 and B2 <~ B3 => B1 <~* B3 </g>
    
    rule
    <k> apply("<~*.i") => . ... </k>
    <g> B1 <~* B2 and B2 <~* B3 => B1 <~* B3 </g>
```

- Nth Ancesestor predicate `<~[n]` introduction rules:

```k
    rule
    <k> apply("nth.i") => . ... </k>
    <g> Block(B) => B <~[0] B  </g>

    rule
    <k> apply("nth.i") => . ... </k>
    <g> B1 <~[N] B2 and B2 <~ B3
       => B1 <~[N +Int 1] B3 </g>
```

- Nth Ancestor predicate `<~[n]` elemination rules:

```k
    rule
    <k> apply("nth.e") => . ... </k>
    <g> B1 <~[0] B2 => B1 == B2 </g>

    rule
    <k> apply("nth.e") => . ... </k>
    <g> B1 <~[N] B3
       => (B1 <~[N -Int 1] ?B2:Int) and ?B2 <~ B3 </g>
          requires N >Int 0
```

- Two conflicting blocks cannot have common ancestry

```k
    rule
    <k> apply("</~*.i") => . ... </k>
    <g> B1 <~* B and ~ (B2 <~* B) => ~ (B2 <~* B1) </g>

endmodule

```
