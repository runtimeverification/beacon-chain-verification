Hash Parent Relation
====================

An abstract representation of block trees based on the block parent relation.

```k

requires "proof-script.k"
requires "hash.k"

module HASH-PARENT 
    imports PROOF-SCRIPT
    imports HASH
```

### Predicates

```k
    syntax Pred ::= BlockP
                  | BlockEqP
                  | ParentP
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

### Assumptions

- A block has at most one parent

```k
   rule
   <k> apply("<~.e") => . ... </k>
   <g> B1 <~ B and B2 <~ B => B1 == B2 </g>
```

- The Genesis block has no parent

```k
   rule
   <k> apply("<~.e1") => . ... </k>
   <g> B1 <~ B2 => ~ (B2 == genesis) </g>
```

- Block parent relation is irreflexive

```k
   rule
   <k> apply("<~.e2") => . ... </k>
   <g> B1 <~ B2 => ~ (B1 == B2) </g> 
```

```k
    rule [subst]:
    <k> subst(V1, V2) => . ... </k>
    <g> V1 <~ V3 => V2 <~ V3 </g>
    <p> M </p> 
```

```k
endmodule
```
