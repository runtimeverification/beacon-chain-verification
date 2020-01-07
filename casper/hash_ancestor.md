Hash Ancestor Relation
======================

The block hash ancestry relation as the  transitive closure of the hash-parent relation. 
```k

requires "hash_parent.k"

module HASH-ANCESTOR

    imports HASH-PARENT
```

### Predicates

```k
    syntax Pred ::= AncestorP
```

- `b1 <~* b2`: Block `b1` is an ancestor block of block `b2`

```k
    syntax AncestorP ::= Hash "<~*" Hash
 // -----------------------------------
```

- Ancestor predicate `<~*` introduction rules:

```k
    rule
    <k> apply("<~*.i") => . ... </k>
    <g> B1 <~ B2 => B1 <~* B2 </g>
 
    rule
    <k> apply("<~*.i") => . ... </k>
    <g> B1 <~ B2 and B2 <~* B3 => B1 <~* B3 </g>
```

```k
endmodule
```
