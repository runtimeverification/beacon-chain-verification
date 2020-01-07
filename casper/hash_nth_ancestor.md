Hash Nth Ancestor Relation
==========================

A formalization of block hash ancestry that shows the distance in the block tree between an ancestor block and a decendent block.
```k

requires "hash_ancestor_ext.k"

module HASH-NTH-ANCESTOR

    imports HASH-ANCESTOR-EXT
```

### Predicates

```k
    syntax Pred ::= NthAncestorP
```

- `b1 <~[n] b2)`: Block `b1` is the `n`th ancestor of block `b2`
 
```k
    syntax NthAncestorP ::= Hash "<~" "[" Int "]" Hash
 // --------------------------------------------------
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

- Nth Ancestor predicate `<~[n]` elemination rules (should be derivable from rules above (?)):

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

```k
endmodule
```
