Hash Nth Ancestor Relation
==========================

An extension of the nth ancestry relation with some properties.
```k

requires "hash_nth_ancestor.k"

module HASH-NTH-ANCESTOR-EXT

    imports HASH-NTH-ANCESTOR
```

### Properties

- The 0th ancestor of a block is itself (shown in `zero-ancestor-spec.md`)

```k
    rule
    <k> apply("zero_ancestor") => . ... </k>
    <g> B1 <~[0] B2 => B1 == B2 </g>
```

- The parent block is the first ancestor
 
```k
    rule
    <k> apply("parent_ancestor") => . ... </k>
    <g> B1 <~ B2 => B1 <~[1] B2 </g>
```

- The nth ancestor is an ancestor
 
```k
    rule
    <k> apply("nth_ancestor_ancestor") => . ... </k>
    <g> B1 <~[N] B2 => B1 <~* B2 </g>
```

```k
endmodule
```
