Hash Nth Ancestor Relation
==========================

An extension of the nth ancestry relation with some properties.
```k

requires "hash_nth_ancestor.k"

module HASH-NTH-ANCESTOR-EXT

    imports HASH-NTH-ANCESTOR
```

### Properties

- The parent block is the first ancestor

```k
    rule
    <k> apply("parent_ancestor") => . ... </k>
    <g> B1 <~ B2 => B1 <~[1] B2 </g>
```

```k
endmodule
```
