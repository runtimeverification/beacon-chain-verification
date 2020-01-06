Hash Ancestor Relation
======================

An extension of the block hash ancestry relation with some properties. 
```k

requires "hash_ancestor.k"

module HASH-ANCESTOR-EXT

    imports HASH-ANCESTOR
```

### Properties

- Transitivity of the relation extends to the right ([TODO] shown in `hash_ancestor_rstep-spec.md` by induction on `<~*`):

```k
    rule
    <k> apply("<~*.rstep") => . ... </k>
    <g> B1 <~* B2 and B2 <~ B3 => B1 <~* B3 </g>
```

- Transitivity of the relation composes ([TODO] shown in `hash_ancestor_comp-spec.md` by induction on `<~*`):

```k
    rule
    <k> apply("<~*.i") => . ... </k>
    <g> B1 <~* B2 and B2 <~* B3 => B1 <~* B3 </g>
```

- Two conflicting blocks cannot have common ancestry ([TODO] shown in `hash_ancestor_conf-spec.md`):

```k
    rule
    <k> apply("</~*.i") => . ... </k>
    <g> B1 <~* B and ~ (B2 <~* B) => ~ (B2 <~* B1) </g>
```

```k
endmodule
```
