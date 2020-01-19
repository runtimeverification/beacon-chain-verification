Hash Ancestor Relation
======================

An extension of the block hash ancestry relation with some properties. 
```k

requires "hash_ancestor.k"

module HASH-ANCESTOR-EXT

    imports HASH-ANCESTOR
```

### Properties

- Transitivity of the relation extends to the right. Proved by induction on `<~*` in
  - `ancestor-parent-base1-spec`
  - `ancestor-parent-base2-spec`
  - `ancestor-parent-ind-spec` 

```k
    rule
    <k> apply("ancestor-parent") => . ... </k>
    <g> B1 <~* B2 and B2 <~ B3 => B1 <~* B3 </g>
```

- Concatenation of the ancestry relation. [TODO] Proved by induction on `<~*` in
  - `ancestor-ancestor-base1-spec`
  - `ancestor-ancestor-base2-spec`
  - `ancestor-ancestor-ind-spec` 

```k
    rule
    <k> apply("ancestor-ancestor") => . ... </k>
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
