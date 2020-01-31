Further Justification Properties
================================

```k

requires "justification_epoch.k"

module JUSTIFICATION-EXT2

    imports JUSTIFICATION-EPOCH

```

## Properties 

- Justified extends to larger vote-sets

```k
    rule
    <k> apply("justified_weaken") => . ... </k>
    <g> (VS1 <= VS2) and justifiedThisEpoch(VS1, T, TH) 
        => justifiedThisEpoch(VS2, T, TH)
    </g>
```

- Justified is a descendent of epoch_start

```k
    rule
    <k> apply("justified_is_descendant") => . ... </k>
    <g> justifiedThisEpoch(VS, T, TH) => epoch_start <~* T </g>
```

```k
endmodule

```
