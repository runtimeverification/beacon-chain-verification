Justification Epoch
===================


```k

requires "justification_ext.k"

module JUSTIFICATION-EPOCH 

    imports JUSTIFICATION-EXT

```

Definition: justification in terms of a path from the epoch start

```k
    syntax JustifiedThisEpochP ::= justifiedThisEpoch(FinVoteSet, Hash, Int)
 // ------------------------------------------------------------------------

    syntax Pred ::= JustifiedThisEpochP
```

- `justified_this_epoch` introduction rules:

```k
    rule
    <k> apply("justified_this_epoch.i") => . ... </k>
    <g> true => justifiedThisEpoch(?VS, epoch_start, epoch_height) </g>

    rule
    <k> apply("justified_this_epoch.i") => . ... </k>
    <g> justifiedThisEpoch(VS, S, SH) and 
       (S <~* T and 
        superMajorityLink(VS, S, T, SH, TH)) 
        => justifiedThisEpoch(VS, T, TH) 
    </g>
```

- `justified_this_epoch` elimination rules:

```k
    rule
    <k> apply("justified_this_epoch.e") => . ... </k>
    <g> justifiedThisEpoch(VS, epoch_start, H)  => H == epoch_height </g>

    rule
    <k> apply("justified_this_epoch.e") => . ... </k>
    <g> justifiedThisEpoch(VS, T, TH) and ~ (T == epoch_start)
        => ?S <~* T and 
          (superMajorityLink(VS, ?S, T, ?SH, TH) and 
           justifiedThisEpoch(VS, ?S, ?SH)) 
    </g>
```

```k
endmodule

```
