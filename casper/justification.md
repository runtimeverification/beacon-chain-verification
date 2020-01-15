Justification
=============


```k

requires "hash_nth_ancestor_ext.k"
requires "slashing.k"

module JUSTIFICATION 

    imports HASH-NTH-ANCESTOR-EXT
    imports SLASHING

```

- Epoch start height assumption

```k

    syntax Hash ::= "epoch_start" 
    syntax Int ::= "epoch_height"
    
    // hypothesis epoch_ancestry : nth_ancestor epoch_height genesis epoch_start.
    rule
    <k> apply("epoch_ancestry") => . ... </k>
    <g> genesis <~[epoch_height] epoch_start => true </g>

```

- Definitions

The set of validators supporting a link in a state:

```k
    syntax FinValSet ::= linkSupporters(FinVoteSet, Hash, Hash, Int, Int)

    rule
    <k> unfold("linkSupporters") => . ... </k>
    <g> VAL in linkSupporters(VS, S, T, SH, TH) 
        => #vote(VAL, S, T, SH, TH) in VS 
    </g>

    rule
    <k> fold("linkSupporters") => . ... </k>
    <g> #vote(VAL, S, T, SH, TH) in VS 
        => VAL in linkSupporters(VS, S, T, SH, TH) 
    </g>
```

Supermajority links

```k
    syntax SuperMP ::= superMajorityLink(FinVoteSet, Hash, Hash, Int, Int)
    
    rule
    <k> unfold("superMajorityLink") => . ... </k>
    <g> superMajorityLink(VS, S, T, SH, TH)
        => most linkSupporters(VS, S, T, SH, TH)
    </g>
    
    rule
    <k> fold("superMajorityLink") => . ... </k>
    <g> most linkSupporters(VS, S, T, SH, TH) 
        => superMajorityLink(VS, S, T, SH, TH)
    </g>
```

```k
endmodule

```
