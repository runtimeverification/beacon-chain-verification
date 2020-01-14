Justification
=============


```k

requires "proof-script.k"
requires "slashing.k"

module JUSTIFICATION 

    imports PROOF-SCRIPT
    imports SLASHING

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

```k
endmodule

```
