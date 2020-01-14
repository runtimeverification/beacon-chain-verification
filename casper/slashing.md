Slashing
========


```k

requires "proof-script.k"
requires "hash_parent.k"
requires "vote.k"

module SLASHING 

    imports PROOF-SCRIPT
    imports HASH-PARENT
    imports VOTE

```

- Predicate signature declarations

```k
    syntax SlashedP ::= slashedDblVote(FinVoteSet, Validator)
                      | slashedSurround(FinVoteSet, Validator)
                      | slashed(FinVoteSet, Validator)
    
    syntax Pred ::= SlashedP
```

- Definitions

Slashing due to double-voting:

```k
    rule
    <k> unfold("slashedDblVote") => . ... </k>
    <g> slashedDblVote(VS, VAL)
        => (~ (?T1 == ?T2)) and 
          (#vote(VAL, ?S1, ?T1, ?S1H, ?TH) in VS and 
           #vote(VAL, ?S2, ?T2, ?S2H, ?TH) in VS) 
    </g>

    rule
    <k> fold("slashedDblVote") => . ... </k>
    <g> (~ (T1 == T2)) and 
       (#vote(VAL, S1, T1, S1H, TH) in VS and 
        #vote(VAL, S2, T2, S2H, TH) in VS)
        => slashedDblVote(VS, VAL) </g>
```

Slashing due to surround-voting:

```K
    rule
    <k> unfold("slashedSurround") => . ... </k>
    <g> slashedSurround(VS, VAL) 
        => #vote(VAL, ?S1, ?T1, ?S1H, ?T1H) in VS and 
          (#vote(VAL, ?S2, ?T2, ?S2H, ?T2H) in VS and 
          (?S2H >Int ?S1H and 
           ?T2H <Int ?T1H))
    </g>

    rule
    <k> fold("slashedSurround") => . ... </k>
    <g> #vote(VAL, S1, T1, S1H, T1H) in VS and 
       (#vote(VAL, S2, T2, S2H, T2H) in VS and 
       (S2H >Int S1H and 
        T2H <Int T1H))
        => slashedSurround(VS, VAL)
    </g>
```

Slashing definition: 

```k
    rule
    <k> unfold("slashed") => . ... </k>
    <g> slashed(VS, V)
        => slashedDblVote(VS, V) or slashedSurround(VS, V)
    </g>

    rule
    <k> fold("slashed") => . ... </k>
    <g> slashedDblVote(VS, V) or slashedSurround(VS, V) 
        => slashed(VS, V)
    </g>
```

```k
endmodule

```
