Slashing
========


```k

requires "proof-script.k"
requires "vote.k"

module VOTE 

    imports PROOF-SCRIPT
    imports VOTE

```

- Predicate signature declarations

```k
    syntax SlashedP ::= slashed_dbl_vote(FinVoteSet, Validator)
                      | slashed_surround(FinVoteSet, Validator)
                      | slashed(FinVoteSet, Validator)
    
    syntax Pred ::= SlashedP
```

- Definitions

Slashing due to double-voting:

```k
    rule
    <k> unfold("slashed_dbl_vote") => . ... </k>
    <g> slashed_dbl_vote(VS, V) 
        => neg (?T1 == ?T2) and 
          (#vote(?VAL, ?S1, ?T1, ?S1H, ?TH) in VS and 
           #vote(?VAL, ?S2, ?T2, ?S2H, ?TH) in VS) 
    </g>

    rule
    <k> fold("slashed_dbl_vote") => . ... </k>
    <g> neg (T1 == T2) and 
       (#vote(VAL, S1, T1, S1H, TH) in VS and 
        #vote(VAL, S2, T2, S2H, TH) in VS)
        => slashed_dbl_vote(VS, V) </g>
```

Slashing due to surround-voting:

```K
    rule
    <k> unfold("slashed_surround") => . ... </k>
    <g> slashed_surround(VS, V) 
        => #vote(?VAL, ?S1, ?T1, ?S1H, ?T1H) in VS and 
          (#vote(?VAL, ?S2, ?T2, ?S2H, ?T2H) in VS and 
          (S2H > S1H and 
           T2H < T1H))
    </g>

    rule
    <k> fold("slashed_surround") => . ... </k>
    <g> #vote(VAL, S1, T1, S1H, T1H) in VS and 
       (#vote(VAL, S2, T2, S2H, T2H) in VS and 
       (S2H > S1H and 
        T2H < T1H)
        => slashed_surround(VS, V)
    </g>
```

Slashing definition: 

```k
    rule
    <k> unfold("slashed") => . ... </k>
    <g> slashed(VS, V)
        => slashed_dbl_vote(VS, V) or slashed_surround(VS, V)
    </g>

    rule
    <k> fold("slashed") => . ... </k>
    <g> slashed_dbl_vote(VS, V) or slashed_surround(VS, V) 
        => slashed(VS, V)
    </g>
```

```k
endmodule

```
