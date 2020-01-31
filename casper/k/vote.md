Votes
=====


```k

requires "proof-script.k"
requires "validator.k"

module VOTE 

    imports PROOF-SCRIPT
    imports VALIDATOR

```

A Casper FFG vote 

```k
    syntax Vote ::= #vote( val : Validator, src : Hash , trgt : Hash , srcH : Int , trgtH : Int )  [klabel(#vote), symbol]
 // ----------------------------------------------------------------------------------------------------------------------
```

Sets of votes

```k
    syntax FinVoteSet
```

Vote Set Predicates

```k
   syntax Pred ::= VSubsetP
                 | VMemberP
                 | VEmptyP

   syntax VSubsetP ::= FinVoteSet "<=" FinVoteSet
   
   syntax VMemberP ::= Vote "in" FinVoteSet
   
   syntax VEmptyP ::= "empty" FinVoteSet
```



```k
endmodule

```
