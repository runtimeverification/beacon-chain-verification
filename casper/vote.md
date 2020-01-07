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
 // ------------------------------------------------------------------------------------------------------------------------ 
```

```k
endmodule

```
