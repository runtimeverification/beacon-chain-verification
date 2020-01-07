Model State
===========


```k

requires "proof-script.k"
requires "hash.k"

module STATE

    imports HASH
```

A Casper validator
```k
    syntax Validator ::= #val ( id : Int ) [klabel(#val), symbol]
 // -------------------------------------------------------------  
```

A Casper FFG vote 

```k
    syntax Vote ::= #vote( val : Validator, src : Hash , trgt : Hash , srcH : Int , trgtH : Int )  [klabel(#vote), symbol]
 // ------------------------------------------------------------------------------------------------------------------------ 
```

```k
endmodule

```
