Casper FFG Model
================

A model of Casper FFG based on previsouly developed models in Coq [here](https://github.com/runtimeverification/casper-proofs) 
and updated to accoommodate new justification and finalization rules. 

```k

requires "proof-script.k"
requires "hash.k"
requires "hash_parent.k"
requires "hash_ancestor.k"
requires "hash_ancestor_ext.k"
requires "hash_nth_ancestor.k"
requires "state.k"

module CASPER

    imports HASH-NTH-ANCESTOR
    imports STATE

endmodule
```
