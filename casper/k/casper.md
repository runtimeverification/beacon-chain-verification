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
requires "hash_nth_ancestor_ext.k"
requires "validator.k"
requires "vote.k"
requires "slashing.k"
requires "justification.k"
requires "justification_ext.k"
requires "justification_epoch.k"
requires "justification_ext2.k"

module CASPER

    imports JUSTIFICATION-EXT2

endmodule
```
