Block Hash
==========

Block hashes as integer identifiers. The Genesis block has the unique hash id `genesis`.

```k

module HASH

    imports INT

    syntax Hash ::= Int
    syntax Hash ::= "genesis"
    
endmodule

```
