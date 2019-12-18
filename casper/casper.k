module CASPER-SYNTAX

    imports INT

    syntax Hash ::= Int
    
    syntax Validator ::= #val ( id : Int )
    syntax Vote ::= #vote( val : Validator, src : Hash , trgt : Hash , srcH : Int , trgtH : Int )  [klabel(#vote), symbol]
 // ------------------------------------------------------------------------------------------------------------------------ 
    syntax Pred ::= BlockP
                  | ParentP
                  | AncestorP
                  | NthAncestorP
    syntax BlockP ::= Block( Hash )
 // ------------------------------------
    syntax ParentP ::= Hash "<~"  Hash
 // ----------------------------------
    syntax AncestorP ::= Hash "<~*" Hash
 // -----------------------------------
    syntax NthAncestorP ::= Hash "<~" "[" Int "]" Hash
 // --------------------------------------------------
endmodule
module CASPER

    imports CASPER-SYNTAX 

endmodule

