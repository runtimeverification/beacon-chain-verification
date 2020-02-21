requires "dynamic-abstract-beacon-chain.k"

module VERIFICATION

imports DYNAMIC-ABSTRACT-BEACON-CHAIN

syntax KItem ::= case2(Bool, Bool)
// case analysis
rule case2(C, _) => . requires C [trusted]
rule case2(_, C) => . requires C [trusted]

endmodule
