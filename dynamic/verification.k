requires "dynamic-abstract-beacon-chain.k"

module VERIFICATION

imports DYNAMIC-ABSTRACT-BEACON-CHAIN

syntax KItem ::= case2(Bool, Bool)
// case analysis
rule case2(C, _) => . requires C [trusted]
rule case2(_, C) => . requires C [trusted]

syntax KItem ::= case3(Bool, Bool, Bool)
// case analysis
rule case3(C, _, _) => . requires C [trusted]
rule case3(_, C, _) => . requires C [trusted]
rule case3(_, _, C) => . requires C [trusted]

syntax Attestations ::= super(Attestations) [function]
rule isJustifiable(B, super(As), Vs) => true
    requires isJustifiable(B, As, Vs)

endmodule
