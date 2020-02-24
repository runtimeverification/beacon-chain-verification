requires "dynamic-abstract-beacon-chain.k"

module VERIFICATION

imports DYNAMIC-ABSTRACT-BEACON-CHAIN

syntax Tactic ::= case2(Bool, Bool)
// case analysis
rule case2(C, _) => . requires C [trusted]
rule case2(_, C) => . requires C [trusted]

syntax Tactic ::= case3(Bool, Bool, Bool)
// case analysis
rule case3(C, _, _) => . requires C [trusted]
rule case3(_, C, _) => . requires C [trusted]
rule case3(_, _, C) => . requires C [trusted]

syntax Attestations ::= super(Attestations) [function]
rule isJustifiable(B, super(As), Vs) => true
    requires isJustifiable(B, As, Vs)


syntax Bool ::= isValidState(Int, Int, Attestations, Map, Option,
                             Int, Int, Attestations, Map, Option,
                             Int, Int) [function]
rule isValidState(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs2, Epoch2JustifiedBlock,
                  Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1, Epoch1JustifiedBlock,
                  LastJustifiedEpoch, LastJustifiedBlock)
  => (
      (
                notBool isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs2)
        andBool notBool isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs1)
        andBool LastJustifiedEpoch <Int Epoch2
        andBool Epoch2JustifiedBlock ==K none
        andBool Epoch1JustifiedBlock ==K none
      ) orBool (
                        isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs2)
        andBool notBool isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs1)
        andBool LastJustifiedEpoch ==Int Epoch2
        andBool LastJustifiedBlock ==Int Epoch2BoundaryBlock
        andBool Epoch2JustifiedBlock ==K some Epoch2BoundaryBlock
        andBool Epoch1JustifiedBlock ==K none
      ) orBool (
                        isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs1)
        andBool LastJustifiedEpoch ==Int Epoch1
        andBool LastJustifiedBlock ==Int Epoch1BoundaryBlock
        andBool Epoch1JustifiedBlock ==K some Epoch1BoundaryBlock
      )
     )

syntax Tactic ::= split2(Bool) [function]
                | split3(Bool) [function]
rule split2(C1 orBool C2) => case2(C1, C2)
rule split3(C1 orBool C2 orBool C3) => case3(C1, C2, C3)

endmodule
