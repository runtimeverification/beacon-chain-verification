requires "dynamic-abstract-beacon-chain.k"

module LEMMAS-JAVA [kast]

imports K-REFLECTION

rule (I1 +Int I2) +Int I3 => I1 +Int (I2 +Int I3) requires notBool #isConcrete(I1) andBool #isConcrete(I2) andBool #isConcrete(I3)
rule (I1 +Int I2) -Int I3 => I1 +Int (I2 -Int I3) requires notBool #isConcrete(I1) andBool #isConcrete(I2) andBool #isConcrete(I3)
rule (I1 -Int I2) +Int I3 => I1 -Int (I2 -Int I3) requires notBool #isConcrete(I1) andBool #isConcrete(I2) andBool #isConcrete(I3)
rule (I1 -Int I2) -Int I3 => I1 -Int (I2 +Int I3) requires notBool #isConcrete(I1) andBool #isConcrete(I2) andBool #isConcrete(I3)

endmodule

module VERIFICATION

imports DYNAMIC-ABSTRACT-BEACON-CHAIN
imports LEMMAS-JAVA

syntax Tactic ::= case(Pred) // case analysis

rule case(xor2(C, _)) => . requires C [trusted]
rule case(xor2(_, C)) => . requires C [trusted]

rule case(xor3(C, _, _)) => . requires C [trusted]
rule case(xor3(_, C, _)) => . requires C [trusted]
rule case(xor3(_, _, C)) => . requires C [trusted]

rule case(xor4(C, _, _, _)) => . requires C [trusted]
rule case(xor4(_, C, _, _)) => . requires C [trusted]
rule case(xor4(_, _, C, _)) => . requires C [trusted]
rule case(xor4(_, _, _, C)) => . requires C [trusted]

rule case(xor5(C, _, _, _, _)) => . requires C [trusted]
rule case(xor5(_, C, _, _, _)) => . requires C [trusted]
rule case(xor5(_, _, C, _, _)) => . requires C [trusted]
rule case(xor5(_, _, _, C, _)) => . requires C [trusted]
rule case(xor5(_, _, _, _, C)) => . requires C [trusted]

syntax Pred ::= xor2(Bool, Bool)
              | xor3(Bool, Bool, Bool)
              | xor4(Bool, Bool, Bool, Bool)
              | xor5(Bool, Bool, Bool, Bool, Bool)

syntax Bool ::= bool(Pred) [function]
rule bool(xor2(C1, C2)) => C1 orBool C2
rule bool(xor3(C1, C2, C3)) => C1 orBool C2 orBool C3
rule bool(xor4(C1, C2, C3, C4)) => C1 orBool C2 orBool C3 orBool C4
rule bool(xor5(C1, C2, C3, C4, C5)) => C1 orBool C2 orBool C3 orBool C4 orBool C5

syntax Attestations ::= super(Attestations) [function, no-evaluators]
rule isJustifiable(B, super(As), Vs) => true
    requires isJustifiable(B, As, Vs)

syntax Pred ::= isValidState(Int, Int, Attestations, Map, Bool,
                             Int, Int, Attestations, Map, Bool,
                             Int) [function]
rule isValidState(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs2, Epoch2Justified,
                  Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1, Epoch1Justified,
                  LastJustifiedEpoch)
  => xor3(
                notBool isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs2)
        andBool notBool isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs1)
        andBool LastJustifiedEpoch <Int Epoch2
        andBool Epoch2Justified ==K false
        andBool Epoch1Justified ==K false
     ,
                        isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs2)
        andBool notBool isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs1)
        andBool LastJustifiedEpoch ==Int Epoch2
        andBool Epoch2Justified ==K true
        andBool Epoch1Justified ==K false
     ,
                        isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs1)
        andBool LastJustifiedEpoch ==Int Epoch1
        andBool Epoch1Justified ==K true
     )

/*


    ite(
        isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs2)
    ,
        Epoch2JustifiedBlock ==K some Epoch2BoundaryBlock
    ,
        Epoch2JustifiedBlock ==K none
    )

    ite(
        isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs1)
    ,
        Epoch1JustifiedBlock ==K some Epoch1BoundaryBlock
    ,
        Epoch1JustifiedBlock ==K none
    )

    xor3(
               LastJustifiedEpoch <Int Epoch2
       andBool Epoch2JustifiedBlock ==K none
       andBool Epoch1JustifiedBlock ==K none
    ,
               LastJustifiedEpoch ==Int Epoch2
       andBool LastJustifiedBlock ==Int Epoch2BoundaryBlock
       andBool Epoch2JustifiedBlock ==K some Epoch2BoundaryBlock
       andBool Epoch1JustifiedBlock ==K none
    ,
               LastJustifiedEpoch ==Int Epoch1
       andBool LastJustifiedBlock ==Int Epoch1BoundaryBlock
       andBool Epoch1JustifiedBlock ==K some Epoch1BoundaryBlock
    )

*/


endmodule
