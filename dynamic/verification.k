requires "dynamic-abstract-beacon-chain.k"

module LEMMAS-JAVA [kast]

imports K-REFLECTION

rule I +Int 0 => I
rule I -Int 0 => I

rule (I1 +Int I2) +Int I3 => I1 +Int (I2 +Int I3) requires notBool #isConcrete(I1) andBool #isConcrete(I2) andBool #isConcrete(I3)
rule (I1 +Int I2) -Int I3 => I1 +Int (I2 -Int I3) requires notBool #isConcrete(I1) andBool #isConcrete(I2) andBool #isConcrete(I3)
rule (I1 -Int I2) +Int I3 => I1 -Int (I2 -Int I3) requires notBool #isConcrete(I1) andBool #isConcrete(I2) andBool #isConcrete(I3)
rule (I1 -Int I2) -Int I3 => I1 -Int (I2 +Int I3) requires notBool #isConcrete(I1) andBool #isConcrete(I2) andBool #isConcrete(I3)

rule (I1 *Int I2) /Int I3 => I1 requires I2 ==Int I3 andBool I3 =/=Int 0

endmodule

module VERIFICATION

imports DYNAMIC-ABSTRACT-BEACON-CHAIN
imports LEMMAS-JAVA

// rule maxInt(I1, I2) => I1 requires I1 >=Int I2
// rule maxInt(I1, I2) => I2 requires I1 <Int I2

rule (V with slashed                      = _).exit_epoch => V.exit_epoch
rule (V with balance                      = _).exit_epoch => V.exit_epoch
rule (V with effective_balance            = _).exit_epoch => V.exit_epoch
rule (V with activation_eligibility_epoch = _).exit_epoch => V.exit_epoch
rule (V with activation_epoch             = _).exit_epoch => V.exit_epoch
rule (V with exit_epoch                   = I).exit_epoch => I
rule (V with withdrawable_epoch           = _).exit_epoch => V.exit_epoch

// for l-spec
rule countValidatorsToExit(v(VM [ VID <- V ]v, VIDs), E) => countValidatorsToExit(v(VM, VIDs), E) +Int 1
    requires V.exit_epoch =/=Int VM[VID]v.exit_epoch

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

/* TODO: fix rule automaton bug
rule case(xor6(C, _, _, _, _, _)) => . requires C [trusted]
rule case(xor6(_, C, _, _, _, _)) => . requires C [trusted]
rule case(xor6(_, _, C, _, _, _)) => . requires C [trusted]
rule case(xor6(_, _, _, C, _, _)) => . requires C [trusted]
rule case(xor6(_, _, _, _, C, _)) => . requires C [trusted]
rule case(xor6(_, _, _, _, _, C)) => . requires C [trusted]
*/

syntax Pred ::= xor2(Bool, Bool)
              | xor3(Bool, Bool, Bool)
              | xor4(Bool, Bool, Bool, Bool)
              | xor5(Bool, Bool, Bool, Bool, Bool)
              | xor6(Bool, Bool, Bool, Bool, Bool, Bool)

syntax Bool ::= bool(Pred) [function, functional]
rule bool(xor2(C1, C2)) => C1 orBool C2
rule bool(xor3(C1, C2, C3)) => C1 orBool C2 orBool C3
rule bool(xor4(C1, C2, C3, C4)) => C1 orBool C2 orBool C3 orBool C4
rule bool(xor5(C1, C2, C3, C4, C5)) => C1 orBool C2 orBool C3 orBool C4 orBool C5
rule bool(xor6(C1, C2, C3, C4, C5, C6)) => C1 orBool C2 orBool C3 orBool C4 orBool C5 orBool C6

syntax Bool ::= implies(Bool, Bool) [function, functional]
rule implies(A, B) => notBool A orBool B

syntax Bool ::= iff(Bool, Bool) [function, functional]
rule iff(A, B) => implies(A, B) andBool implies(B, A)

syntax Attestations ::= super(Attestations) [function, functional, no-evaluators]
rule isJustifiable(E, B, super(As), Vs) => true
    requires isJustifiable(E, B, As, Vs)
    [simplification]

syntax Pred ::= isValidState(Int, Int, Attestations, Validators, Bool,
                             Int, Int, Attestations, Validators, Bool,
                             Int) [function, functional]
rule isValidState(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs2, Epoch2Justified,
                  Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1, Epoch1Justified,
                  LastJustifiedEpoch)
  => xor3(
                notBool isJustifiable(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs2)
        andBool notBool isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1)
        andBool LastJustifiedEpoch <Int Epoch2
        andBool Epoch2Justified ==K false
        andBool Epoch1Justified ==K false
     ,
                        isJustifiable(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs2)
        andBool notBool isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1)
        andBool LastJustifiedEpoch ==Int Epoch2
        andBool Epoch2Justified ==K true
        andBool Epoch1Justified ==K false
     ,
                        isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1)
        andBool LastJustifiedEpoch ==Int Epoch1
        andBool Epoch1Justified ==K true
     )


syntax Bool ::= isGoodState(Int, Int, Attestations, Validators, Bool,
                            Int, Int, Attestations, Validators, Bool,
                            Int) [function, functional]
rule isGoodState(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs2, Epoch2Justified,
                 Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1, Epoch1Justified,
                 LastJustifiedEpoch)
  => // justification of e-2 and e-1
             iff(Epoch2Justified ==K true, isJustifiable(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs2))
     andBool iff(Epoch1Justified ==K true, isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1))
     // last justified epoch
     andBool implies(LastJustifiedEpoch  <Int Epoch2, Epoch2Justified ==K false andBool Epoch1Justified ==K false)
     andBool implies(LastJustifiedEpoch ==Int Epoch2, Epoch2Justified ==K true  andBool Epoch1Justified ==K false)
     andBool implies(LastJustifiedEpoch ==Int Epoch1,                                   Epoch1Justified ==K true )
     andBool         LastJustifiedEpoch <=Int Epoch1

syntax Bool ::= isCorrectLastJustifiedEpoch(Int, Int, Bool, Bool) [function, functional]
rule isCorrectLastJustifiedEpoch(LastJustifiedEpoch, Epoch, Epoch1Justified, Epoch2Justified)
  =>         implies(LastJustifiedEpoch  <Int Epoch -Int 2, Epoch2Justified ==K false andBool Epoch1Justified ==K false)
     andBool implies(LastJustifiedEpoch ==Int Epoch -Int 2, Epoch2Justified ==K true  andBool Epoch1Justified ==K false)
     andBool implies(LastJustifiedEpoch ==Int Epoch -Int 1,                                   Epoch1Justified ==K true)
     andBool         LastJustifiedEpoch <=Int Epoch -Int 1

syntax Bool ::= isCorrectLastFinalizedEpoch(Int, Int, Bool, Bool) [function, functional]
              | isCorrectLastFinalizedEpoch(Int, Int, Bool, Bool, Bool) [function, functional]
rule isCorrectLastFinalizedEpoch(LastFinalizedEpoch, Epoch, Epoch2Finalized, Epoch3Finalized)
  =>         implies(LastFinalizedEpoch  <Int Epoch -Int 3, Epoch3Finalized ==K false andBool Epoch2Finalized ==K false)
     andBool implies(LastFinalizedEpoch ==Int Epoch -Int 3, Epoch3Finalized ==K true  andBool Epoch2Finalized ==K false)
     andBool implies(LastFinalizedEpoch ==Int Epoch -Int 2,                                   Epoch2Finalized ==K true)
     andBool         LastFinalizedEpoch <=Int Epoch -Int 2
rule isCorrectLastFinalizedEpoch(LastFinalizedEpoch, Epoch, Epoch2Finalized, Epoch3Finalized, Epoch4Finalized)
  =>         implies(LastFinalizedEpoch  <Int Epoch -Int 4, Epoch4Finalized ==K false andBool Epoch3Finalized ==K false andBool Epoch2Finalized ==K false)
     andBool implies(LastFinalizedEpoch ==Int Epoch -Int 4, Epoch4Finalized ==K true  andBool Epoch3Finalized ==K false andBool Epoch2Finalized ==K false)
     andBool implies(LastFinalizedEpoch ==Int Epoch -Int 3,                                   Epoch3Finalized ==K true  andBool Epoch2Finalized ==K false)
     andBool implies(LastFinalizedEpoch ==Int Epoch -Int 2,                                                                     Epoch2Finalized ==K true)
     andBool         LastFinalizedEpoch <=Int Epoch -Int 2

endmodule
