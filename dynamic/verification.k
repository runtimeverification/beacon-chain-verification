require "dynamic-abstract-beacon-chain.k"
require "substitution.k"

module LEMMAS-JAVA [kast]

imports K-REFLECTION

rule I +Int 0 => I
rule I -Int 0 => I

rule (I1 +Int I2) +Int I3 => I1 +Int (I2 +Int I3) requires notBool #isConcrete(I1) andBool #isConcrete(I2) andBool #isConcrete(I3)
rule (I1 +Int I2) -Int I3 => I1 +Int (I2 -Int I3) requires notBool #isConcrete(I1) andBool #isConcrete(I2) andBool #isConcrete(I3)
rule (I1 -Int I2) +Int I3 => I1 -Int (I2 -Int I3) requires notBool #isConcrete(I1) andBool #isConcrete(I2) andBool #isConcrete(I3)
rule (I1 -Int I2) -Int I3 => I1 -Int (I2 +Int I3) requires notBool #isConcrete(I1) andBool #isConcrete(I2) andBool #isConcrete(I3)

rule (I1 *Int I2) /Int I3 => I1 requires I2 ==Int I3 andBool I3 =/=Int 0

rule I >=Int I => true
rule I <=Int I => true

rule I >Int I => false
rule I <Int I => false

endmodule

module VERIFICATION

imports DYNAMIC-ABSTRACT-BEACON-CHAIN
imports LEMMAS-JAVA
imports SUBSTITUTION

syntax KVar ::= "x" [token]

syntax Int ::= KVar
syntax Bool ::= forall(KVar, IntList, Bool) [binder, function]
rule forall(X, V Vs, E) => E[V / X] andBool forall(X, Vs, E)
rule forall(_, .IntList, _) => true

syntax VoluntaryExit ::= KVar
syntax Bool ::= forallE(KVar, VoluntaryExits, Bool) [binder, function]
rule forallE(X, V Vs, E) => E[V / X] andBool forallE(X, Vs, E)
rule forallE(_, .VoluntaryExits, _) => true

syntax Validator ::= KVar
syntax Bool ::= forallV(KVar, ValidatorList, Bool) [binder, function]
rule forallV(X, V Vs, E) => E[V / X] andBool forallV(X, Vs, E)
rule forallV(_, .ValidatorList, _) => true

/*
syntax Int ::= KVar
syntax Int ::= lambda(KVar, Int) [binder, function]

syntax Bool ::= forall(KVar, IntList, Bool) [binder, function]
rule forall(X, V Vs, E) => E[V / X] andBool forall(X, Vs, E)
rule forall(_, .IntList, _) => true

syntax ValidatorMap ::= ValidatorMap "[" IntList ":=" Validator "]v" [function]
rule M [ (K Ks) := lambda(X, V) ]v => ( M [ K <- V[K / X] ]v ) [ Ks := lambda(X, V) ]v
rule M [ .IntList := _ ]v => M
*/

// rule maxInt(I1, I2) => I1 requires I1 >=Int I2
// rule maxInt(I1, I2) => I2 requires I1 <Int I2

rule (V with slashed                      = _).exit_epoch => V.exit_epoch
rule (V with balance                      = _).exit_epoch => V.exit_epoch
rule (V with effective_balance            = _).exit_epoch => V.exit_epoch
rule (V with activation_eligibility_epoch = _).exit_epoch => V.exit_epoch
rule (V with activation_epoch             = _).exit_epoch => V.exit_epoch
rule (V with exit_epoch                   = I).exit_epoch => I
rule (V with withdrawable_epoch           = _).exit_epoch => V.exit_epoch

rule (V with slashed                      = _).activation_epoch => V.activation_epoch
rule (V with balance                      = _).activation_epoch => V.activation_epoch
rule (V with effective_balance            = _).activation_epoch => V.activation_epoch
rule (V with activation_eligibility_epoch = _).activation_epoch => V.activation_epoch
rule (V with activation_epoch             = I).activation_epoch => I
rule (V with exit_epoch                   = _).activation_epoch => V.activation_epoch
rule (V with withdrawable_epoch           = _).activation_epoch => V.activation_epoch

rule (V with slashed                      = _).balance => V.balance
rule (V with balance                      = I).balance => I
rule (V with effective_balance            = _).balance => V.balance
rule (V with activation_eligibility_epoch = _).balance => V.balance
rule (V with activation_epoch             = _).balance => V.balance
rule (V with exit_epoch                   = _).balance => V.balance
rule (V with withdrawable_epoch           = _).balance => V.balance

rule (V with balance                      = _) with balance = I => V with balance = I
rule (V with effective_balance            = J) with balance = I => V with balance = I with effective_balance            = J
rule (V with activation_eligibility_epoch = J) with balance = I => V with balance = I with activation_eligibility_epoch = J
rule (V with activation_epoch             = J) with balance = I => V with balance = I with activation_epoch             = J
rule (V with exit_epoch                   = J) with balance = I => V with balance = I with exit_epoch                   = J
rule (V with withdrawable_epoch           = J) with balance = I => V with balance = I with withdrawable_epoch           = J

// for l-spec
rule countValidatorsToExit(v(VM [ VID <- V ]v, VIDs), E) => countValidatorsToExit(v(VM, VIDs), E) +Int 1
    requires V.exit_epoch =/=Int VM[VID]v.exit_epoch
     andBool V.exit_epoch ==Int E
     andBool VID in VIDs

syntax Bool ::= isValidVoluntaryExits(VoluntaryExits, ValidatorMap, Int, IntList) [function]
rule isValidVoluntaryExits(E Es, VM, Epoch, VIDs) => isValidVoluntaryExit(E, VM[E.validator]v, Epoch) andBool isValidVoluntaryExits(Es, VM, Epoch, VIDs)
                                                     andBool distinctVoluntaryExits(E Es)
                                                     andBool E.validator in VIDs
rule isValidVoluntaryExits(.VoluntaryExits, _, _, _) => true

rule isValidVoluntaryExits(Es, VM [ E.validator <- _ ]v, Epoch, VIDs) => true
    requires isValidVoluntaryExits(Es, VM, Epoch, VIDs)
     andBool distinctVoluntaryExits(E Es)

syntax Bool ::= distinctVoluntaryExits(VoluntaryExits) [function]
// TODO: implement
// rule distinctVoluntaryExits(Es) => distinct(Es.validator)

syntax Bool ::= distinct(IntList) [function]
// TODO: implement

syntax Validators ::= storeValidatorExits(Validators, VoluntaryExits, Int) [function]
rule storeValidatorExits(v(VM, VIDs), E Es, Epoch)
  => storeValidatorExits(v(VM [ E.validator <- VM[E.validator]v with exit_epoch         = computeExitEpoch(v(VM, VIDs), Epoch)
                                                                with withdrawable_epoch = computeExitEpoch(v(VM, VIDs), Epoch) +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY ]v, VIDs), Es, Epoch)
rule storeValidatorExits(Vs, .VoluntaryExits, _) => Vs

syntax ValidatorMap ::= updateValidatorExits(ValidatorMap, VoluntaryExits, IntList, Int) [function]
rule updateValidatorExits(VM, E Es, VIDs, Epoch) => updateValidatorExits(VM [ E.validator <- updateExitEpoch(VM[E.validator]v, v(VM,VIDs), Epoch) ]v, Es, VIDs, Epoch)
rule updateValidatorExits(VM, .VoluntaryExits, _, _) => VM

rule countValidatorsToExit(v(updateValidatorExits(VM [ VE.validator <- V ]v, VEs, VIDs, Epoch), VIDs), E) <=Int ChurnLimit => true
     requires countValidatorsToExit(v(VM [ VE.validator <- V ]v, VIDs), E) <=Int ChurnLimit
      andBool forallE(x, VEs, countValidatorsToExit(v(updateValidatorExits(VM [ VE.validator <- V ]v, VEs, VIDs, Epoch), VIDs), updateValidatorExits(VM [ VE.validator <- V ]v, VEs, VIDs, Epoch)[x.validator]v.exit_epoch) <=Int ChurnLimit)
      andBool distinctVoluntaryExits(VE VEs)

rule activeValidators(v(updateValidatorExits(VM, VEs, _, _), VIDs), Epoch) => activeValidators(v(VM, VIDs), Epoch) // TODO: proof
     requires isValidVoluntaryExits(VEs, VM, Epoch, VIDs)
rule activeValidators(v(VM [ VID <- V ]v, VIDs), Epoch) => activeValidators(v(VM, VIDs), Epoch)
     requires V.exit_epoch >Int Epoch
      andBool VM[VID]v.exit_epoch ==Int FAR_FUTURE_EPOCH
      andBool VM[VID]v.activation_epoch ==Int V.activation_epoch

rule updateValidatorExits(VM, Es, _, _) [ E.validator ]v => VM [ E.validator ]v
     requires distinctVoluntaryExits(E Es)

rule VM[VID]v.id => VID

syntax Validator ::= updateExitEpoch(Validator, Validators, Int) [function]
rule [updateExitEpoch]:
     updateExitEpoch(V, Vs, Epoch) => V with exit_epoch         = computeExitEpoch(Vs, Epoch)
                                        with withdrawable_epoch = computeExitEpoch(Vs, Epoch) +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY

rule sizeE(_) >=Int 0 => true [smt-lemma]

rule countValidatorsToExit(Vs, E) => 0
     requires maxExitEpoch(Vs) <Int E andBool E <Int FAR_FUTURE_EPOCH
     [smt-lemma]

rule maxExitEpoch(v(VM [ VID <- V ]v, VIDs)) => maxInt(maxExitEpoch(v(VM, VIDs)), V.exit_epoch)
     requires V.exit_epoch =/=Int FAR_FUTURE_EPOCH
      andBool VID in VIDs

// for m-spec
/*
rule sizeV(take(N, _)) <=Int M => true requires N >=Int 0 andBool N <=Int M
*/
rule sizeV(take(N, _)) <=Int N => true requires N >=Int 0 [smt-lemma]
rule sizeV(_:ValidatorList) >=Int 0 => true [smt-lemma]

rule subset(take(_, S1), S2) => true requires subset(S1, S2)
rule subset(sort(S1), S2) => true requires subset(S1, S2)
rule subset(S, S) => true

syntax ValidatorMap ::= updateActivations(ValidatorMap, ValidatorList, Int) [function]
rule updateActivations(VM, V Vs, Epoch) => updateActivations(VM [ V.id <- V with activation_epoch = delayedActivationExitEpoch(Epoch) ]v, Vs, Epoch)
rule updateActivations(VM, .ValidatorList, _) => VM

rule updateActivations(VM, Vs, _) [ V.id ]v => VM [ V.id ]v
     requires distinctValidators(V Vs)

syntax Bool ::= distinctValidators(ValidatorList) [function]
// TODO: implement
// rule distinctValidators(Vs) => distinct(Vs.id)

syntax Bool ::= isValidValidatorsToActivate(ValidatorList, Validators, Int) [function]
rule isValidValidatorsToActivate(V Vs, v(VM, VIDs), FinalizedEpoch) => isValidValidatorToActivate(V, FinalizedEpoch) andBool isValidValidatorsToActivate(Vs, v(VM, VIDs), FinalizedEpoch)
                                                                       andBool distinctValidators(V Vs)
                                                                       andBool V.id in VIDs
                                                                       andBool VM[V.id]v ==K V
rule isValidValidatorsToActivate(.ValidatorList, _, _) => true

rule isValidValidatorsToActivate(Vs, v(VM [ V.id <- _ ]v, VIDs), FinalizedEpoch) => true
    requires isValidValidatorsToActivate(Vs, v(VM, VIDs), FinalizedEpoch)
     andBool distinctValidators(V Vs)

syntax Int ::= countValidatorsToActivate(Validators, Int) [function, smtlib(countValidatorsToActivate)]
rule countValidatorsToActivate(v(VM, VID VIDs), ActivationEpoch)
  => #if VM[VID]v.activation_epoch ==Int ActivationEpoch #then 1 #else 0 #fi +Int countValidatorsToActivate(v(VM, VIDs), ActivationEpoch)
rule countValidatorsToActivate(v(_, .IntList), _) => 0

rule countValidatorsToActivate(v(VM [ VID <- V ]v, VIDs), E) => countValidatorsToActivate(v(VM, VIDs), E) +Int 1
    requires V.activation_epoch =/=Int VM[VID]v.activation_epoch
     andBool V.activation_epoch ==Int E
     andBool VID in VIDs

rule activeValidators(v(VM [ VID <- V ]v, VIDs), Epoch) => activeValidators(v(VM, VIDs), Epoch)
     requires V.activation_epoch >Int Epoch
      andBool VM[VID]v.activation_epoch ==Int FAR_FUTURE_EPOCH
      andBool VM[VID]v.exit_epoch ==Int V.exit_epoch

rule isValidValidatorsToActivate(take(_, sort(activationQueue(Vs, FinalizedEpoch))), Vs, FinalizedEpoch) => true
// TODO: proof

// for n-spec

/*
rule X1 +Int Y1 <=Int X2 +Int Y2 => true requires X1 <=Int X2 andBool Y1 <=Int Y2
rule X1 +Int Y1 >=Int X2 +Int Y2 => true requires X1 >=Int X2 andBool Y1 >=Int Y2

rule X /Int Y <=Int Z => true requires X <=Int Z
                               andBool X >=Int 0 andBool Y >Int 0 andBool Z >=Int 0
rule X *Int Y /Int Z <=Int X => true requires Y <=Int Z
                                      andBool X >=Int 0 andBool Y >=Int 0 andBool Z >Int 0
rule X /Int N <=Int Y /Int N => true requires X <=Int Y
                                      andBool X >=Int 0 andBool Y >=Int 0 andBool N >Int 0
rule X /Int Y >Int 0 => true requires X >=Int Y
                              andBool X >Int 0 andBool Y >Int 0
*/

rule lift(X) >=Int EFFECTIVE_BALANCE_INCREMENT => true [smt-lemma]

rule getMatchingReward(B, A, T) <=Int B => true requires B >=Int 0 andBool A >=Int 0 andBool T >=Int EFFECTIVE_BALANCE_INCREMENT andBool A <=Int T [smt-lemma]
rule getMatchingReward(B, A, T) >=Int 0 => true requires B >=Int 0 andBool A >=Int 0 andBool T >=Int EFFECTIVE_BALANCE_INCREMENT                   [smt-lemma]

rule getInclusionReward(B, D) <=Int B => true requires B >=Int 0 andBool D >=Int 1 [smt-lemma]
rule getInclusionReward(B, D) >=Int 0 => true requires B >=Int 0 andBool D >=Int 1 [smt-lemma]

rule getInactivityPenalty(B, D) >=Int 0 => true requires B >=Int 0 andBool D >=Int 0 [smt-lemma]

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
