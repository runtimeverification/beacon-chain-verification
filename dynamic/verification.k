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

module COMMON

imports DYNAMIC-ABSTRACT-BEACON-CHAIN
imports SUBSTITUTION

// FOL

syntax Bool ::= implies(Bool, Bool) [function, functional]
rule implies(A, B) => notBool A orBool B [macro]

syntax Bool ::= iff(Bool, Bool) [function, functional]
rule iff(A, B) => implies(A, B) andBool implies(B, A) [macro]

// Tactics

syntax Tactic ::= "begin"
rule begin => .

syntax Tactic ::= case(Pred) // case analysis

syntax Pred ::= xor2(Bool, Bool)
              | xor3(Bool, Bool, Bool)

rule case(xor2(C, _)) => . requires C [trusted]
rule case(xor2(_, C)) => . requires C [trusted]

rule case(xor3(C, _, _)) => . requires C [trusted]
rule case(xor3(_, C, _)) => . requires C [trusted]
rule case(xor3(_, _, C)) => . requires C [trusted]

// Builtin Map

rule ( K1 |-> V M:Map ) [ K2 ] => V        requires K1  ==Int K2
rule ( K1 |-> _ M:Map ) [ K2 ] => M [ K2 ] requires K1 =/=Int K2

// Quantified formula

syntax KVar ::= "x" [token]

syntax Int ::= KVar
syntax Bool ::= forall(KVar, IntList, Bool) [binder, function, smtlib((forall ((#1 Int)) (=> (inI #1 #2) #3)))]
rule forall(X, V Vs, E) => E[V / X] andBool forall(X, Vs, E)
rule forall(_, .IntList, _) => true
rule forall(_, _, true) => true
rule forall(X, S, X in S) => true

syntax Slashing ::= KVar
syntax Bool ::= forallS(KVar, Slashings, Bool) [binder, function, smtlib((forall ((#1 Slashing)) (=> (inS #1 #2) #3)))]
rule forallS(X, V Vs, E) => E[V / X] andBool forallS(X, Vs, E)
rule forallS(_, .Slashings, _) => true
rule forallS(_, _, true) => true

syntax VoluntaryExit ::= KVar
syntax Bool ::= forallE(KVar, VoluntaryExits, Bool) [binder, function, smtlib((forall ((#1 VoluntaryExit)) (=> (inE #1 #2) #3)))]
rule forallE(X, V Vs, E) => E[V / X] andBool forallE(X, Vs, E)
rule forallE(_, .VoluntaryExits, _) => true
rule forallE(_, _, true) => true

// Projections

syntax IntList ::= getValidatorsA(Attestations) [function, smtlib(getValidatorsA)]
rule getValidatorsA(A As) => A.attester getValidatorsA(As)
rule getValidatorsA(.Attestations) => .IntList

syntax IntList ::= getValidatorsD(Deposits) [function, smtlib(getValidatorsD)]
rule getValidatorsD(D Ds) => D.sender getValidatorsD(Ds)
rule getValidatorsD(.Deposits) => .IntList

syntax IntList ::= getValidatorsS(Slashings) [function, smtlib(getValidatorsS)]
rule getValidatorsS(S Ss) => S.attestation_1.attester getValidatorsS(Ss)
rule getValidatorsS(.Slashings) => .IntList

syntax IntList ::= getValidatorsE(VoluntaryExits) [function, smtlib(getValidatorsE)]
rule getValidatorsE(E Es) => E.validator getValidatorsE(Es)
rule getValidatorsE(.VoluntaryExits) => .IntList

// IntList

syntax IntList ::= rev(IntList) [function, smtlib(revI)]

rule rev(.IntList) => .IntList

rule forall(X, rev(V Vs), E) => E[V / X] andBool forall(X, rev(Vs), E)

rule iff(X in rev(L), X in L) => true [concrete, smt-lemma]

syntax IntList ::= IntList "++" IntList [function, smtlib(concatI)]

rule L ++ .IntList => L
rule .IntList ++ L => L

rule rev(X Ys) ++ Xs => rev(Ys) ++ X Xs

syntax Bool ::= subset(IntList, IntList) [function, klabel(subsetI), smtlib(subsetI)] // subset in set-like view

rule implies(X in Xs1, X in Xs2) => true requires subset(Xs1, Xs2) [concrete, smt-lemma]

syntax Bool ::= distinct(IntList) [function, smtlib(distinctI)]

rule implies(distinct(L Ls), distinct(Ls)) => true [concrete, smt-lemma]

syntax Bool ::= disjoint(IntList, IntList) [function, smtlib(disjointI)]
              | disjoint1(IntList, Int)    [function, smtlib(disjointI1)]

rule disjoint(Ls, R Rs) => disjoint1(Ls, R) andBool disjoint(Ls, Rs)
rule disjoint(.IntList, _) => true
rule disjoint(_, .IntList) => true

rule implies(disjoint(L1, L2) andBool X in L1, notBool X in L2) => true [concrete, smt-lemma]
rule implies(disjoint(L1, L2) andBool X in L2, notBool X in L1) => true [concrete, smt-lemma]

rule implies(J in Js andBool disjoint1(Js, I), I =/=K J) => true [concrete, smt-lemma]

rule disjoint1(Is, I) => true requires distinct(I Is) [concrete, smt-lemma]

rule disjoint(R Ls, Rs) => true requires distinct(R Rs) andBool disjoint(Ls, Rs)

// Attestations

syntax Attestations ::= revA(Attestations) [function, smtlib(revA)]

rule revA(.Attestations) => .Attestations

syntax Attestations ::= Attestations "++A" Attestations [function, klabel(concatA), smtlib(concatA)]

rule L ++A .Attestations => L
rule .Attestations ++A L => L

rule (X Xs) ++A Ys => X (Xs ++A Ys)
rule revA(X Ys) ++A Xs => revA(Ys) ++A (X Xs)

syntax Bool ::= subsetA(Attestations, Attestations) [function, functional, smtlib(subsetA)] // subset in set-like view

endmodule

module VERIFICATION

imports DYNAMIC-ABSTRACT-BEACON-CHAIN
imports LEMMAS-JAVA
imports COMMON
imports SUBSTITUTION

// for processVoluntaryExits

rule countValidatorsToExit(VIDs, EM [ VID <- E ]i, Exit)
  => countValidatorsToExit(VIDs, EM,               Exit) +Int 1
    requires E =/=Int EM[VID]i
     andBool E ==Int Exit
     andBool VID in VIDs

rule activeValidators(VIDs, AM, EM [ VID <- E ]i, Epoch)
  => activeValidators(VIDs, AM, EM              , Epoch)
     requires E >Int Epoch
      andBool EM[VID]i ==Int FAR_FUTURE_EPOCH

rule countValidatorsToExit(VIDs, EM, E) => 0
     requires maxExitEpoch(VIDs, EM) <Int E andBool E <Int FAR_FUTURE_EPOCH
     [smt-lemma]

rule maxExitEpoch(VIDs, EM [ VID <- E ]i) => maxInt(maxExitEpoch(VIDs, EM), E)
     requires E =/=Int FAR_FUTURE_EPOCH
      andBool VID in VIDs

rule forall(X, rev(L), countValidatorsToExit(VIDs, EM, (M [ Y <- _ ]i)[X]i) <=Int E)
  => forall(X, rev(L), countValidatorsToExit(VIDs, EM,  M             [X]i) <=Int E)
     requires disjoint1(L, Y)

// for processValidatorActivation

/*
rule sizeI(take(N, _)) <=Int M => true requires N >=Int 0 andBool N <=Int M
*/
rule sizeI(take(N, _)) <=Int N => true requires N >=Int 0 [smt-lemma]
rule sizeI(_) >=Int 0 => true [smt-lemma]

rule subsetI(take(_, S1), S2) => true requires subsetI(S1, S2)
rule subsetI(sortByActivationEligibility(S1), S2) => true requires subsetI(S1, S2)
rule subsetI(S, S) => true

syntax Int ::= countValidatorsToActivate(IntList, IMap, Int) [function, smtlib(countValidatorsToActivate)]
rule countValidatorsToActivate(VID VIDs, AM, ActivationEpoch)
  => #if AM[VID]i ==Int ActivationEpoch #then 1 #else 0 #fi +Int countValidatorsToActivate(VIDs, AM, ActivationEpoch)
rule countValidatorsToActivate(.IntList, _, _) => 0

rule countValidatorsToActivate(VIDs, AM [ VID <- A ]i, E)
  => countValidatorsToActivate(VIDs, AM              , E) +Int 1
    requires A =/=Int AM[VID]i
     andBool A ==Int E
     andBool VID in VIDs

rule activeValidators(VIDs, AM [ VID <- E ]i, EM, Epoch)
  => activeValidators(VIDs, AM              , EM, Epoch)
     requires E >Int Epoch
      andBool AM[VID]i ==Int FAR_FUTURE_EPOCH

rule distinct(activationQueue(VIDs, _, _, _)) => true
     requires distinct(VIDs)

rule forall(X, activationQueue(VIDs, _, _, _), X in VIDs) => true

rule forall(X, activationQueue(VIDs, AEM, AM, FinalizedEpoch), E) => true
     requires E ==K isValidValidatorToActivate(X, AEM, AM, FinalizedEpoch)

rule distinct(take(_, sortByActivationEligibility(L))) => true
     requires distinct(L)

rule forall(X, take(_, sortByActivationEligibility(L)), E) => true
     requires forall(X, L, E)

// for processRewardsPenalties

rule lift(X) >=Int EFFECTIVE_BALANCE_INCREMENT => true [smt-lemma]

rule getBaseReward(B, T) <=Int B => true requires B >=Int 0 andBool T >=Int 256 [smt-lemma]
rule getBaseReward(B, T) >=Int 0 => true requires B >=Int 0 andBool T >=Int 1   [smt-lemma]

rule getMatchingReward(B, A, T) <=Int B => true requires B >=Int 0 andBool A >=Int 0 andBool T >=Int EFFECTIVE_BALANCE_INCREMENT andBool A <=Int T [smt-lemma]
rule getMatchingReward(B, A, T) >=Int 0 => true requires B >=Int 0 andBool A >=Int 0 andBool T >=Int EFFECTIVE_BALANCE_INCREMENT                   [smt-lemma]

rule getInclusionReward(B, D) <=Int B => true requires B >=Int 0 andBool D >=Int 1 [smt-lemma]
rule getInclusionReward(B, D) >=Int 0 => true requires B >=Int 0 andBool D >=Int 1 [smt-lemma]

rule getInactivityPenalty(B, D) >=Int 0 => true requires B >=Int 0 andBool D >=Int 0 [smt-lemma]

rule forall(X, rev(L), (M [ Y <- _ ]i)[X]i <=Int E)
  => forall(X, rev(L),  M             [X]i <=Int E)
     requires disjoint1(L, Y)

rule forall(X, rev(L), (M [ Y <- _ ]i)[X]i  <Int E)
  => forall(X, rev(L),  M             [X]i  <Int E)
     requires disjoint1(L, Y)

rule forall(X, rev(L), (M [ Y <- _ ]i)[X]i >=Int E)
  => forall(X, rev(L),  M             [X]i >=Int E)
     requires disjoint1(L, Y)

rule forall(X, Ls, (M [ L <- _ ]i)[X]i ==K E)
  => forall(X, Ls,  M             [X]i ==K E)
     requires distinct(L Ls)

rule lift(totalBalance(M, L1)) <=Int lift(totalBalance(M, L2)) => true
     requires subset(L1, L2)

rule subset(getUniqueValidators(As), activeValidators(VIDs, AM, EM, Epoch)) => true
     requires isValidAttestations(As, VIDs, AM, EM, Epoch)

// the attester of each attestation is in the list of validators, and active in the given epoch
syntax Bool ::= isValidAttestations(Attestations, IntList, IMap, IMap, Int) [function, smtlib(isValidAttestations)]
// TODO: rule isValidAttestations(As, VIDs, AM, EM, Epoch) => forall(x, As, x.attester in VIDs andBool isActiveValidator(x.attester, AM, EM, Epoch))

rule isValidAttestations(filterNotSlashed(_, As), VIDs, AM, EM, Epoch) => true requires isValidAttestations(As, VIDs, AM, EM, Epoch)
rule isValidAttestations(filterByTarget(_,   As), VIDs, AM, EM, Epoch) => true requires isValidAttestations(As, VIDs, AM, EM, Epoch)
rule isValidAttestations(filterByHead(_,     As), VIDs, AM, EM, Epoch) => true requires isValidAttestations(As, VIDs, AM, EM, Epoch)

// for updateActivationEligibilities

rule forall(X, rev(L), (M [ Y <- _ ]i)[X]i ==K E)
  => forall(X, rev(L),  M             [X]i ==K E)
     requires disjoint1(L, Y)

rule forall(X, rev(L), (M [ Y <- _ ]b)[X]b ==K E)
  => forall(X, rev(L),  M             [X]b ==K E)
     requires disjoint1(L, Y)

// X is not in the activation queue before and after updating AEM
rule activationQueue(VIDs, AEM [ X <- E ]i, AM, FinalizedEpoch)
  => activationQueue(VIDs, AEM            , AM, FinalizedEpoch)
     requires AEM[X]i >Int FinalizedEpoch
      andBool E       >Int FinalizedEpoch

// for processValidatorEjections

rule forall(X, rev(L), #if E0 #then (M [ Y <- _ ]i)[X]i >=Int E1 andBool (M [ Y <- _ ]i)[X]i <Int E2 andBool countValidatorsToExit(VIDs, EM, (M [ Y <- _ ]i)[X]i) <=Int E3 #else (M [ Y <- _ ]i)[X]i ==K E4 #fi)
  => forall(X, rev(L), #if E0 #then  M             [X]i >=Int E1 andBool  M             [X]i <Int E2 andBool countValidatorsToExit(VIDs, EM,  M             [X]i) <=Int E3 #else  M             [X]i ==K E4 #fi)
     requires disjoint1(L, Y)

rule countValidatorsToExit(VIDs, EM [ VID <- E ]i, Exit) <=Int ChurnLimit
  => countValidatorsToExit(VIDs, EM              , Exit) <=Int ChurnLimit
     requires countValidatorsToExit(VIDs, EM, E) <Int ChurnLimit
      andBool EM[VID]i ==Int FAR_FUTURE_EPOCH

// X is active before and after updating EM
rule activeValidators(VIDs, AM, EM [ X <- E ]i, Epoch)
  => activeValidators(VIDs, AM, EM            , Epoch)
     requires EM[X]i  >Int Epoch
      andBool E       >Int Epoch
      andBool AM[X]i <=Int Epoch

// for process-validator-updates-spec

// for process-deposit-spec

syntax Bool ::= isValidDeposits(Deposits) [function, smtlib(isValidDeposits)]
rule isValidDeposits(D Ds) => D.amount >=Int 0 andBool isValidDeposits(Ds)
rule isValidDeposits(.Deposits) => true

// remove duplicate elements in the given list: the ones that appear earlier (more left) are removed.
syntax IntList ::= unique(IntList) [function, smtlib(uniqueI)]
rule unique(I Is) =>   unique(Is) requires         I in Is
rule unique(I Is) => I unique(Is) requires notBool I in Is
rule unique(.IntList) => .IntList

rule unique(Is) => Is requires distinct(Is)

rule distinct(unique(_)) => true [concrete, smt-lemma]

rule iff(X in unique(L1 ++ L2), X in L1 orBool X in L2) => true [concrete, smt-lemma]

rule unique(rev(Ys) ++ X Xs)
  => unique(rev(Ys) ++   Xs)
     requires X in Xs

rule unique((X Xs) ++ Ys)
  => unique(   Xs  ++ Ys)
     requires X in Xs orBool X in Ys

rule   unique((X Xs) ++ Ys)
  => X unique(   Xs  ++ Ys)
     requires notBool X in unique(Xs ++ Ys)
     [concrete, smt-lemma]

rule subset(L, unique(_ ++ L)) => true
     requires distinct(L)
     [concrete, smt-lemma]

// for process-block

rule maxExitEpoch(unique(L ++ VIDs), EM2)
 ==K maxExitEpoch(            VIDs,  EM1) => true
     requires forall(x, L, implies(notBool x in VIDs, EM2[x]i ==Int FAR_FUTURE_EPOCH)) // new validators have no exit epoch
      andBool forall(x, VIDs, EM2[x]i ==Int EM1[x]i) // existing validators' exit epoch is preserved
     [concrete, smt-lemma]

rule activeValidators(unique(L ++ VIDs), AM2, EM2, Epoch)
 ==K activeValidators(            VIDs , AM1, EM1, Epoch) => true
     requires forall(x, L, implies(notBool x in VIDs, AM2[x]i ==Int FAR_FUTURE_EPOCH)) // new validators are not active
      andBool forall(x, VIDs, AM2[x]i ==Int AM1[x]i) // existing validators' activation epoch is preserved
      andBool forall(x, VIDs, EM2[x]i ==Int EM1[x]i) // existing validators' exit epoch is preserved
     [concrete, smt-lemma]

rule implies(
       forall(x, getValidatorsE(VEs), x in VIDs:IntList)
     ,
       forallE(x, VEs, x.validator in VIDs)
     ) => true
     [concrete, smt-lemma]

rule X.validator in getValidatorsE(VEs) => true requires X inE VEs [concrete, smt-lemma]

// for process-attestation

syntax Attestations ::= getAttestations(Attestations, Int) [function, smtlib(getAttestations)]
rule getAttestations(A As, E) => A getAttestations(As, E) requires A.target_epoch  ==Int E
rule getAttestations(A As, E) =>   getAttestations(As, E) requires A.target_epoch =/=Int E
rule getAttestations(.Attestations, _) => .Attestations

// TODO: add check A.attester in VIDs
syntax Bool ::= isValidAttestationListPartial(Attestations, Int, IList, IMap) [function, smtlib(isValidAttestationListPartial)]
rule isValidAttestationListPartial(A As, Slot, SourceEpoch, SourceBlock)
  => isValidAttestation(A, Slot, SourceEpoch[A.target_epoch]ii, SourceBlock[firstSlotOf(SourceEpoch[A.target_epoch]ii)]i, false)
     andBool isValidAttestationListPartial(As, Slot, SourceEpoch, SourceBlock)
rule isValidAttestationListPartial(.Attestations, _, _, _) => true

// for process-slashing

// for process-justification-finalization

rule implies(isJustifiable(E, B, As1, SM, EBM, AM, EM, VIDs), isJustifiable(E, B, As2, SM, EBM, AM, EM, VIDs)) => true
    requires subsetA(As1, As2)
    [concrete, smt-lemma]

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

// TODO: prove lemmas

endmodule
