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
syntax Bool ::= forall(KVar, IntList, Bool) [binder, function] // smtlib((forall ((#1 Int)) (=> (inI #1 #2) #3)))
rule forall(X, V Vs, E) => E[V / X] andBool forall(X, Vs, E)
rule forall(_, .IntList, _) => true
rule forall(_, _, true) => true
rule forall(X, S, X in S) => true

syntax VoluntaryExit ::= KVar
syntax Bool ::= forallE(KVar, VoluntaryExits, Bool) [binder, function]
rule forallE(X, V Vs, E) => E[V / X] andBool forallE(X, Vs, E)
rule forallE(_, .VoluntaryExits, _) => true
rule forallE(_, _, true) => true

/*
syntax Validator ::= KVar
syntax Bool ::= forallV(KVar, ValidatorList, Bool) [binder, function]
rule forallV(X, V Vs, E) => E[V / X] andBool forallV(X, Vs, E)
rule forallV(_, .ValidatorList, _) => true
rule forallV(_, _, true) => true
*/

/*
syntax Int ::= KVar
syntax Int ::= lambda(KVar, Int) [binder, function]

syntax Bool ::= forall(KVar, IntList, Bool) [binder, function]
rule forall(X, V Vs, E) => E[V / X] andBool forall(X, Vs, E)
rule forall(_, .IntList, _) => true

syntax ValidatorMap ::= ValidatorMap "[" IntList ":=" Validator "]i" [function]
rule M [ (K Ks) := lambda(X, V) ]i => ( M [ K <- V[K / X] ]i ) [ Ks := lambda(X, V) ]i
rule M [ .IntList := _ ]i => M
*/

// rule maxInt(I1, I2) => I1 requires I1 >=Int I2
// rule maxInt(I1, I2) => I2 requires I1 <Int I2

/*
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

rule (V with slashed                      = _).activation_eligibility_epoch => V.activation_eligibility_epoch
rule (V with balance                      = _).activation_eligibility_epoch => V.activation_eligibility_epoch
rule (V with effective_balance            = _).activation_eligibility_epoch => V.activation_eligibility_epoch
rule (V with activation_eligibility_epoch = I).activation_eligibility_epoch => I
rule (V with activation_epoch             = _).activation_eligibility_epoch => V.activation_eligibility_epoch
rule (V with exit_epoch                   = _).activation_eligibility_epoch => V.activation_eligibility_epoch
rule (V with withdrawable_epoch           = _).activation_eligibility_epoch => V.activation_eligibility_epoch

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
*/

// for l-spec
rule countValidatorsToExit(v(m(SM, BM, EBM, AEM, AM, EM [ VID <- E ]i, WM [ VID <- _ ]i), VIDs), Exit)
  => countValidatorsToExit(v(m(SM, BM, EBM, AEM, AM, EM,               WM              ), VIDs), Exit) +Int 1
    requires E =/=Int EM[VID]i
     andBool E ==Int Exit
     andBool VID in VIDs

syntax Bool ::= isValidVoluntaryExits(VoluntaryExits, ValidatorMap, Int, IntList) [function]
rule isValidVoluntaryExits(E Es, VM, Epoch, VIDs) => isValidVoluntaryExit(E, VM, Epoch) andBool isValidVoluntaryExits(Es, VM, Epoch, VIDs)
                                                     andBool distinctVoluntaryExits(E Es)
                                                     andBool E.validator in VIDs
rule isValidVoluntaryExits(.VoluntaryExits, _, _, _) => true

rule isValidVoluntaryExits(Es, m(SM, BM, EBM, AEM, AM, EM [ E.validator <- _ ]i, WM [ E.validator <- _ ]i), Epoch, VIDs) => true
    requires isValidVoluntaryExits(Es, m(SM, BM, EBM, AEM, AM, EM, WM), Epoch, VIDs)
     andBool distinctVoluntaryExits(E Es)

syntax Bool ::= distinctVoluntaryExits(VoluntaryExits) [function]
// TODO: implement
// rule distinctVoluntaryExits(Es) => distinct(Es.validator)

syntax Bool ::= distinct(IntList) [function, smtlib(distinctI)]
// TODO: implement

/// syntax Validators ::= storeValidatorExits(Validators, VoluntaryExits, Int) [function]
/// rule storeValidatorExits(v(VM, VIDs), E Es, Epoch)
///   => storeValidatorExits(v(VM [ E.validator <- VM[E.validator]i with exit_epoch         = computeExitEpoch(v(VM, VIDs), Epoch)
///                                                                 with withdrawable_epoch = computeExitEpoch(v(VM, VIDs), Epoch) +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY ]i, VIDs), Es, Epoch)
/// rule storeValidatorExits(Vs, .VoluntaryExits, _) => Vs
/// 
/// syntax ValidatorMap ::= updateValidatorExits(ValidatorMap, VoluntaryExits, IntList, Int) [function]
/// rule updateValidatorExits(VM, E Es, VIDs, Epoch) => updateValidatorExits(VM [ E.validator <- updateExitEpoch(VM[E.validator]i, v(VM,VIDs), Epoch) ]i, Es, VIDs, Epoch)
/// rule updateValidatorExits(VM, .VoluntaryExits, _, _) => VM
/// 
/// rule countValidatorsToExit(v(updateValidatorExits(VM [ VE.validator <- V ]i, VEs, VIDs, Epoch), VIDs), E) <=Int ChurnLimit => true
///      requires countValidatorsToExit(v(VM [ VE.validator <- V ]i, VIDs), E) <=Int ChurnLimit
///       andBool forallE(x, VEs, countValidatorsToExit(v(updateValidatorExits(VM [ VE.validator <- V ]i, VEs, VIDs, Epoch), VIDs), updateValidatorExits(VM [ VE.validator <- V ]i, VEs, VIDs, Epoch)[x.validator]i.exit_epoch) <=Int ChurnLimit)
///       andBool distinctVoluntaryExits(VE VEs)
/// 
/// rule activeValidators(v(updateValidatorExits(VM, VEs, _, _), VIDs), Epoch) => activeValidators(v(VM, VIDs), Epoch) // TODO: proof
///      requires isValidVoluntaryExits(VEs, VM, Epoch, VIDs)

rule activeValidators(v(m(SM, BM, EBM, AEM, AM, EM [ VID <- E ]i, WM [ VID <- _ ]i), VIDs), Epoch)
  => activeValidators(v(m(SM, BM, EBM, AEM, AM, EM              , WM              ), VIDs), Epoch)
     requires E >Int Epoch
      andBool EM[VID]i ==Int FAR_FUTURE_EPOCH
    //andBool VM[VID]i.activation_epoch ==Int V.activation_epoch

/// 
/// rule updateValidatorExits(VM, Es, _, _) [ E.validator ]i => VM [ E.validator ]i
///      requires distinctVoluntaryExits(E Es)
/// 
/// rule VM[VID]i.id => VID
/// 
/// syntax Validator ::= updateExitEpoch(Validator, Validators, Int) [function]
/// rule [updateExitEpoch]:
///      updateExitEpoch(V, Vs, Epoch) => V with exit_epoch         = computeExitEpoch(Vs, Epoch)
///                                         with withdrawable_epoch = computeExitEpoch(Vs, Epoch) +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY

rule sizeE(_) >=Int 0 => true [smt-lemma]

rule countValidatorsToExit(Vs, E) => 0
     requires maxExitEpoch(Vs) <Int E andBool E <Int FAR_FUTURE_EPOCH
     [smt-lemma]

rule maxExitEpoch(v(m(SM, BM, EBM, AEM, AM, EM [ VID <- E ]i, WM [ VID <- _ ]i), VIDs)) => maxInt(maxExitEpoch(v(m(SM, BM, EBM, AEM, AM, EM, WM), VIDs)), E)
     requires E =/=Int FAR_FUTURE_EPOCH
      andBool VID in VIDs



rule forall(X, rev(L), countValidatorsToExit(VS, (M [ Y <- _ ]i)[X]i) <=Int E)
  => forall(X, rev(L), countValidatorsToExit(VS,  M             [X]i) <=Int E)
     requires disjoint1(L, Y)



syntax IntList ::= getValidatorsE(VoluntaryExits) [function, smtlib(getValidatorsE)]
rule getValidatorsE(E Es) => E.validator getValidatorsE(Es)
rule getValidatorsE(.VoluntaryExits) => .IntList



// for m-spec
/*
rule sizeI(take(N, _)) <=Int M => true requires N >=Int 0 andBool N <=Int M
*/
rule sizeI(take(N, _)) <=Int N => true requires N >=Int 0 [smt-lemma]
rule sizeI(_) >=Int 0 => true [smt-lemma]

rule subsetI(take(_, S1), S2) => true requires subsetI(S1, S2)
rule subsetI(sort(S1), S2) => true requires subsetI(S1, S2)
rule subsetI(S, S) => true

/// syntax ValidatorMap ::= updateActivations(ValidatorMap, ValidatorList, Int) [function]
/// rule updateActivations(VM, V Vs, Epoch) => updateActivations(VM [ V.id <- V with activation_epoch = delayedActivationExitEpoch(Epoch) ]i, Vs, Epoch)
/// rule updateActivations(VM, .ValidatorList, _) => VM
/// 
/// rule updateActivations(VM, Vs, _) [ V.id ]i => VM [ V.id ]i
///      requires distinctValidators(V Vs)
/// 
/// syntax Bool ::= distinctValidators(ValidatorList) [function]
/// // TODO: implement
/// // rule distinctValidators(Vs) => distinct(Vs.id)
/// 
/// syntax Bool ::= isValidValidatorsToActivate(ValidatorList, Validators, Int) [function]
/// rule isValidValidatorsToActivate(V Vs, v(VM, VIDs), FinalizedEpoch) => isValidValidatorToActivate(V, FinalizedEpoch) andBool isValidValidatorsToActivate(Vs, v(VM, VIDs), FinalizedEpoch)
///                                                                        andBool distinctValidators(V Vs)
///                                                                        andBool V.id in VIDs
///                                                                        andBool VM[V.id]i ==K V
/// rule isValidValidatorsToActivate(.ValidatorList, _, _) => true
/// 
/// rule isValidValidatorsToActivate(Vs, v(VM [ V.id <- _ ]i, VIDs), FinalizedEpoch) => true
///     requires isValidValidatorsToActivate(Vs, v(VM, VIDs), FinalizedEpoch)
///      andBool distinctValidators(V Vs)
/// 
/// syntax Int ::= countValidatorsToActivate(Validators, Int) [function, smtlib(countValidatorsToActivate)]
/// rule countValidatorsToActivate(v(VM, VID VIDs), ActivationEpoch)
///   => #if VM[VID]i.activation_epoch ==Int ActivationEpoch #then 1 #else 0 #fi +Int countValidatorsToActivate(v(VM, VIDs), ActivationEpoch)
/// rule countValidatorsToActivate(v(_, .IntList), _) => 0
/// 
/// rule countValidatorsToActivate(v(VM [ VID <- V ]i, VIDs), E) => countValidatorsToActivate(v(VM, VIDs), E) +Int 1
///     requires V.activation_epoch =/=Int VM[VID]i.activation_epoch
///      andBool V.activation_epoch ==Int E
///      andBool VID in VIDs
/// 

rule activeValidators(v(m(SM, BM, EBM, AEM, AM [ VID <- E ]i, EM, WM), VIDs), Epoch)
  => activeValidators(v(m(SM, BM, EBM, AEM, AM              , EM, WM), VIDs), Epoch)
     requires E >Int Epoch
      andBool AM[VID]i ==Int FAR_FUTURE_EPOCH
    //andBool VM[VID]i.exit_epoch ==Int V.exit_epoch

/// 
/// rule isValidValidatorsToActivate(take(_, sort(activationQueue(Vs, FinalizedEpoch))), Vs, FinalizedEpoch) => true
/// // TODO: proof

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

rule getBaseReward(B, T) <=Int B => true requires B >=Int 0 andBool T >=Int 256 [smt-lemma]
rule getBaseReward(B, T) >=Int 0 => true requires B >=Int 0 andBool T >=Int 1   [smt-lemma]

rule getMatchingReward(B, A, T) <=Int B => true requires B >=Int 0 andBool A >=Int 0 andBool T >=Int EFFECTIVE_BALANCE_INCREMENT andBool A <=Int T [smt-lemma]
rule getMatchingReward(B, A, T) >=Int 0 => true requires B >=Int 0 andBool A >=Int 0 andBool T >=Int EFFECTIVE_BALANCE_INCREMENT                   [smt-lemma]

rule getInclusionReward(B, D) <=Int B => true requires B >=Int 0 andBool D >=Int 1 [smt-lemma]
rule getInclusionReward(B, D) >=Int 0 => true requires B >=Int 0 andBool D >=Int 1 [smt-lemma]

rule getInactivityPenalty(B, D) >=Int 0 => true requires B >=Int 0 andBool D >=Int 0 [smt-lemma]

syntax IntList ::= rev(IntList) [function, smtlib(revI)]

rule rev(.IntList) => .IntList

syntax IntList ::= IntList "++" IntList [function, smtlib(concatI)]

rule L ++ .IntList => L
rule .IntList ++ L => L

rule rev(X Ys) ++ Xs => rev(Ys) ++ X Xs

rule forall(X, rev(V Vs), E) => E[V / X] andBool forall(X, rev(Vs), E)

syntax Bool ::= disjoint(IntList, IntList) [function, smtlib(disjointI)]
              | disjoint1(IntList, Int)    [function, smtlib(disjointI1)]
rule disjoint(Ls, R Rs) => disjoint1(Ls, R) andBool disjoint(Ls, Rs)
rule disjoint(.IntList, _) => true
rule disjoint(_, .IntList) => true

rule disjoint(R Ls, Rs) => true
     requires distinct(R Rs) andBool disjoint(Ls, Rs)

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

rule implies(distinct(L Ls), distinct(Ls)) => true [concrete, smt-lemma]

rule lift(totalBalance(M, L1)) <=Int lift(totalBalance(M, L2)) => true
     requires subset(L1, L2)

rule subset(getValidators(As), activeValidators(Vs, Epoch)) => true
     requires isValidAttestations(As, Vs, Epoch)

syntax Bool ::= isValidAttestations(Attestations, Validators, Int) [function]

rule isValidAttestations(filterNotSlashed(_, As), Vs, Epoch) => true requires isValidAttestations(As, Vs, Epoch)
rule isValidAttestations(filterByTarget(_,   As), Vs, Epoch) => true requires isValidAttestations(As, Vs, Epoch)
rule isValidAttestations(filterByHead(_,     As), Vs, Epoch) => true requires isValidAttestations(As, Vs, Epoch)

/// // TODO: drop
/// rule _.effective_balance >=Int 0 => true [concrete, smt-lemma]

// for o-spec

rule forall(X, rev(L), (M [ Y <- _ ]i)[X]i ==K E)
  => forall(X, rev(L),  M             [X]i ==K E)
     requires disjoint1(L, Y)

/*
rule forall(X, Ls, (M [ L <- _ ]i)[X]i ==K E)
  => forall(X, Ls,  M             [X]i ==K E)
     requires distinct(L Ls)
*/

// for p-spec

rule size(_:IntList) >=Int 0 => true [smt-lemma]

rule forall(X, rev(L), #if E0 #then (M [ Y <- _ ]i)[X]i >=Int E1 andBool (M [ Y <- _ ]i)[X]i <Int E2 andBool countValidatorsToExit(VS, (M [ Y <- _ ]i)[X]i) <=Int E3 #else (M [ Y <- _ ]i)[X]i ==K E4 #fi)
  => forall(X, rev(L), #if E0 #then  M             [X]i >=Int E1 andBool  M             [X]i <Int E2 andBool countValidatorsToExit(VS,  M             [X]i) <=Int E3 #else  M             [X]i ==K E4 #fi)
     requires disjoint1(L, Y)

rule countValidatorsToExit(v(m(SM, BM, EBM, AEM, AM, EM [ VID <- E ]i, WM [ VID <- _ ]i), VIDs), Exit) <=Int ChurnLimit
  => countValidatorsToExit(v(m(SM, BM, EBM, AEM, AM, EM              , WM              ), VIDs), Exit) <=Int ChurnLimit
     requires countValidatorsToExit(v(m(SM, BM, EBM, AEM, AM, EM, WM), VIDs), E) <Int ChurnLimit
      andBool EM[VID]i ==Int FAR_FUTURE_EPOCH

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
rule implies(A, B) => notBool A orBool B [macro]

syntax Bool ::= iff(Bool, Bool) [function, functional]
rule iff(A, B) => implies(A, B) andBool implies(B, A) [macro]

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
