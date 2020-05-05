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

// // for process-epoch-spec
// rule (I /Int 32) *Int 32 => I

endmodule

module VERIFICATION

imports DYNAMIC-ABSTRACT-BEACON-CHAIN
imports LEMMAS-JAVA
imports SUBSTITUTION

rule ( K1 |-> V M:Map ) [ K2 ] => V        requires K1  ==Int K2
rule ( K1 |-> _ M:Map ) [ K2 ] => M [ K2 ] requires K1 =/=Int K2

syntax KVar ::= "x" [token]

syntax Int ::= KVar
syntax Bool ::= forall(KVar, IntList, Bool) [binder, function, smtlib((forall ((#1 Int)) (=> (inI #1 #2) #3)))]
rule forall(X, V Vs, E) => E[V / X] andBool forall(X, Vs, E)
rule forall(_, .IntList, _) => true
rule forall(_, _, true) => true
rule forall(X, S, X in S) => true

syntax VoluntaryExit ::= KVar
syntax Bool ::= forallE(KVar, VoluntaryExits, Bool) [binder, function, smtlib((forall ((#1 VoluntaryExit)) (=> (inE #1 #2) #3)))]
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

// for processVoluntaryExits
rule countValidatorsToExit(VIDs, EM [ VID <- E ]i, Exit)
  => countValidatorsToExit(VIDs, EM,               Exit) +Int 1
    requires E =/=Int EM[VID]i
     andBool E ==Int Exit
     andBool VID in VIDs

/// syntax Bool ::= isValidVoluntaryExits(VoluntaryExits, ValidatorMap, Int, IntList) [function]
/// rule isValidVoluntaryExits(E Es, VM, Epoch, VIDs) => isValidVoluntaryExit(E, VM, Epoch) andBool isValidVoluntaryExits(Es, VM, Epoch, VIDs)
///                                                      andBool distinctVoluntaryExits(E Es)
///                                                      andBool E.validator in VIDs
/// rule isValidVoluntaryExits(.VoluntaryExits, _, _, _) => true
/// 
/// rule isValidVoluntaryExits(Es, m(SM, BM, EBM, AEM, AM, EM [ E.validator <- _ ]i, WM [ E.validator <- _ ]i), Epoch, VIDs) => true
///     requires isValidVoluntaryExits(Es, m(SM, BM, EBM, AEM, AM, EM, WM), Epoch, VIDs)
///      andBool distinctVoluntaryExits(E Es)

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

rule activeValidators(VIDs, AM, EM [ VID <- E ]i, Epoch)
  => activeValidators(VIDs, AM, EM              , Epoch)
     requires E >Int Epoch
      andBool EM[VID]i ==Int FAR_FUTURE_EPOCH

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

rule countValidatorsToExit(VIDs, EM, E) => 0
     requires maxExitEpoch(VIDs, EM) <Int E andBool E <Int FAR_FUTURE_EPOCH
     [smt-lemma]

rule maxExitEpoch(VIDs, EM [ VID <- E ]i) => maxInt(maxExitEpoch(VIDs, EM), E)
     requires E =/=Int FAR_FUTURE_EPOCH
      andBool VID in VIDs



rule forall(X, rev(L), countValidatorsToExit(VIDs, EM, (M [ Y <- _ ]i)[X]i) <=Int E)
  => forall(X, rev(L), countValidatorsToExit(VIDs, EM,  M             [X]i) <=Int E)
     requires disjoint1(L, Y)



syntax IntList ::= getValidatorsE(VoluntaryExits) [function, smtlib(getValidatorsE)]
rule getValidatorsE(E Es) => E.validator getValidatorsE(Es)
rule getValidatorsE(.VoluntaryExits) => .IntList



// for processValidatorActivation
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

rule distinct(take(_, sort(L))) => true
     requires distinct(L)

rule forall(X, take(_, sort(L)), E) => true
     requires forall(X, L, E)

/// 
/// rule isValidValidatorsToActivate(take(_, sort(activationQueue(Vs, FinalizedEpoch))), Vs, FinalizedEpoch) => true
/// // TODO: proof

// for processRewardsPenalties

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

rule subset(getValidators(As), activeValidators(VIDs, AM, EM, Epoch)) => true
     requires isValidAttestations(As, VIDs, AM, EM, Epoch)

// the attester of each attestation is in the list of validators, and active in the given epoch
syntax Bool ::= isValidAttestations(Attestations, IntList, IMap, IMap, Int) [function, smtlib(isValidAttestations)]
// rule isValidAttestations(As, VIDs, AM, EM, Epoch) => forall(x, As, x.attester in VIDs andBool isActiveValidator(x.attester, AM, EM, Epoch))

rule isValidAttestations(filterNotSlashed(_, As), VIDs, AM, EM, Epoch) => true requires isValidAttestations(As, VIDs, AM, EM, Epoch)
rule isValidAttestations(filterByTarget(_,   As), VIDs, AM, EM, Epoch) => true requires isValidAttestations(As, VIDs, AM, EM, Epoch)
rule isValidAttestations(filterByHead(_,     As), VIDs, AM, EM, Epoch) => true requires isValidAttestations(As, VIDs, AM, EM, Epoch)

/// // TODO: drop
/// rule _.effective_balance >=Int 0 => true [concrete, smt-lemma]

// for updateActivationEligibilities

rule forall(X, rev(L), (M [ Y <- _ ]i)[X]i ==K E)
  => forall(X, rev(L),  M             [X]i ==K E)
     requires disjoint1(L, Y)

rule forall(X, rev(L), (M [ Y <- _ ]b)[X]b ==K E)
  => forall(X, rev(L),  M             [X]b ==K E)
     requires disjoint1(L, Y)

/*
rule forall(X, Ls, (M [ L <- _ ]i)[X]i ==K E)
  => forall(X, Ls,  M             [X]i ==K E)
     requires distinct(L Ls)
*/

// X is not in the activation queue before and after updating AEM
rule activationQueue(VIDs, AEM [ X <- E ]i, AM, FinalizedEpoch)
  => activationQueue(VIDs, AEM            , AM, FinalizedEpoch)
     requires AEM[X]i >Int FinalizedEpoch
      andBool E       >Int FinalizedEpoch

// for processValidatorEjections

rule size(_:IntList) >=Int 0 => true [smt-lemma]

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

/// rule activeValidators(v(m(_, _, _, _, AM, EM, _), VIDs), Epoch)
///  ==K activeValidators(v(m(_, _, _, _, AM, EM, _), VIDs), Epoch) => true [smt-lemma]

/// rule activationQueue(v(m(_, _, _, AEM, AM, _, _), VIDs), E)
///  ==K activationQueue(v(m(_, _, _, AEM, AM, _, _), VIDs), E) => true [smt-lemma]

// for process-deposit-spec

syntax Bool ::= isValidDeposits(Deposits) [function, smtlib(isValidDeposits)]
rule isValidDeposits(D Ds) => D.amount >=Int 0 andBool isValidDeposits(Ds)
rule isValidDeposits(.Deposits) => true

syntax IntList ::= getValidatorsD(Deposits) [function, smtlib(getValidatorsD)]
rule getValidatorsD(D Ds) => D.sender getValidatorsD(Ds)
rule getValidatorsD(.Deposits) => .IntList

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

rule implies(X in Xs1, X in Xs2) => true
     requires subset(Xs1, Xs2)
     [concrete, smt-lemma]

rule subset(L, unique(_ ++ L)) => true
     requires distinct(L)
     [concrete, smt-lemma]

rule disjoint1(Is, I) => true requires distinct(I Is) [concrete, smt-lemma]

rule implies(J in Js andBool disjoint1(Js, I), I =/=K J) => true [concrete, smt-lemma]

rule iff(X in rev(L), X in L) => true [concrete, smt-lemma]

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

// for process-attestation

syntax Attestations ::= getAttestations(Attestations, Int) [function, smtlib(getAttestations)]
rule getAttestations(A As, E) => A getAttestations(As, E) requires A.target_epoch  ==Int E
rule getAttestations(A As, E) =>   getAttestations(As, E) requires A.target_epoch =/=Int E
rule getAttestations(.Attestations, _) => .Attestations

syntax Bool ::= isValidAttestationList(Attestations, Int, IList, IMap, BMap) [function, smtlib(isValidAttestationList)]
rule isValidAttestationList(A As, Slot, SourceEpoch, SourceBlock, Slashed)
  => isValidAttestation(A, Slot, SourceEpoch[A.target_epoch]ii, SourceBlock[firstSlotOf(SourceEpoch[A.target_epoch]ii)]i, Slashed[A.attester]b)
     andBool ( A.target_epoch ==Int epochOf(Slot) orBool A.target_epoch ==Int epochOf(Slot) -Int 1 ) // TODO: drop
     andBool isValidAttestationList(As, Slot, SourceEpoch, SourceBlock, Slashed)
rule isValidAttestationList(.Attestations, _, _, _, _) => true

// rule (A getAttestations(As, E)) ++ As0
//   => A (getAttestations(As, E)  ++ As0)

// for process-slashing

syntax Slashing ::= KVar
syntax Bool ::= forallS(KVar, Slashings, Bool) [binder, function, smtlib((forall ((#1 Slashing)) (=> (inS #1 #2) #3)))]
rule forallS(X, V Vs, E) => E[V / X] andBool forallS(X, Vs, E)
rule forallS(_, .Slashings, _) => true
rule forallS(_, _, true) => true

/*
syntax Bool ::= isValidSlashings(Slashings, BMap) [function, smtlib(isValidSlashings)]
rule isValidSlashings(S Ss)
  => isSlashableAttestation(S.attestation_1, S.attestation_2)
     andBool S.attestation_1.attester ==Int S.attestation_2.attester
     andBool SM[S.attestation_1.attester]b ==K false
     andBool isValidSlashings(Ss)
*/

syntax IntList ::= getValidatorsS(Slashings) [function, smtlib(getValidatorsS)]
rule getValidatorsS(S Ss) => S.attestation_1.attester getValidatorsS(Ss)
rule getValidatorsS(.Slashings) => .IntList

syntax Tactic ::= "begin"
rule begin => .

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

syntax Bool ::= subsetA(Attestations, Attestations) [function, functional, smtlib(subsetA)]
rule implies(isJustifiable(E, B, As1, EBM, VIDs), isJustifiable(E, B, As2, EBM, VIDs)) => true
    requires subsetA(As1, As2)
    [concrete, smt-lemma]

/// syntax Pred ::= isValidState(Int, Int, Attestations, Validators, Bool,
///                              Int, Int, Attestations, Validators, Bool,
///                              Int) [function, functional]
/// rule isValidState(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs2, Epoch2Justified,
///                   Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1, Epoch1Justified,
///                   LastJustifiedEpoch)
///   => xor3(
///                 notBool isJustifiable(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs2)
///         andBool notBool isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1)
///         andBool LastJustifiedEpoch <Int Epoch2
///         andBool Epoch2Justified ==K false
///         andBool Epoch1Justified ==K false
///      ,
///                         isJustifiable(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs2)
///         andBool notBool isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1)
///         andBool LastJustifiedEpoch ==Int Epoch2
///         andBool Epoch2Justified ==K true
///         andBool Epoch1Justified ==K false
///      ,
///                         isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1)
///         andBool LastJustifiedEpoch ==Int Epoch1
///         andBool Epoch1Justified ==K true
///      )
/// 
/// 
/// syntax Bool ::= isGoodState(Int, Int, Attestations, Validators, Bool,
///                             Int, Int, Attestations, Validators, Bool,
///                             Int) [function, functional]
/// rule isGoodState(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs2, Epoch2Justified,
///                  Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1, Epoch1Justified,
///                  LastJustifiedEpoch)
///   => // justification of e-2 and e-1
///              iff(Epoch2Justified ==K true, isJustifiable(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs2))
///      andBool iff(Epoch1Justified ==K true, isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, Vs1))
///      // last justified epoch
///      andBool implies(LastJustifiedEpoch  <Int Epoch2, Epoch2Justified ==K false andBool Epoch1Justified ==K false)
///      andBool implies(LastJustifiedEpoch ==Int Epoch2, Epoch2Justified ==K true  andBool Epoch1Justified ==K false)
///      andBool implies(LastJustifiedEpoch ==Int Epoch1,                                   Epoch1Justified ==K true )
///      andBool         LastJustifiedEpoch <=Int Epoch1

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
