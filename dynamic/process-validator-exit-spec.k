require "verification.k"

module PROCESS-VALIDATOR-EXIT-SPEC

imports VERIFICATION

rule
<T>
  <k> processVoluntaryExits(VEs) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM, EBM, AEM, AM, EM1 => ?EM2, WM1 => ?WM2), VIDs) </validators>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
// let-bindings
andBool ?Epoch ==Int epochOf(Slot)
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(VIDs, AM, EM1, ?Epoch)))
// pre-conditions
andBool ?LastExitEpoch +Int sizeE(VEs) +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY <Int FAR_FUTURE_EPOCH
andBool ?Epoch +Int EPOCHS_PER_SLASHINGS_VECTOR <Int FAR_FUTURE_EPOCH
andBool forallE(x, VEs, isValidVoluntaryExit(x, AM, EM1, ?Epoch))
andBool distinct(getValidatorsE(VEs))
andBool forall(x, getValidatorsE(VEs), x in VIDs)
//
andBool forall(x, VIDs,  BM[x]i >=Int 0)
andBool forall(x, VIDs, EBM[x]i >=Int 0)
andBool forall(x, VIDs, AEM[x]i >=Int 0)
andBool forall(x, VIDs,  AM[x]i >=Int 0)
andBool forall(x, VIDs, EM1[x]i >=Int 0)
andBool forall(x, VIDs, WM1[x]i >=Int 0)
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, implies(notBool x in getValidatorsE(VEs), ?EM2[x]i ==K EM1[x]i))
andBool forall(x, VIDs, implies(notBool x in getValidatorsE(VEs), ?WM2[x]i ==K WM1[x]i))
andBool forall(x, getValidatorsE(VEs), ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch))
andBool forall(x, getValidatorsE(VEs), ?EM2[x]i  <Int FAR_FUTURE_EPOCH)
andBool forall(x, getValidatorsE(VEs), countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit)
//
andBool forall(x, VIDs, ?EM2[x]i >=Int 0)
andBool forall(x, VIDs, ?WM2[x]i >=Int 0)

rule
<T>
  <k> processVoluntaryExitsAux(L_VIDs, R_VEs, m(SM, BM, EBM, AEM, AM, EM0, WM0)) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM, EBM, AEM, AM, EM1 => ?EM2, WM1 => ?WM2), VIDs) </validators>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
// let-bindings
andBool ?Epoch ==Int epochOf(Slot)
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(VIDs, AM, EM1, ?Epoch)))
// pre-conditions
andBool ?LastExitEpoch +Int sizeE(R_VEs) +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY <Int FAR_FUTURE_EPOCH
andBool ?Epoch +Int EPOCHS_PER_SLASHINGS_VECTOR <Int FAR_FUTURE_EPOCH
andBool forallE(x, R_VEs, isValidVoluntaryExit(x, AM, EM0, ?Epoch))
andBool distinct(getValidatorsE(R_VEs))
andBool forall(x, getValidatorsE(R_VEs), x in VIDs)
//
andBool forall(x, VIDs,  BM[x]i >=Int 0)
andBool forall(x, VIDs, EBM[x]i >=Int 0)
andBool forall(x, VIDs, AEM[x]i >=Int 0)
andBool forall(x, VIDs,  AM[x]i >=Int 0)
andBool forall(x, VIDs, EM0[x]i >=Int 0)
andBool forall(x, VIDs, WM0[x]i >=Int 0)
// invariants
andBool disjoint(L_VIDs, getValidatorsE(R_VEs))
andBool forall(x, getValidatorsE(R_VEs), EM1[x]i ==K EM0[x]i)
andBool forall(x, getValidatorsE(R_VEs), WM1[x]i ==K WM0[x]i)
andBool forall(x, VIDs, implies(notBool x in rev(L_VIDs)                         , EM1[x]i ==K EM0[x]i))
andBool forall(x, VIDs, implies(notBool x in rev(L_VIDs)                         , WM1[x]i ==K WM0[x]i))
andBool forall(x, rev(L_VIDs)                         , EM1[x]i >=Int delayedActivationExitEpoch(?Epoch))
andBool forall(x, rev(L_VIDs)                         , EM1[x]i  <Int FAR_FUTURE_EPOCH)
andBool forall(x, rev(L_VIDs)                         , countValidatorsToExit(VIDs, EM1, EM1[x]i) <=Int ?ChurnLimit)
//
andBool forall(x, rev(L_VIDs)                         , EM1[x]i >=Int 0)
andBool forall(x, rev(L_VIDs)                         , WM1[x]i >=Int 0)
ensures true
// post-conditions
andBool forall(x, VIDs, implies(notBool x in rev(L_VIDs) ++ getValidatorsE(R_VEs), ?EM2[x]i ==K EM0[x]i))
andBool forall(x, VIDs, implies(notBool x in rev(L_VIDs) ++ getValidatorsE(R_VEs), ?WM2[x]i ==K WM0[x]i))
andBool forall(x, rev(L_VIDs) ++ getValidatorsE(R_VEs), ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch))
andBool forall(x, rev(L_VIDs) ++ getValidatorsE(R_VEs), ?EM2[x]i  <Int FAR_FUTURE_EPOCH)
andBool forall(x, rev(L_VIDs) ++ getValidatorsE(R_VEs), countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit)
//
andBool forall(x, rev(L_VIDs) ++ getValidatorsE(R_VEs), ?EM2[x]i >=Int 0)
andBool forall(x, rev(L_VIDs) ++ getValidatorsE(R_VEs), ?WM2[x]i >=Int 0)

endmodule
