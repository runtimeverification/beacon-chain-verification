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
andBool ?LastExitEpoch +Int sizeE(VEs) <Int FAR_FUTURE_EPOCH
andBool forallE(x, VEs, isValidVoluntaryExit(x, AM, EM1, ?Epoch))
andBool distinct(getValidatorsE(VEs))
andBool forall(x, getValidatorsE(VEs), x in VIDs)
// invariants
ensures true
// post-conditions
andBool forall(x, getValidatorsE(VEs), ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch))
andBool forall(x, getValidatorsE(VEs), ?EM2[x]i  <Int FAR_FUTURE_EPOCH)
andBool forall(x, getValidatorsE(VEs), countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit)

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
andBool ?LastExitEpoch +Int sizeE(R_VEs) <Int FAR_FUTURE_EPOCH
andBool forallE(x, R_VEs, isValidVoluntaryExit(x, AM, EM0, ?Epoch))
andBool distinct(getValidatorsE(R_VEs))
andBool forall(x, getValidatorsE(R_VEs), x in VIDs)
// invariants
andBool disjoint(L_VIDs, getValidatorsE(R_VEs))
andBool forall(x, getValidatorsE(R_VEs), EM1[x]i ==K EM0[x]i)
andBool forall(x, getValidatorsE(R_VEs), WM1[x]i ==K WM0[x]i)
andBool forall(x, rev(L_VIDs)                         , EM1[x]i >=Int delayedActivationExitEpoch(?Epoch))
andBool forall(x, rev(L_VIDs)                         , EM1[x]i  <Int FAR_FUTURE_EPOCH)
andBool forall(x, rev(L_VIDs)                         , countValidatorsToExit(VIDs, EM1, EM1[x]i) <=Int ?ChurnLimit)
ensures true
// post-conditions
andBool forall(x, rev(L_VIDs) ++ getValidatorsE(R_VEs), ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch))
andBool forall(x, rev(L_VIDs) ++ getValidatorsE(R_VEs), ?EM2[x]i  <Int FAR_FUTURE_EPOCH)
andBool forall(x, rev(L_VIDs) ++ getValidatorsE(R_VEs), countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit)

endmodule
