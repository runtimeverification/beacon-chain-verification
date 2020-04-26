require "../../verification.k"

module L6-SPEC

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
andBool ?VM1 ==K m(SM, BM, EBM, AEM, AM, EM1, WM1)
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(v(?VM1, VIDs)), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(?VM1, VIDs), ?Epoch)))
// pre-conditions
andBool ?LastExitEpoch +Int sizeE(VEs) <Int FAR_FUTURE_EPOCH
andBool forallE(x, VEs, isValidVoluntaryExit(x, ?VM1, ?Epoch))
andBool distinct(getValidatorsE(VEs))
andBool forall(x, getValidatorsE(VEs), x in VIDs)
// invariants
ensures true
// post-conditions
andBool forall(x, getValidatorsE(VEs), ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch))
andBool forall(x, getValidatorsE(VEs), ?EM2[x]i  <Int FAR_FUTURE_EPOCH)
andBool forall(x, getValidatorsE(VEs), countValidatorsToExit(v(m(SM, BM, EBM, AEM, AM, ?EM2, ?WM2), VIDs), ?EM2[x]i) <=Int ?ChurnLimit)

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
andBool ?VM0 ==K m(SM, BM, EBM, AEM, AM, EM0, WM0)
andBool ?VM1 ==K m(SM, BM, EBM, AEM, AM, EM1, WM1)
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(v(?VM1, VIDs)), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(?VM1, VIDs), ?Epoch)))
// pre-conditions
andBool ?LastExitEpoch +Int sizeE(R_VEs) <Int FAR_FUTURE_EPOCH
andBool forallE(x, R_VEs, isValidVoluntaryExit(x, ?VM0, ?Epoch))
andBool distinct(getValidatorsE(R_VEs))
andBool forall(x, getValidatorsE(R_VEs), x in VIDs)
// invariants
andBool disjoint(L_VIDs, getValidatorsE(R_VEs))
andBool forall(x, getValidatorsE(R_VEs), EM1[x]i ==K EM0[x]i)
andBool forall(x, getValidatorsE(R_VEs), WM1[x]i ==K WM0[x]i)
andBool forall(x, rev(L_VIDs)                         , EM1[x]i >=Int delayedActivationExitEpoch(?Epoch))
andBool forall(x, rev(L_VIDs)                         , EM1[x]i  <Int FAR_FUTURE_EPOCH)
andBool forall(x, rev(L_VIDs)                         , countValidatorsToExit(v(?VM1, VIDs), EM1[x]i) <=Int ?ChurnLimit)
ensures true
// post-conditions
andBool forall(x, rev(L_VIDs) ++ getValidatorsE(R_VEs), ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch))
andBool forall(x, rev(L_VIDs) ++ getValidatorsE(R_VEs), ?EM2[x]i  <Int FAR_FUTURE_EPOCH)
andBool forall(x, rev(L_VIDs) ++ getValidatorsE(R_VEs), countValidatorsToExit(v(m(SM, BM, EBM, AEM, AM, ?EM2, ?WM2), VIDs), ?EM2[x]i) <=Int ?ChurnLimit)

endmodule
