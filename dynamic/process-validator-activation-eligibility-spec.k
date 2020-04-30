require "verification.k"

module PROCESS-VALIDATOR-ACTIVATION-ELIGIBILITY-SPEC

imports VERIFICATION

rule
<T>
  <k> updateActivationEligibilities(VIDs) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM, EBM, AEM1 => ?AEM2, AM, EM, WM), VIDs) </validators>
      <lastFinalized> FinalizedEpoch </lastFinalized>
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
// pre-conditions
andBool distinct(VIDs)
andBool FinalizedEpoch <Int FAR_FUTURE_EPOCH
andBool FinalizedEpoch <Int ?Epoch
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, ?AEM2[x]i ==Int #if isActivationEligible(x, AEM1, EBM) #then ?Epoch #else AEM1[x]i #fi)
// rely-guarantee conditions
andBool activationQueue(VIDs, ?AEM2, AM, FinalizedEpoch) ==K activationQueue(VIDs, AEM1, AM, FinalizedEpoch)

rule
<T>
  <k> updateActivationEligibilitiesAux(L_VIDs, R_VIDs, m(SM, BM, EBM, AEM0, AM, EM, WM)) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM, EBM, AEM1 => ?AEM2, AM, EM, WM), VIDs) </validators>
      <lastFinalized> FinalizedEpoch </lastFinalized>
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
// pre-conditions
andBool distinct(R_VIDs)
andBool FinalizedEpoch <Int FAR_FUTURE_EPOCH
andBool FinalizedEpoch <Int ?Epoch
// invariants
andBool disjoint(L_VIDs, R_VIDs)
andBool forall(x, R_VIDs, x in VIDs)
andBool forall(x, R_VIDs, AEM1[x]i ==K AEM0[x]i)
andBool forall(x, rev(L_VIDs),            AEM1[x]i ==Int #if isActivationEligible(x, AEM0, EBM) #then ?Epoch #else AEM0[x]i #fi)
andBool activationQueue(VIDs,  AEM1, AM, FinalizedEpoch) ==K activationQueue(VIDs, AEM0, AM, FinalizedEpoch)
ensures true
// post-conditions
andBool forall(x, rev(L_VIDs) ++ R_VIDs, ?AEM2[x]i ==Int #if isActivationEligible(x, AEM0, EBM) #then ?Epoch #else AEM0[x]i #fi)
// rely-guarantee conditions
andBool activationQueue(VIDs, ?AEM2, AM, FinalizedEpoch) ==K activationQueue(VIDs, AEM0, AM, FinalizedEpoch)

endmodule
