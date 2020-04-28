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
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, ?AEM2[x]i ==Int #if isActivationEligible(x, AEM1, EBM) #then ?Epoch #else AEM1[x]i #fi)

rule
<T>
  <k> updateActivationEligibilitiesAux(L_VIDs, R_VIDs, m(SM, BM, EBM, AEM0, AM, EM, WM)) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM, EBM, AEM1 => ?AEM2, AM, EM, WM), VIDs) </validators>
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
// invariants
andBool disjoint(L_VIDs, R_VIDs)
andBool forall(x, R_VIDs, x in VIDs)
andBool forall(x, R_VIDs, AEM1[x]i ==K AEM0[x]i)
andBool forall(x, rev(L_VIDs),            AEM1[x]i ==Int #if isActivationEligible(x, AEM0, EBM) #then ?Epoch #else AEM0[x]i #fi)
ensures true
// post-conditions
andBool forall(x, rev(L_VIDs) ++ R_VIDs, ?AEM2[x]i ==Int #if isActivationEligible(x, AEM0, EBM) #then ?Epoch #else AEM0[x]i #fi)

endmodule
