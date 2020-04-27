require "../../verification.k"
require "o1-spec.k"

module O2-SPEC

imports VERIFICATION
imports O1-SPEC

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
andBool ?VM1 ==K m(SM, BM, EBM, AEM1, AM, EM, WM)
// pre-conditions
andBool distinct(VIDs)
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, ?AEM2[x]i ==Int #if isActivationEligible(x, ?VM1) #then ?Epoch #else AEM1[x]i #fi)

endmodule
