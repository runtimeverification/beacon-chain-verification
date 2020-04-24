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
      <validators> v(VM1 => ?VM2, VIDs) </validators>
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
// conditions
// invariants
andBool distinct(VIDs)
// consistency conditions
ensures true
// ensures
andBool forall(x, VIDs, ?VM2[x]v.activation_eligibility_epoch ==Int #if isActivationEligible(VM1[x]v) #then epochOf(Slot) #else VM1[x]v.activation_eligibility_epoch #fi)

endmodule
