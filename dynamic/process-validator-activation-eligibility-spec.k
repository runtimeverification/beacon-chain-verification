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

rule
<T>
  <k> updateActivationEligibilitiesAux(L_VIDs, R_VIDs, VM0) => .K ... </k>
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
andBool forall(x, rev(L_VIDs), VM1[x]v.activation_eligibility_epoch ==Int #if isActivationEligible(VM0[x]v) #then epochOf(Slot) #else VM0[x]v.activation_eligibility_epoch #fi)
// invariants
andBool distinct(R_VIDs)
andBool disjoint(L_VIDs, R_VIDs)
andBool forall(x, R_VIDs, VM1[x]v ==K VM0[x]v)
// consistency conditions
andBool forall(x, R_VIDs, x in VIDs)
ensures true
// ensures
andBool forall(x, rev(L_VIDs) ++ R_VIDs, ?VM2[x]v.activation_eligibility_epoch ==Int #if isActivationEligible(VM0[x]v) #then epochOf(Slot) #else VM0[x]v.activation_eligibility_epoch #fi)

endmodule
