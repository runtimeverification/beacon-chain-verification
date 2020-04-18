require "../../verification.k"

module M2-SPEC

imports VERIFICATION

rule
<T>
  <k> activateValidators(Vs) => .K ... </k>
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
andBool ?Epoch ==Int epochOf(Slot) -Int 1
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(VM1,VIDs), ?Epoch)))
// conditions
andBool isValidValidators(Vs, VIDs)
ensures true
// ensures
andBool ?VM2 ==K updateActivations(VM1, Vs, ?Epoch)
andBool forallV(x, Vs, ?VM2[x.id]v.activation_epoch ==Int delayedActivationExitEpoch(?Epoch))
//andBool forallV(x, Vs, countValidatorsToActivate(v(?VM2, VIDs), ?VM2[x.id]v.activation_epoch) <=Int ?ChurnLimit)

endmodule
