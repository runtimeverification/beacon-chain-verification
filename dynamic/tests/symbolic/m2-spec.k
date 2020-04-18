require "../../verification.k"

module M2-SPEC

imports VERIFICATION

rule
<T>
  <k> processValidatorActivation() => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(VM1 => ?VM2, VIDs) </validators>
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
andBool ?Epoch ==Int epochOf(Slot) -Int 1
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(VM1, VIDs), ?Epoch)))
andBool ?ActivationEpoch ==Int delayedActivationExitEpoch(?Epoch)
andBool ?ValidatorsToBeActivated ==K activationQueueUptoChurnLimit(v(VM1, VIDs), FinalizedEpoch, ?Epoch)
// conditions
andBool ?ActivationEpoch <Int FAR_FUTURE_EPOCH
andBool countValidatorsToActivate(v(VM1, VIDs), ?ActivationEpoch) ==Int 0
ensures true
// ensures
andBool ?VM2 ==K updateActivations(VM1, ?ValidatorsToBeActivated, ?Epoch)
andBool forallV(x, ?ValidatorsToBeActivated, ?VM2[x.id]v.activation_epoch ==Int ?ActivationEpoch)
andBool countValidatorsToActivate(v(?VM2, VIDs), ?ActivationEpoch) <=Int ?ChurnLimit

rule
<T>
  <k> activateValidators(Vs) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(VM1 => ?VM2, VIDs) </validators>
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
andBool ?Epoch ==Int epochOf(Slot) -Int 1
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(VM1, VIDs), ?Epoch)))
andBool ?ActivationEpoch ==Int delayedActivationExitEpoch(?Epoch)
// conditions
andBool ?ActivationEpoch <Int FAR_FUTURE_EPOCH
andBool isValidValidatorsToActivate(Vs, v(VM1, VIDs), FinalizedEpoch)
andBool countValidatorsToActivate(v(VM1, VIDs), ?ActivationEpoch) +Int sizeV(Vs) <=Int ?ChurnLimit
ensures true
// ensures
andBool ?VM2 ==K updateActivations(VM1, Vs, ?Epoch)
andBool forallV(x, Vs, ?VM2[x.id]v.activation_epoch ==Int ?ActivationEpoch)
andBool countValidatorsToActivate(v(?VM2, VIDs), ?ActivationEpoch) <=Int ?ChurnLimit

endmodule
