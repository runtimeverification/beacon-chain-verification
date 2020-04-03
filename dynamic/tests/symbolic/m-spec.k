require "../../verification.k"

module M-SPEC

imports VERIFICATION

rule
<T>
  <k> processValidatorActivation() => activateValidators(?ValidatorsToBeActivated) </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> Validators </validators>
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
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(Validators, ?Epoch)))
ensures true
// ensures
andBool size(?ValidatorsToBeActivated) <=Int ?ChurnLimit
andBool subset(?ValidatorsToBeActivated, activationQueue(Validators, FinalizedEpoch))

endmodule