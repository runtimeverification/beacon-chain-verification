require "verification.k"

module PROCESS-VALIDATOR-ACTIVATION-SPEC

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

// inductive case
rule
<T>
  <k> activateValidators(V Vs => Vs) </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(VM1 => ?VM2, _) </validators>
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
ensures true
// ensures
andBool ?VM2[V.id]v.activation_epoch ==Int delayedActivationExitEpoch(?Epoch)

// base case
rule
<T>
  <k> activateValidators(.ValidatorList) => . </k>
  ...
</T>

endmodule
