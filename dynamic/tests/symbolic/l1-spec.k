require "../../verification.k"

module L1-SPEC

imports VERIFICATION

rule
<T>
  <k> initiateValidatorExit(V) => . </k>
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
andBool V.exit_epoch ==Int FAR_FUTURE_EPOCH
// types
andBool Slot >=Int 0
ensures true
andBool ?VM2[V.id]v.exit_epoch >=Int delayedActivationExitEpoch(epochOf(Slot))

endmodule
