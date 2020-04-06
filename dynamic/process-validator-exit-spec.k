require "verification.k"

module PROCESS-VALIDATOR-EXIT-SPEC

imports VERIFICATION

rule
<T>
  <k> case(xor2(
        countValidatorsToExit(v(VM1,VIDs), ?LastExitEpoch) >=Int ?ChurnLimit
      ,
        countValidatorsToExit(v(VM1,VIDs), ?LastExitEpoch)  <Int ?ChurnLimit
      ))
   ~> initiateValidatorExit(V) => . </k>
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
andBool ?Epoch ==Int epochOf(Slot)
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(v(VM1,VIDs)), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(VM1,VIDs), ?Epoch)))
// conditions
andBool V.id in VIDs
andBool V.exit_epoch ==Int FAR_FUTURE_EPOCH
andBool VM1[V.id]v ==K V
andBool ?LastExitEpoch +Int 1 <Int FAR_FUTURE_EPOCH
// invariant
andBool countValidatorsToExit(v(VM1,VIDs), ?LastExitEpoch +Int 1) ==Int 0
ensures true
// ensures
andBool ?VM2[V.id]v.exit_epoch >=Int delayedActivationExitEpoch(?Epoch)
andBool countValidatorsToExit(v(?VM2,VIDs), ?VM2[V.id]v.exit_epoch) <=Int ?ChurnLimit
/*
andBool activeValidators(v(VM1,VIDs), ?Epoch) ==K activeValidators(v(?VM2,VIDs), ?Epoch)
*/

endmodule
