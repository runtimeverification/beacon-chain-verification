require "verification.k"

module PROCESS-VALIDATOR-EXIT-SPEC

imports VERIFICATION

rule
<T>
  <k> processVoluntaryExits(VEs) => .K ... </k>
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
andBool isValidVoluntaryExits(VEs, VM1, ?Epoch, VIDs)
andBool ?LastExitEpoch +Int sizeE(VEs) <Int FAR_FUTURE_EPOCH
ensures true
// ensures
andBool ?VM2 ==K updateValidatorExits(VM1, VEs, VIDs, ?Epoch)
andBool forallE(x, VEs, countValidatorsToExit(v(?VM2, VIDs), ?VM2[x.validator]v.exit_epoch) <=Int ?ChurnLimit)
[matching(updateValidatorExits,updateExitEpoch,storeV)]

rule
<T>
  <k> initiateValidatorExit(V) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(VM1 => VM1 [ V.id <- ?V2 ]v, VIDs) </validators>
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
andBool countValidatorsToExit(v(VM1,VIDs), ?LastExitEpoch +Int 1) ==Int 0
ensures true
// ensures
andBool ?V2 ==K updateExitEpoch(V, v(VM1,VIDs), ?Epoch)
andBool ?V2.exit_epoch >=Int delayedActivationExitEpoch(?Epoch)
andBool countValidatorsToExit(v(VM1 [ V.id <- ?V2 ]v, VIDs), ?V2.exit_epoch) <=Int ?ChurnLimit
[matching(storeV)]

endmodule
