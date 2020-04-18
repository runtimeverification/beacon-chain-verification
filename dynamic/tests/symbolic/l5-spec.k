require "../../verification.k"
require "l3-spec.k"

module L5-SPEC

imports VERIFICATION
imports L3-SPEC

rule
<T>
  <k> processVoluntaryExits(VEs) => . </k>
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
andBool forall(x, VEs, countValidatorsToExit(v(?VM2, VIDs), ?VM2[x.validator]v.exit_epoch) <=Int ?ChurnLimit)
[matching(updateValidatorExits,updateExitEpoch,storeV)]

endmodule
