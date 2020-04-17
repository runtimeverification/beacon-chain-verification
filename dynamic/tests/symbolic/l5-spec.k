require "../../verification.k"

module L5-SPEC

imports VERIFICATION

// --concrete-rules "computeExitEpoch,eee"
rule
<T>
  <k> processVoluntaryExits(VEs) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(VM => ?VM2, VIDs) </validators>
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
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(VM,VIDs), ?Epoch)))
// conditions
andBool isValidVoluntaryExits(VEs, VM, ?Epoch)
ensures true
// ensures
andBool ?VM2 ==K sss(VM, VEs, VIDs, ?Epoch)
andBool forall(x, VEs, countValidatorsToExit(v(?VM2, VIDs), ?VM2[x.validator]v.exit_epoch) <=Int ?ChurnLimit)
[matching(sss,eee,storeV)]

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
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(VM1,VIDs), ?Epoch)))
ensures true
// ensures
andBool ?V2 ==K eee(V, v(VM1,VIDs), ?Epoch)
andBool countValidatorsToExit(v(VM1 [ V.id <- ?V2 ]v, VIDs), ?V2.exit_epoch) <=Int ?ChurnLimit
//andBool activeValidators(v(VM1,VIDs), ?Epoch) ==K activeValidators(v(VM1 [ V.id <- ?V2 ]v, VIDs), ?Epoch)
[trusted, matching(storeV)]

endmodule
