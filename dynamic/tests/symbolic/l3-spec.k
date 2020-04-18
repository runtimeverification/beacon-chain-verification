require "../../verification.k"

module L3-SPEC

imports VERIFICATION

rule
<T>
  <k> /* case(xor2(
        countValidatorsToExit(v(VM1,VIDs), ?LastExitEpoch) >=Int ?ChurnLimit
      ,
        countValidatorsToExit(v(VM1,VIDs), ?LastExitEpoch)  <Int ?ChurnLimit
      ))
   ~> */ initiateValidatorExit(V) => .K ... </k>
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
// invariant
andBool countValidatorsToExit(v(VM1,VIDs), ?LastExitEpoch +Int 1) ==Int 0
ensures true
// ensures
andBool ?V2 ==K updateExitEpoch(V, v(VM1,VIDs), ?Epoch)
andBool ?V2.exit_epoch >=Int delayedActivationExitEpoch(?Epoch)
andBool countValidatorsToExit(v(VM1 [ V.id <- ?V2 ]v, VIDs), ?V2.exit_epoch) <=Int ?ChurnLimit
/*
andBool activeValidators(v(VM1,VIDs), ?Epoch) ==K activeValidators(v(VM1 [ V.id <- ?V2 ]v, VIDs), ?Epoch)
*/
[matching(storeV)]

endmodule
