require "verification.k"

module PROCESS-VALIDATOR-EJECTION-SPEC

imports VERIFICATION

rule
<T>
  <k> processValidatorEjections(VIDs) => .K ... </k>
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
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(v(VM1, VIDs)), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(VM1, VIDs), ?Epoch)))
// pre-conditions
andBool ?LastExitEpoch +Int size(VIDs) <Int FAR_FUTURE_EPOCH
andBool distinct(VIDs)
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, #if isActiveValidator(VM1[x]v, ?Epoch -Int 1) andBool VM1[x]v.effective_balance <=Int EJECTION_BALANCE andBool VM1[x]v.exit_epoch ==Int FAR_FUTURE_EPOCH
                        #then ?VM2[x]v.exit_epoch >=Int delayedActivationExitEpoch(?Epoch) andBool ?VM2[x]v.exit_epoch <Int FAR_FUTURE_EPOCH
                              andBool countValidatorsToExit(v(?VM2, VIDs), ?VM2[x]v.exit_epoch) <=Int ?ChurnLimit
                        #else ?VM2[x]v.exit_epoch ==Int VM1[x]v.exit_epoch
                        #fi)

rule
<T>
  <k> processValidatorEjectionsAux(L_VIDs, R_VIDs, VM0) => .K ... </k>
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
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(v(VM1, VIDs)), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(VM1, VIDs), ?Epoch)))
// pre-conditions
andBool ?LastExitEpoch +Int size(R_VIDs) <Int FAR_FUTURE_EPOCH
andBool distinct(R_VIDs)
// invariants
andBool disjoint(L_VIDs, R_VIDs)
andBool forall(x, R_VIDs, x in VIDs)
andBool forall(x, R_VIDs, VM1[x]v ==K VM0[x]v)
andBool forall(x, rev(L_VIDs)          , #if isActiveValidator(VM0[x]v, ?Epoch -Int 1) andBool VM0[x]v.effective_balance <=Int EJECTION_BALANCE andBool VM0[x]v.exit_epoch ==Int FAR_FUTURE_EPOCH
                                         #then VM1[x]v.exit_epoch >=Int delayedActivationExitEpoch(?Epoch) andBool VM1[x]v.exit_epoch <Int FAR_FUTURE_EPOCH
                                               andBool countValidatorsToExit(v(VM1, VIDs), VM1[x]v.exit_epoch) <=Int ?ChurnLimit
                                         #else VM1[x]v.exit_epoch ==Int VM0[x]v.exit_epoch
                                         #fi)
ensures true
// post-conditions
andBool forall(x, rev(L_VIDs) ++ R_VIDs, #if isActiveValidator(VM0[x]v, ?Epoch -Int 1) andBool VM0[x]v.effective_balance <=Int EJECTION_BALANCE andBool VM0[x]v.exit_epoch ==Int FAR_FUTURE_EPOCH
                                         #then ?VM2[x]v.exit_epoch >=Int delayedActivationExitEpoch(?Epoch) andBool ?VM2[x]v.exit_epoch <Int FAR_FUTURE_EPOCH
                                               andBool countValidatorsToExit(v(?VM2, VIDs), ?VM2[x]v.exit_epoch) <=Int ?ChurnLimit
                                         #else ?VM2[x]v.exit_epoch ==Int VM0[x]v.exit_epoch
                                         #fi)

endmodule
