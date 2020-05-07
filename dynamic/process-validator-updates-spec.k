require "verification.k"
require "process-validator-ejection-spec.k"
require "process-validator-activation-eligibility-spec.k"
require "process-validator-activation-spec.k"

module PROCESS-VALIDATOR-UPDATES-SPEC

imports VERIFICATION

imports PROCESS-VALIDATOR-EJECTION-SPEC
imports PROCESS-VALIDATOR-ACTIVATION-ELIGIBILITY-SPEC
imports PROCESS-VALIDATOR-ACTIVATION-SPEC

rule
<T>
  <k> processValidatorUpdates() => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM, EBM, AEM1 => ?AEM2, AM1 => ?AM2, EM1 => ?EM2, WM1 => ?WM2), VIDs) </validators>
      ...
    </state>
    ...
  </states>
  <lastFinalized> ( epochOf(Slot) , FinalizedEpoch ) _ </lastFinalized>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
// let-bindings
andBool ?Epoch ==Int epochOf(Slot)
andBool ?ChurnLimitA ==Int churnLimit(size(activeValidators(VIDs, AM1, EM1, ?Epoch)))
andBool ?ChurnLimitB ==Int churnLimit(size(activeValidators(VIDs, AM1, EM1, ?Epoch -Int 1)))
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ActivationEpoch ==Int delayedActivationExitEpoch(?Epoch -Int 1)
andBool ?ValidatorsToBeActivated ==K activationQueueUptoChurnLimit(VIDs, AEM1, AM1, EM1, FinalizedEpoch, ?Epoch -Int 1)
// pre-conditions
andBool distinct(VIDs)
andBool FinalizedEpoch <Int FAR_FUTURE_EPOCH
andBool FinalizedEpoch <Int ?Epoch
andBool ?LastExitEpoch +Int size(VIDs) +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY <Int FAR_FUTURE_EPOCH
andBool ?ActivationEpoch <Int FAR_FUTURE_EPOCH
andBool countValidatorsToActivate(VIDs, AM1, ?ActivationEpoch) ==Int 0
// invariants
ensures true
// post-conditions
// processValidatorEjections 
andBool forall(x, VIDs, #if isActiveValidator(x, AM1, EM1, ?Epoch -Int 1) andBool EBM[x]i <=Int EJECTION_BALANCE andBool EM1[x]i ==Int FAR_FUTURE_EPOCH
                        #then countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimitA
                              andBool ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch)                                          andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH
                              andBool ?WM2[x]i >=Int delayedActivationExitEpoch(?Epoch) +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY andBool ?WM2[x]i <Int FAR_FUTURE_EPOCH
                        #else         ?EM2[x]i ==Int EM1[x]i
                              andBool ?WM2[x]i ==Int WM1[x]i
                        #fi)
// updateActivationEligibilities
andBool forall(x, VIDs, ?AEM2[x]i ==Int #if isActivationEligible(x, AEM1, EBM) #then ?Epoch #else AEM1[x]i #fi)
// processValidatorActivation
andBool forall(x, ?ValidatorsToBeActivated, ?AM2[x]i ==Int ?ActivationEpoch)
andBool countValidatorsToActivate(VIDs, ?AM2, ?ActivationEpoch) <=Int ?ChurnLimitB

endmodule
