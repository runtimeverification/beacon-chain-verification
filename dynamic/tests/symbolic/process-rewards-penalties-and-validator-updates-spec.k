require "verification.k"
require "process-rewards-penalties-spec.k"
require "process-validator-updates-spec.k"

module PROCESS-REWARDS-PENALTIES-AND-VALIDATOR-UPDATES-SPEC

imports VERIFICATION

imports PROCESS-REWARDS-PENALTIES-SPEC
imports PROCESS-VALIDATOR-UPDATES-SPEC

rule
<T>
  <k> begin
   ~> processRewardsPenalties(?Epoch -Int 2)
   ~> processValidatorUpdates() => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM1 => ?BM2, EBM, AEM1 => ?AEM2, AM1 => ?AM2, EM1 => ?EM2, WM1 => ?WM2), VIDs) </validators>
      <attested>
        ?Epoch -Int 2 |-> Attestations:Attestations
        ...
      </attested>
      <lastFinalized> LastFinalizedEpoch </lastFinalized>
      ...
    </state>
    <state>
      <slot> firstSlotOf(?Epoch -Int 2) </slot>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
andBool ?Epoch >=Int 0
andBool ?FinalityDelay >=Int 0
// let-bindings
andBool ?Epoch ==Int epochOf(Slot)
andBool ?FinalityDelay ==Int ?Epoch -Int 2 -Int LastFinalizedEpoch
andBool ?SourceAttestations ==K filterNotSlashed(SM, Attestations)
andBool ?TotalActiveBalance ==Int lift(totalBalance(EBM, activeValidators(VIDs, AM1, EM1, ?Epoch -Int 2)))
//
andBool ?ChurnLimitA ==Int churnLimit(size(activeValidators(VIDs, AM1, EM1, ?Epoch)))
andBool ?ChurnLimitB ==Int churnLimit(size(activeValidators(VIDs, AM1, EM1, ?Epoch -Int 1)))
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ActivationEpoch ==Int delayedActivationExitEpoch(?Epoch -Int 1)
andBool ?ValidatorsToBeActivated ==K activationQueueUptoChurnLimit(VIDs, AEM1, AM1, EM1, LastFinalizedEpoch, ?Epoch -Int 1)
// pre-conditions
andBool ?Epoch >=Int 4
andBool forall(x, VIDs, EBM[x]i >=Int 0)
andBool distinct(VIDs)
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).inclusion_delay >=Int 1))
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).proposer in VIDs))
andBool isValidAttestations(Attestations, VIDs, AM1, EM1, ?Epoch -Int 2)
//
andBool LastFinalizedEpoch <Int FAR_FUTURE_EPOCH
andBool LastFinalizedEpoch <Int ?Epoch
andBool ?LastExitEpoch +Int size(VIDs) <Int FAR_FUTURE_EPOCH
andBool ?ActivationEpoch <Int FAR_FUTURE_EPOCH
andBool countValidatorsToActivate(VIDs, AM1, ?ActivationEpoch) ==Int 0
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, ?BM2[x]i <=Int BM1[x]i +Int (4 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)))
andBool forall(x, VIDs, ?BM2[x]i >=Int BM1[x]i -Int (7 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)) -Int getInactivityPenalty(EBM[x]i, ?FinalityDelay))
//
// processValidatorEjections 
andBool forall(x, VIDs, #if isActiveValidator(x, AM1, EM1, ?Epoch -Int 1) andBool EBM[x]i <=Int EJECTION_BALANCE andBool EM1[x]i ==Int FAR_FUTURE_EPOCH
                        #then ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH
                              andBool countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimitA
                        #else ?EM2[x]i ==Int EM1[x]i
                        #fi)
// updateActivationEligibilities
andBool forall(x, VIDs, ?AEM2[x]i ==Int #if isActivationEligible(x, AEM1, EBM) #then ?Epoch #else AEM1[x]i #fi)
// processValidatorActivation
andBool forall(x, ?ValidatorsToBeActivated, ?AM2[x]i ==Int ?ActivationEpoch)
andBool countValidatorsToActivate(VIDs, ?AM2, ?ActivationEpoch) <=Int ?ChurnLimitB

endmodule
