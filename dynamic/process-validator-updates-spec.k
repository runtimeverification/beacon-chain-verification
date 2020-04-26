require "verification.k"

module PROCESS-VALIDATOR-UPDATES-SPEC

imports VERIFICATION

rule
<T>
  <k> processValidatorUpdates() => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM, EBM, AEM1 => ?AEM2, AM1 => ?AM2, EM1 => ?EM2, WM1 => ?WM2), VIDs) </validators>
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
andBool ?Epoch ==Int epochOf(Slot)
andBool ?VM1 ==K m(SM, BM, EBM, AEM1, AM1, EM1, WM1)
andBool ?ChurnLimitA ==Int churnLimit(size(activeValidators(v(?VM1, VIDs), ?Epoch)))
andBool ?ChurnLimitB ==Int churnLimit(size(activeValidators(v(?VM1, VIDs), ?Epoch -Int 1)))
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ActivationEpoch ==Int delayedActivationExitEpoch(?Epoch -Int 1)
andBool ?ValidatorsToBeActivated ==K activationQueueUptoChurnLimit(v(?VM1, VIDs), FinalizedEpoch, ?Epoch -Int 1)
// pre-conditions
andBool distinct(VIDs)
andBool ?LastExitEpoch +Int size(VIDs) <Int FAR_FUTURE_EPOCH
andBool ?ActivationEpoch <Int FAR_FUTURE_EPOCH
andBool countValidatorsToActivate(VIDs, AM1, ?ActivationEpoch) ==Int 0
// invariants
ensures true
// post-conditions
// processValidatorEjections 
andBool forall(x, VIDs, #if isActiveValidator(x, ?VM1, ?Epoch -Int 1) andBool EBM[x]i <=Int EJECTION_BALANCE andBool EM1[x]i ==Int FAR_FUTURE_EPOCH
                        #then ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH
                              andBool countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimitA
                        #else ?EM2[x]i ==Int EM1[x]i
                        #fi)
// updateActivationEligibilities
andBool forall(x, VIDs, ?AEM2[x]i ==Int #if isActivationEligible(x, ?VM1) #then ?Epoch #else AEM1[x]i #fi)
// processValidatorActivation
andBool forall(x, ?ValidatorsToBeActivated, ?AM2[x]i ==Int ?ActivationEpoch)
andBool countValidatorsToActivate(VIDs, ?AM2, ?ActivationEpoch) <=Int ?ChurnLimitB



rule
<T>
  <k> processValidatorEjections(VIDs) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM, EBM, AEM, AM, EM1 => ?EM2, WM1 => ?WM2), VIDs) </validators>
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
andBool ?VM1 ==K m(SM, BM, EBM, AEM, AM, EM1, WM1)
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(?VM1, VIDs), ?Epoch)))
// pre-conditions
andBool ?LastExitEpoch +Int size(VIDs) <Int FAR_FUTURE_EPOCH
andBool distinct(VIDs)
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, #if isActiveValidator(x, ?VM1, ?Epoch -Int 1) andBool EBM[x]i <=Int EJECTION_BALANCE andBool EM1[x]i ==Int FAR_FUTURE_EPOCH
                        #then ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH
                              andBool countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit
                        #else ?EM2[x]i ==Int EM1[x]i
                        #fi)
// TODO: activeValidators is preserved
andBool activeValidators(v(?VM1, VIDs), ?Epoch -Int 1) ==K activeValidators(v(m(SM, BM, EBM, AEM, AM, ?EM2, ?WM2), VIDs), ?Epoch -Int 1)
[trusted]

rule
<T>
  <k> updateActivationEligibilities(VIDs) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM, EBM, AEM1 => ?AEM2, AM, EM, WM), VIDs) </validators>
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
andBool ?Epoch ==Int epochOf(Slot)
andBool ?VM1 ==K m(SM, BM, EBM, AEM1, AM, EM, WM)
// pre-conditions
andBool distinct(VIDs)
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, ?AEM2[x]i ==Int #if isActivationEligible(x, ?VM1) #then ?Epoch #else AEM1[x]i #fi)
// TODO: activationQueue is preserved
andBool activationQueue(v(?VM1, VIDs), FinalizedEpoch) ==K activationQueue(v(m(SM, BM, EBM, ?AEM2, AM, EM, WM), VIDs), FinalizedEpoch)
[trusted]


rule
<T>
  <k> processValidatorActivation() => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM, EBM, AEM, AM1 => ?AM2, EM, WM), VIDs) </validators>
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
andBool ?VM1 ==K m(SM, BM, EBM, AEM, AM1, EM, WM)
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(?VM1, VIDs), ?Epoch)))
andBool ?ActivationEpoch ==Int delayedActivationExitEpoch(?Epoch)
andBool ?ValidatorsToBeActivated ==K activationQueueUptoChurnLimit(v(?VM1, VIDs), FinalizedEpoch, ?Epoch)
// pre-conditions
andBool distinct(VIDs)
andBool ?ActivationEpoch <Int FAR_FUTURE_EPOCH
andBool countValidatorsToActivate(VIDs, AM1, ?ActivationEpoch) ==Int 0
// invariants
ensures true
// post-conditions
andBool forall(x, ?ValidatorsToBeActivated, ?AM2[x]i ==Int ?ActivationEpoch)
andBool countValidatorsToActivate(VIDs, ?AM2, ?ActivationEpoch) <=Int ?ChurnLimit
[trusted]

endmodule
