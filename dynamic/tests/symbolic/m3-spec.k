require "../../verification.k"

module M3-SPEC

imports VERIFICATION

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
andBool countValidatorsToActivate(v(?VM1, VIDs), ?ActivationEpoch) ==Int 0
// invariants
ensures true
// post-conditions
andBool forall(x, ?ValidatorsToBeActivated, ?AM2[x]i ==Int ?ActivationEpoch)
andBool countValidatorsToActivate(v(m(SM, BM, EBM, AEM, ?AM2, EM, WM), VIDs), ?ActivationEpoch) <=Int ?ChurnLimit

rule
<T>
  <k> activateValidators(R_VIDs) => .K ... </k>
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
// pre-conditions
andBool distinct(R_VIDs)
andBool forall(x, R_VIDs, isValidValidatorToActivate(x, ?VM1, FinalizedEpoch))
andBool forall(x, R_VIDs, x in VIDs)
andBool ?ActivationEpoch <Int FAR_FUTURE_EPOCH
andBool countValidatorsToActivate(v(?VM1, VIDs), ?ActivationEpoch) +Int size(R_VIDs) <=Int ?ChurnLimit
// invariants
ensures true
// post-conditions
andBool forall(x, R_VIDs, ?AM2[x]i ==Int ?ActivationEpoch)
andBool countValidatorsToActivate(v(m(SM, BM, EBM, AEM, ?AM2, EM, WM), VIDs), ?ActivationEpoch) <=Int ?ChurnLimit

rule
<T>
  <k> activateValidatorsAux(L_VIDs, R_VIDs, m(SM, BM, EBM, AEM, AM0, EM, WM)) => .K ... </k>
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
andBool ?VM0 ==K m(SM, BM, EBM, AEM, AM0, EM, WM)
andBool ?VM1 ==K m(SM, BM, EBM, AEM, AM1, EM, WM)
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(?VM1, VIDs), ?Epoch)))
andBool ?ActivationEpoch ==Int delayedActivationExitEpoch(?Epoch)
// pre-conditions
andBool distinct(R_VIDs)
andBool ?ActivationEpoch <Int FAR_FUTURE_EPOCH
andBool forall(x, R_VIDs, isValidValidatorToActivate(x, ?VM0, FinalizedEpoch))
andBool forall(x, R_VIDs, x in VIDs)
andBool countValidatorsToActivate(v(?VM1, VIDs), ?ActivationEpoch) +Int size(R_VIDs) <=Int ?ChurnLimit
// invariants
andBool disjoint(L_VIDs, R_VIDs)
andBool forall(x, R_VIDs, AM1[x]i ==K AM0[x]i)
andBool forall(x, rev(L_VIDs)          ,  AM1[x]i ==Int ?ActivationEpoch)
ensures true
// post-conditions
andBool forall(x, rev(L_VIDs) ++ R_VIDs, ?AM2[x]i ==Int ?ActivationEpoch)
andBool countValidatorsToActivate(v(m(SM, BM, EBM, AEM, ?AM2, EM, WM), VIDs), ?ActivationEpoch) <=Int ?ChurnLimit

endmodule
