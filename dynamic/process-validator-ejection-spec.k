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
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(VIDs, AM, EM1, ?Epoch)))
// pre-conditions
andBool ?LastExitEpoch +Int size(VIDs) <Int FAR_FUTURE_EPOCH
andBool distinct(VIDs)
andBool ?Epoch <Int FAR_FUTURE_EPOCH
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, #if isActiveValidator(x, AM, EM1, ?Epoch -Int 1) andBool EBM[x]i <=Int EJECTION_BALANCE andBool EM1[x]i ==Int FAR_FUTURE_EPOCH
                        #then ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH
                              andBool countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit
                        #else ?EM2[x]i ==Int EM1[x]i
                        #fi)
// rely-guarantee conditions
andBool activeValidators(VIDs, AM, ?EM2, ?Epoch -Int 1) ==K activeValidators(VIDs, AM, EM1, ?Epoch -Int 1)

rule
<T>
  <k> processValidatorEjectionsAux(L_VIDs, R_VIDs, m(SM, BM, EBM, AEM, AM, EM0, WM0)) => .K ... </k>
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
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(VIDs, AM, EM1, ?Epoch)))
// pre-conditions
andBool ?LastExitEpoch +Int size(R_VIDs) <Int FAR_FUTURE_EPOCH
andBool distinct(R_VIDs)
andBool ?Epoch <Int FAR_FUTURE_EPOCH
// invariants
andBool disjoint(L_VIDs, R_VIDs)
andBool forall(x, R_VIDs, x in VIDs)
andBool forall(x, R_VIDs, EM1[x]i ==K EM0[x]i)
andBool forall(x, R_VIDs, WM1[x]i ==K WM0[x]i)
andBool forall(x, rev(L_VIDs)          , #if isActiveValidator(x, AM, EM0, ?Epoch -Int 1) andBool EBM[x]i <=Int EJECTION_BALANCE andBool EM0[x]i ==Int FAR_FUTURE_EPOCH
                                         #then EM1[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool EM1[x]i <Int FAR_FUTURE_EPOCH
                                               andBool countValidatorsToExit(VIDs, EM1, EM1[x]i) <=Int ?ChurnLimit
                                         #else EM1[x]i ==Int EM0[x]i
                                         #fi)
andBool activeValidators(VIDs, AM,  EM1, ?Epoch -Int 1) ==K activeValidators(VIDs, AM, EM0, ?Epoch -Int 1)
ensures true
// post-conditions
andBool forall(x, rev(L_VIDs) ++ R_VIDs, #if isActiveValidator(x, AM, EM0, ?Epoch -Int 1) andBool EBM[x]i <=Int EJECTION_BALANCE andBool EM0[x]i ==Int FAR_FUTURE_EPOCH
                                         #then ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH
                                               andBool countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit
                                         #else ?EM2[x]i ==Int EM0[x]i
                                         #fi)
// rely-guarantee conditions
andBool activeValidators(VIDs, AM, ?EM2, ?Epoch -Int 1) ==K activeValidators(VIDs, AM, EM0, ?Epoch -Int 1)

endmodule
