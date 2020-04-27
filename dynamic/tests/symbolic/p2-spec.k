require "../../verification.k"
require "p1-spec.k"

module P2-SPEC

imports VERIFICATION
imports P1-SPEC

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
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(v(?VM1, VIDs)), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(v(?VM1, VIDs), ?Epoch)))
// pre-conditions
andBool ?LastExitEpoch +Int size(VIDs) <Int FAR_FUTURE_EPOCH
andBool distinct(VIDs)
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, #if isActiveValidator(x, ?VM1, ?Epoch -Int 1) andBool EBM[x]i <=Int EJECTION_BALANCE andBool EM1[x]i ==Int FAR_FUTURE_EPOCH
                        #then ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH
                              andBool countValidatorsToExit(v(m(SM, BM, EBM, AEM, AM, ?EM2, ?WM2), VIDs), ?EM2[x]i) <=Int ?ChurnLimit
                        #else ?EM2[x]i ==Int EM1[x]i
                        #fi)

endmodule
