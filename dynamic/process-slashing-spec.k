require "verification.k"

module PROCESS-SLASHING-SPEC

imports VERIFICATION

rule
<T>
  <k> processSlashings(Ss) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM1 => ?SM2, BM1 => ?BM2, EBM, AEM, AM, EM1 => ?EM2, WM1 => ?WM2), VIDs) </validators>
      <slashedBalance> _ => ?_ </slashedBalance>
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
andBool ?LastExitEpoch +Int sizeS(Ss) <Int FAR_FUTURE_EPOCH
andBool forallS(x, Ss, isSlashableAttestation(x.attestation_1, x.attestation_2) andBool x.attestation_1.attester ==Int x.attestation_2.attester)
andBool forall(x, getValidatorsS(Ss), SM1[x]b ==K false)
andBool distinct(getValidatorsS(Ss))
andBool forall(x, getValidatorsS(Ss), x in VIDs)
andBool ?Epoch <Int FAR_FUTURE_EPOCH
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, implies(notBool x in getValidatorsS(Ss), ?SM2[x]b ==K SM1[x]b))
andBool forall(x, VIDs, implies(notBool x in getValidatorsS(Ss), ?BM2[x]i ==K BM1[x]i))
andBool forall(x, VIDs, implies(notBool x in getValidatorsS(Ss), ?EM2[x]i ==K EM1[x]i))
andBool forall(x, VIDs, implies(notBool x in getValidatorsS(Ss), ?WM2[x]i ==K WM1[x]i))
andBool forall(x, getValidatorsS(Ss), ?SM2[x]b ==K true)
andBool forall(x, getValidatorsS(Ss), #if EM1[x]i ==Int FAR_FUTURE_EPOCH
                                      #then ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH
                                            andBool countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit
                                      #else ?EM2[x]i ==Int EM1[x]i
                                      #fi)

rule
<T>
  <k> processSlashingsAux(L_VIDs, R_Ss, m(SM0, BM0, EBM, AEM, AM, EM0, WM0)) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM1 => ?SM2, BM1 => ?BM2, EBM, AEM, AM, EM1 => ?EM2, WM1 => ?WM2), VIDs) </validators>
      <slashedBalance> _ => ?_ </slashedBalance>
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
andBool ?LastExitEpoch +Int sizeS(R_Ss) <Int FAR_FUTURE_EPOCH
andBool forallS(x, R_Ss, isSlashableAttestation(x.attestation_1, x.attestation_2) andBool x.attestation_1.attester ==Int x.attestation_2.attester)
andBool forall(x, getValidatorsS(R_Ss), SM1[x]b ==K false)
andBool distinct(getValidatorsS(R_Ss))
andBool forall(x, getValidatorsS(R_Ss), x in VIDs)
andBool ?Epoch <Int FAR_FUTURE_EPOCH
// invariants
andBool disjoint(L_VIDs, getValidatorsS(R_Ss))
andBool forall(x, getValidatorsS(R_Ss), SM1[x]b ==K SM0[x]b)
andBool forall(x, getValidatorsS(R_Ss), BM1[x]i ==K BM0[x]i)
andBool forall(x, getValidatorsS(R_Ss), EM1[x]i ==K EM0[x]i)
andBool forall(x, getValidatorsS(R_Ss), WM1[x]i ==K WM0[x]i)
andBool forall(x, VIDs, implies(notBool x in rev(L_VIDs)                      , SM1[x]b ==K SM0[x]b))
andBool forall(x, VIDs, implies(notBool x in rev(L_VIDs)                      , BM1[x]i ==K BM0[x]i))
andBool forall(x, VIDs, implies(notBool x in rev(L_VIDs)                      , EM1[x]i ==K EM0[x]i))
andBool forall(x, VIDs, implies(notBool x in rev(L_VIDs)                      , WM1[x]i ==K WM0[x]i))
andBool forall(x, rev(L_VIDs)                         , SM1[x]b ==K true)
andBool forall(x, rev(L_VIDs)                         , #if EM0[x]i ==Int FAR_FUTURE_EPOCH
                                                        #then EM1[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool EM1[x]i <Int FAR_FUTURE_EPOCH
                                                              andBool countValidatorsToExit(VIDs, EM1, EM1[x]i) <=Int ?ChurnLimit
                                                        #else EM1[x]i ==Int EM0[x]i
                                                        #fi)
ensures true
// post-conditions
andBool forall(x, VIDs, implies(notBool x in rev(L_VIDs) ++ getValidatorsS(R_Ss), ?SM2[x]b ==K SM0[x]b))
andBool forall(x, VIDs, implies(notBool x in rev(L_VIDs) ++ getValidatorsS(R_Ss), ?BM2[x]i ==K BM0[x]i))
andBool forall(x, VIDs, implies(notBool x in rev(L_VIDs) ++ getValidatorsS(R_Ss), ?EM2[x]i ==K EM0[x]i))
andBool forall(x, VIDs, implies(notBool x in rev(L_VIDs) ++ getValidatorsS(R_Ss), ?WM2[x]i ==K WM0[x]i))
andBool forall(x, rev(L_VIDs) ++ getValidatorsS(R_Ss), ?SM2[x]b ==K true)
andBool forall(x, rev(L_VIDs) ++ getValidatorsS(R_Ss), #if EM0[x]i ==Int FAR_FUTURE_EPOCH
                                                       #then ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH
                                                             andBool countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit
                                                       #else ?EM2[x]i ==Int EM0[x]i
                                                       #fi)
[trusted]

endmodule
