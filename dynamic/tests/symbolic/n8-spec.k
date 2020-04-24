require "../../verification.k"

module N8-SPEC

imports VERIFICATION

rule
<T>
  <k> processRewardsPenaltiesAux3(L_VIDs, R_VIDs, m(SM, BM0, EBM, AEM, AM, EM, WM), ?Epoch, ?FinalityDelay,
        ?SourceAttestations,     ?TargetAttestations,     ?HeadAttestations,
        ?SourceAttestingBalance, ?TargetAttestingBalance, ?HeadAttestingBalance, ?TotalActiveBalance) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM1 => ?BM2, EBM, AEM, AM, EM, WM), VIDs) </validators>
      <attested>
        ?Epoch |-> Attestations:Attestations
        ...
      </attested>
      <lastFinalized> LastFinalizedEpoch </lastFinalized>
      ...
    </state>
    <state>
      <slot> firstSlotOf(?Epoch) </slot>
      <lastBlock> (_, EpochBoundaryBlock) </lastBlock>
      ...
    </state>
    ...
  </states>
  <blocks> BM </blocks>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
andBool ?Epoch >=Int 0
andBool ?FinalityDelay >=Int 0
andBool ?SourceAttestingBalance >=Int 0
andBool ?TargetAttestingBalance >=Int 0
andBool   ?HeadAttestingBalance >=Int 0
andBool     ?TotalActiveBalance >=Int 0
// let-bindings
andBool ?Epoch ==Int epochOf(Slot) -Int 2
andBool ?VM0 ==K m(SM, BM0, EBM, AEM, AM, EM, WM)
andBool ?VM1 ==K m(SM, BM1, EBM, AEM, AM, EM, WM)
andBool ?FinalityDelay ==Int ?Epoch -Int LastFinalizedEpoch
andBool ?SourceAttestations ==K filterNotSlashed(?VM0, Attestations)
andBool ?TargetAttestations ==K filterByTarget(EpochBoundaryBlock, ?SourceAttestations)
andBool   ?HeadAttestations ==K filterByHead(BM, ?TargetAttestations)
andBool ?SourceAttestingBalance ==Int lift(totalBalance(?VM0, getValidators(?SourceAttestations)))
andBool ?TargetAttestingBalance ==Int lift(totalBalance(?VM0, getValidators(?TargetAttestations)))
andBool   ?HeadAttestingBalance ==Int lift(totalBalance(?VM0, getValidators(?HeadAttestations)))
andBool     ?TotalActiveBalance ==Int lift(totalBalance(?VM0, activeValidators(v(?VM0, VIDs), ?Epoch)))
// pre-conditions
andBool ?Epoch >=Int 2
andBool forall(x, R_VIDs, EBM[x]i >=Int 0)
andBool distinct(R_VIDs)
andBool forall(x, R_VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).inclusion_delay >=Int 1))
andBool forall(x, R_VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).proposer in VIDs))
andBool ?SourceAttestingBalance <=Int ?TotalActiveBalance
andBool ?TargetAttestingBalance <=Int ?TotalActiveBalance
andBool   ?HeadAttestingBalance <=Int ?TotalActiveBalance
// invariants
andBool disjoint(L_VIDs, R_VIDs)
andBool forall(x, R_VIDs, x in VIDs)
andBool forall(x, R_VIDs, BM1[x]i ==Int BM0[x]i)
andBool forall(x, rev(L_VIDs),            BM1[x]i <=Int BM0[x]i +Int (4 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)))
andBool forall(x, rev(L_VIDs),            BM1[x]i >=Int BM0[x]i -Int (7 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)) -Int getInactivityPenalty(EBM[x]i, ?FinalityDelay))
ensures true
// post-conditions
andBool forall(x, rev(L_VIDs) ++ R_VIDs, ?BM2[x]i <=Int BM0[x]i +Int (4 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)))
andBool forall(x, rev(L_VIDs) ++ R_VIDs, ?BM2[x]i >=Int BM0[x]i -Int (7 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)) -Int getInactivityPenalty(EBM[x]i, ?FinalityDelay))

endmodule
