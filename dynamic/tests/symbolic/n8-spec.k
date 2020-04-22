require "../../verification.k"

module N8-SPEC

imports VERIFICATION

rule
<T>
  <k> processRewardsPenaltiesAux3(L_VIDs, R_VIDs, VM0, ?Epoch, ?FinalityDelay,
        ?SourceAttestations,     ?TargetAttestations,     ?HeadAttestations,
        ?SourceAttestingBalance, ?TargetAttestingBalance, ?HeadAttestingBalance, ?TotalActiveBalance) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(VM1 => ?VM2, VIDs) </validators>
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
andBool ?FinalityDelay ==Int ?Epoch -Int LastFinalizedEpoch
andBool ?SourceAttestations ==K filterNotSlashed(VM0, Attestations)
andBool ?TargetAttestations ==K filterByTarget(EpochBoundaryBlock, ?SourceAttestations)
andBool   ?HeadAttestations ==K filterByHead(BM, ?TargetAttestations)
andBool ?SourceAttestingBalance ==Int lift(totalBalance(VM0, getValidators(?SourceAttestations)))
andBool ?TargetAttestingBalance ==Int lift(totalBalance(VM0, getValidators(?TargetAttestations)))
andBool   ?HeadAttestingBalance ==Int lift(totalBalance(VM0, getValidators(?HeadAttestations)))
andBool     ?TotalActiveBalance ==Int lift(totalBalance(VM0, activeValidators(v(VM0,VIDs), ?Epoch)))
// conditions
andBool ?Epoch >=Int 2
andBool forall(x, rev(L_VIDs), VM1[x]v.balance <=Int VM0[x]v.balance +Int (4 *Int getBaseReward(VM0[x]v.effective_balance, ?TotalActiveBalance)))
andBool forall(x, rev(L_VIDs), VM1[x]v.balance >=Int VM0[x]v.balance -Int (7 *Int getBaseReward(VM0[x]v.effective_balance, ?TotalActiveBalance)) -Int getInactivityPenalty(VM0[x]v.effective_balance, ?FinalityDelay))
// invariants
andBool distinct(R_VIDs)
andBool disjoint(L_VIDs, R_VIDs)
andBool forall(x, R_VIDs, VM1[x]v.balance ==Int VM0[x]v.balance)
andBool ?SourceAttestingBalance <=Int ?TotalActiveBalance
andBool ?TargetAttestingBalance <=Int ?TotalActiveBalance
andBool   ?HeadAttestingBalance <=Int ?TotalActiveBalance
andBool forall(x, R_VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).inclusion_delay >=Int 1))
// consistency conditions
andBool forall(x, R_VIDs, x in VIDs)
andBool forall(x, R_VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).proposer in VIDs))
ensures true
// ensures
andBool forall(x, rev(L_VIDs) ++ R_VIDs, ?VM2[x]v.balance <=Int VM0[x]v.balance +Int (4 *Int getBaseReward(VM0[x]v.effective_balance, ?TotalActiveBalance)))
andBool forall(x, rev(L_VIDs) ++ R_VIDs, ?VM2[x]v.balance >=Int VM0[x]v.balance -Int (7 *Int getBaseReward(VM0[x]v.effective_balance, ?TotalActiveBalance)) -Int getInactivityPenalty(VM0[x]v.effective_balance, ?FinalityDelay))

endmodule
