require "verification.k"

module PROCESS-REWARDS-PENALTIES-SPEC

imports VERIFICATION

rule
<T>
  <k> processRewardsPenaltiesAux(?Epoch) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM1 => ?BM2, EBM, AEM, AM, EM, WM), VIDs) </validators>
      <attested>
        ?Epoch |-> Attestations:Attestations
        ...
      </attested>
      ...
    </state>
    ...
  </states>
  <lastFinalized> ( epochOf(Slot) , LastFinalizedEpoch ) _ </lastFinalized>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
andBool ?Epoch >=Int 0
andBool ?FinalityDelay >=Int 0
// let-bindings
andBool ?Epoch ==Int epochOf(Slot) -Int 2
andBool ?FinalityDelay ==Int ?Epoch -Int LastFinalizedEpoch
andBool ?SourceAttestations ==K filterNotSlashed(SM, Attestations)
andBool ?TotalActiveBalance ==Int lift(totalBalance(EBM, activeValidators(VIDs, AM, EM, ?Epoch)))
// pre-conditions
andBool forall(x, VIDs, EBM[x]i >=Int 0)
andBool distinct(VIDs)
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).inclusion_delay >=Int 1))
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).proposer in VIDs))
andBool isValidAttestations(Attestations, VIDs, AM, EM, ?Epoch)
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, ?BM2[x]i <=Int BM1[x]i +Int (4 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)))
andBool forall(x, VIDs, ?BM2[x]i >=Int BM1[x]i -Int (7 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)) -Int getInactivityPenalty(EBM[x]i, ?FinalityDelay))

rule
<T>
  <k> processRewardsPenaltiesAux1(VIDs, m(SM, BM1, EBM, AEM, AM, EM, WM), ?Epoch, ?FinalityDelay, ?SourceAttestations, ?TargetAttestations, ?HeadAttestations) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM1 => ?BM2, EBM, AEM, AM, EM, WM), VIDs) </validators>
      <attested>
        ?Epoch |-> Attestations:Attestations
        ...
      </attested>
      ...
    </state>
    ...
  </states>
  <lastBlock> BlockMap </lastBlock>
  <lastFinalized> ( epochOf(Slot) , LastFinalizedEpoch ) _ </lastFinalized>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
andBool ?Epoch >=Int 0
andBool ?FinalityDelay >=Int 0
// let-bindings
andBool ?Epoch ==Int epochOf(Slot) -Int 2
andBool ?FinalityDelay ==Int ?Epoch -Int LastFinalizedEpoch
andBool ?SourceAttestations ==K filterNotSlashed(SM, Attestations)
andBool ?TargetAttestations ==K filterByTarget(BlockMap[firstSlotOf(?Epoch)]i, ?SourceAttestations)
andBool   ?HeadAttestations ==K filterByHead(BlockMap, ?TargetAttestations)
andBool ?SourceAttestingBalance ==Int lift(totalBalance(EBM, getUniqueValidators(?SourceAttestations)))
andBool ?TargetAttestingBalance ==Int lift(totalBalance(EBM, getUniqueValidators(?TargetAttestations)))
andBool   ?HeadAttestingBalance ==Int lift(totalBalance(EBM, getUniqueValidators(?HeadAttestations)))
andBool     ?TotalActiveBalance ==Int lift(totalBalance(EBM, activeValidators(VIDs, AM, EM, ?Epoch)))
// pre-conditions
andBool forall(x, VIDs, EBM[x]i >=Int 0)
andBool distinct(VIDs)
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).inclusion_delay >=Int 1))
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).proposer in VIDs))
andBool ?SourceAttestingBalance <=Int ?TotalActiveBalance
andBool ?TargetAttestingBalance <=Int ?TotalActiveBalance
andBool   ?HeadAttestingBalance <=Int ?TotalActiveBalance
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, ?BM2[x]i <=Int BM1[x]i +Int (4 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)))
andBool forall(x, VIDs, ?BM2[x]i >=Int BM1[x]i -Int (7 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)) -Int getInactivityPenalty(EBM[x]i, ?FinalityDelay))

rule
<T>
  <k> processRewardsPenaltiesAux2(VIDs, m(SM, BM1, EBM, AEM, AM, EM, WM), ?Epoch, ?FinalityDelay,
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
      ...
    </state>
    ...
  </states>
  <lastBlock> BlockMap </lastBlock>
  <lastFinalized> ( epochOf(Slot) , LastFinalizedEpoch ) _ </lastFinalized>
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
andBool ?SourceAttestations ==K filterNotSlashed(SM, Attestations)
andBool ?TargetAttestations ==K filterByTarget(BlockMap[firstSlotOf(?Epoch)]i, ?SourceAttestations)
andBool   ?HeadAttestations ==K filterByHead(BlockMap, ?TargetAttestations)
andBool ?SourceAttestingBalance ==Int lift(totalBalance(EBM, getUniqueValidators(?SourceAttestations)))
andBool ?TargetAttestingBalance ==Int lift(totalBalance(EBM, getUniqueValidators(?TargetAttestations)))
andBool   ?HeadAttestingBalance ==Int lift(totalBalance(EBM, getUniqueValidators(?HeadAttestations)))
andBool     ?TotalActiveBalance ==Int lift(totalBalance(EBM, activeValidators(VIDs, AM, EM, ?Epoch)))
// pre-conditions
andBool forall(x, VIDs, EBM[x]i >=Int 0)
andBool distinct(VIDs)
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).inclusion_delay >=Int 1))
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).proposer in VIDs))
andBool ?SourceAttestingBalance <=Int ?TotalActiveBalance
andBool ?TargetAttestingBalance <=Int ?TotalActiveBalance
andBool   ?HeadAttestingBalance <=Int ?TotalActiveBalance
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, ?BM2[x]i <=Int BM1[x]i +Int (4 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)))
andBool forall(x, VIDs, ?BM2[x]i >=Int BM1[x]i -Int (7 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)) -Int getInactivityPenalty(EBM[x]i, ?FinalityDelay))

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
      ...
    </state>
    ...
  </states>
  <lastBlock> BlockMap </lastBlock>
  <lastFinalized> ( epochOf(Slot) , LastFinalizedEpoch ) _ </lastFinalized>
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
andBool ?SourceAttestations ==K filterNotSlashed(SM, Attestations)
andBool ?TargetAttestations ==K filterByTarget(BlockMap[firstSlotOf(?Epoch)]i, ?SourceAttestations)
andBool   ?HeadAttestations ==K filterByHead(BlockMap, ?TargetAttestations)
andBool ?SourceAttestingBalance ==Int lift(totalBalance(EBM, getUniqueValidators(?SourceAttestations)))
andBool ?TargetAttestingBalance ==Int lift(totalBalance(EBM, getUniqueValidators(?TargetAttestations)))
andBool   ?HeadAttestingBalance ==Int lift(totalBalance(EBM, getUniqueValidators(?HeadAttestations)))
andBool     ?TotalActiveBalance ==Int lift(totalBalance(EBM, activeValidators(VIDs, AM, EM, ?Epoch)))
// pre-conditions
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
