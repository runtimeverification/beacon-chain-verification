require "../../verification.k"
require "n8-spec.k"

module N9-SPEC

imports VERIFICATION
imports N8-SPEC

rule
<T>
  <k> processRewardsPenalties(?Epoch) => .K ... </k>
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
// let-bindings
andBool ?Epoch ==Int epochOf(Slot) -Int 2
andBool ?VM1 ==K m(SM, BM1, EBM, AEM, AM, EM, WM)
andBool ?FinalityDelay ==Int ?Epoch -Int LastFinalizedEpoch
andBool ?SourceAttestations ==K filterNotSlashed(?VM1, Attestations)
andBool ?TotalActiveBalance ==Int lift(totalBalance(?VM1, activeValidators(v(?VM1, VIDs), ?Epoch)))
// pre-conditions
andBool ?Epoch >=Int 2
andBool forall(x, VIDs, EBM[x]i >=Int 0)
andBool distinct(VIDs)
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).inclusion_delay >=Int 1))
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).proposer in VIDs))
andBool isValidAttestations(Attestations, v(?VM1, VIDs), ?Epoch)
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
// let-bindings
andBool ?Epoch ==Int epochOf(Slot) -Int 2
andBool ?VM1 ==K m(SM, BM1, EBM, AEM, AM, EM, WM)
andBool ?FinalityDelay ==Int ?Epoch -Int LastFinalizedEpoch
andBool ?SourceAttestations ==K filterNotSlashed(?VM1, Attestations)
andBool ?TargetAttestations ==K filterByTarget(EpochBoundaryBlock, ?SourceAttestations)
andBool   ?HeadAttestations ==K filterByHead(BM, ?TargetAttestations)
andBool ?SourceAttestingBalance ==Int lift(totalBalance(?VM1, getValidators(?SourceAttestations)))
andBool ?TargetAttestingBalance ==Int lift(totalBalance(?VM1, getValidators(?TargetAttestations)))
andBool   ?HeadAttestingBalance ==Int lift(totalBalance(?VM1, getValidators(?HeadAttestations)))
andBool     ?TotalActiveBalance ==Int lift(totalBalance(?VM1, activeValidators(v(?VM1, VIDs), ?Epoch)))
// pre-conditions
andBool ?Epoch >=Int 2
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
andBool ?VM1 ==K m(SM, BM1, EBM, AEM, AM, EM, WM)
andBool ?FinalityDelay ==Int ?Epoch -Int LastFinalizedEpoch
andBool ?SourceAttestations ==K filterNotSlashed(?VM1, Attestations)
andBool ?TargetAttestations ==K filterByTarget(EpochBoundaryBlock, ?SourceAttestations)
andBool   ?HeadAttestations ==K filterByHead(BM, ?TargetAttestations)
andBool ?SourceAttestingBalance ==Int lift(totalBalance(?VM1, getValidators(?SourceAttestations)))
andBool ?TargetAttestingBalance ==Int lift(totalBalance(?VM1, getValidators(?TargetAttestations)))
andBool   ?HeadAttestingBalance ==Int lift(totalBalance(?VM1, getValidators(?HeadAttestations)))
andBool     ?TotalActiveBalance ==Int lift(totalBalance(?VM1, activeValidators(v(?VM1, VIDs), ?Epoch)))
// pre-conditions
andBool ?Epoch >=Int 2
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

endmodule
