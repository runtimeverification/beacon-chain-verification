require "../../verification.k"

module N7-SPEC

imports VERIFICATION

rule
<T>
  <k> processRewardPenalty(VID, m(SM, BM1, EBM, AEM, AM, EM, WM), ?Epoch, ?FinalityDelay, ?BaseReward,
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

andBool implies(VID inA ?SourceAttestations, VID =/=Int minByInclusionDelay(VID, ?SourceAttestations).proposer)

// types
andBool Slot >=Int 0
andBool ?Epoch >=Int 0
andBool ?FinalityDelay >=Int 0
andBool ?BaseReward >=Int 0
andBool ?SourceAttestingBalance >=Int 0
andBool ?TargetAttestingBalance >=Int 0
andBool   ?HeadAttestingBalance >=Int 0
andBool     ?TotalActiveBalance >=Int 0
// let-bindings
andBool ?Epoch ==Int epochOf(Slot) -Int 2
andBool ?VM1 ==K m(SM, BM1, EBM, AEM, AM, EM, WM)
andBool ?FinalityDelay ==Int ?Epoch -Int LastFinalizedEpoch
andBool ?BaseReward ==Int getBaseReward(EBM[VID]i, ?TotalActiveBalance)
andBool ?SourceAttestations ==K filterNotSlashed(?VM1, Attestations)
andBool ?TargetAttestations ==K filterByTarget(EpochBoundaryBlock, ?SourceAttestations)
andBool   ?HeadAttestations ==K filterByHead(BM, ?TargetAttestations)
andBool ?SourceAttestingBalance ==Int lift(totalBalance(?VM1, getValidators(?SourceAttestations)))
andBool ?TargetAttestingBalance ==Int lift(totalBalance(?VM1, getValidators(?TargetAttestations)))
andBool   ?HeadAttestingBalance ==Int lift(totalBalance(?VM1, getValidators(?HeadAttestations)))
andBool     ?TotalActiveBalance ==Int lift(totalBalance(?VM1, activeValidators(v(?VM1, VIDs), ?Epoch)))
// pre-conditions
andBool ?Epoch >=Int 2
andBool EBM[VID]i >=Int 0
andBool implies(VID inA ?SourceAttestations, minByInclusionDelay(VID, ?SourceAttestations).inclusion_delay >=Int 1)
andBool implies(VID inA ?SourceAttestations, minByInclusionDelay(VID, ?SourceAttestations).proposer in VIDs)
andBool ?SourceAttestingBalance <=Int ?TotalActiveBalance
andBool ?TargetAttestingBalance <=Int ?TotalActiveBalance
andBool   ?HeadAttestingBalance <=Int ?TotalActiveBalance
andBool VID in VIDs // andBool VM1[V.id]v ==K V
ensures true
// ensures

andBool implies(
          notBool ( isActiveValidator(VID, ?VM1, ?Epoch) orBool ( SM[VID]b andBool ?Epoch +Int 1 <Int WM[VID]i ) )
        ,
          ?BM2 ==K BM1
        )

andBool implies(
          isActiveValidator(VID, ?VM1, ?Epoch) orBool ( SM[VID]b andBool ?Epoch +Int 1 <Int WM[VID]i )
        ,
          implies(
            // active case
            ?FinalityDelay <=Int MIN_EPOCHS_TO_INACTIVITY_PENALTY
          ,
            // max: + 4 * BaseReward
            ?BM2[VID]i <=Int BM1[VID]i +Int (4 *Int ?BaseReward)
          andBool
            // min: - 3 * BaseReward
            ?BM2[VID]i >=Int BM1[VID]i -Int (3 *Int ?BaseReward)
          )
        andBool
          implies(
            // inactive case
            ?FinalityDelay >Int MIN_EPOCHS_TO_INACTIVITY_PENALTY
          ,
            // max: + 0
            ?BM2[VID]i <=Int BM1[VID]i
          andBool
            // min: - 7 * BaseReward - (EffectiveBalance * FinalityDelay / 33,554,432)
            ?BM2[VID]i >=Int BM1[VID]i -Int (7 *Int ?BaseReward) -Int getInactivityPenalty(EBM[VID]i, ?FinalityDelay)
          )
        )

// max: + 4 * BaseReward
andBool ?BM2[VID]i <=Int BM1[VID]i +Int (4 *Int ?BaseReward)

// min: - 7 * BaseReward - (EffectiveBalance * FinalityDelay / 33,554,432)
andBool ?BM2[VID]i >=Int BM1[VID]i -Int (7 *Int ?BaseReward) -Int getInactivityPenalty(EBM[VID]i, ?FinalityDelay)

endmodule
