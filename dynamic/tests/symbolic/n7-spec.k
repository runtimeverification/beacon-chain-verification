require "../../verification.k"

module N7-SPEC

imports VERIFICATION

rule
<T>
  <k> processRewardPenalty(V, ?Epoch, ?FinalityDelay, ?BaseReward,
                           ?SourceAttestations,     ?TargetAttestations,     ?HeadAttestations,
                           ?SourceAttestingBalance, ?TargetAttestingBalance, ?HeadAttestingBalance, ?TotalActiveBalance) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(VM1 => ?VM2, VIDs) </validators>
      <attested>
        Epoch |-> Attestations:Attestations
        ...
      </attested>
      <lastFinalized> LastFinalizedEpoch </lastFinalized>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch) </slot>
      <lastBlock> (_, EpochBoundaryBlock) </lastBlock>
      ...
    </state>
    <blocks> BM </blocks>
    ...
  </states>
  ...
</T>
requires true

andBool implies(V.id inA ?SourceAttestations, V.id =/=Int minByInclusionDelay(V.id, ?SourceAttestations).proposer)

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
andBool ?FinalityDelay ==Int ?Epoch -Int LastFinalizedEpoch
andBool ?BaseReward ==Int getBaseReward(V, ?TotalActiveBalance)
andBool ?SourceAttestations ==K filterNotSlashed(VM1, Attestations)
andBool ?TargetAttestations ==K filterByTarget(EpochBoundaryBlock, ?SourceAttestations)
andBool   ?HeadAttestations ==K filterByHead(BM, ?TargetAttestations)
andBool ?SourceAttestingBalance ==Int lift(totalBalance(VM1, getValidators(?SourceAttestations)))
andBool ?TargetAttestingBalance ==Int lift(totalBalance(VM1, getValidators(?TargetAttestations)))
andBool   ?HeadAttestingBalance ==Int lift(totalBalance(VM1, getValidators(?HeadAttestations)))
andBool     ?TotalActiveBalance ==Int lift(totalBalance(VM1, activeValidators(v(VM1,VIDs), ?Epoch)))
// conditions
andBool ?Epoch >=Int 2
// invariants
andBool ?SourceAttestingBalance <=Int ?TotalActiveBalance
andBool ?TargetAttestingBalance <=Int ?TotalActiveBalance
andBool   ?HeadAttestingBalance <=Int ?TotalActiveBalance
andBool implies(V.id inA ?SourceAttestations, minByInclusionDelay(V.id, ?SourceAttestations).inclusion_delay >=Int 1)
// consistency conditions
andBool V.id in VIDs andBool VM1[V.id]v ==K V
andBool implies(V.id inA ?SourceAttestations, minByInclusionDelay(V.id, ?SourceAttestations).proposer in VIDs)
ensures true
// ensures

andBool implies(
          notBool ( isActiveValidator(V, ?Epoch) orBool ( V.slashed andBool ?Epoch +Int 1 <Int V.withdrawable_epoch ) )
        ,
          ?VM2 ==K VM1
        )

andBool implies(
          isActiveValidator(V, ?Epoch) orBool ( V.slashed andBool ?Epoch +Int 1 <Int V.withdrawable_epoch )
        ,
          implies(
            // active case
            ?FinalityDelay <=Int MIN_EPOCHS_TO_INACTIVITY_PENALTY
          ,
            // max: + 4 * BaseReward
            ?VM2[V.id]v.balance <=Int VM1[V.id]v.balance +Int ?BaseReward +Int ?BaseReward +Int ?BaseReward +Int ?BaseReward
          andBool
            // min: - 3 * BaseReward
            ?VM2[V.id]v.balance >=Int VM1[V.id]v.balance +Int (0 -Int ?BaseReward) +Int (0 -Int ?BaseReward) +Int (0 -Int ?BaseReward)
          )
        andBool
          implies(
            // inactive case
            ?FinalityDelay >Int MIN_EPOCHS_TO_INACTIVITY_PENALTY
          ,
            // max: + 0
            ?VM2[V.id]v.balance <=Int VM1[V.id]v.balance +Int ?BaseReward +Int ?BaseReward +Int ?BaseReward +Int ?BaseReward
                                                         +Int (0 -Int BASE_REWARDS_PER_EPOCH *Int ?BaseReward)
                                                         +Int #if V.id inA ?TargetAttestations
                                                              #then 0
                                                              #else (0 -Int V.effective_balance *Int ?FinalityDelay /Int INACTIVITY_PENALTY_QUOTIENT)
                                                              #fi
          andBool
            // min: - 7 * BaseReward - (EffectiveBalance * FinalityDelay / 33,554,432)
            ?VM2[V.id]v.balance >=Int VM1[V.id]v.balance +Int (0 -Int ?BaseReward) +Int (0 -Int ?BaseReward) +Int (0 -Int ?BaseReward)
                                                         +Int (0 -Int BASE_REWARDS_PER_EPOCH *Int ?BaseReward)
                                                         +Int #if V.id inA ?TargetAttestations
                                                              #then 0
                                                              #else (0 -Int V.effective_balance *Int ?FinalityDelay /Int INACTIVITY_PENALTY_QUOTIENT)
                                                              #fi
          )
        )

endmodule
