require "../../verification.k"

module N1-SPEC

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

andBool ( isActiveValidator(V, ?Epoch) orBool ( V.slashed andBool ?Epoch +Int 1 <Int V.withdrawable_epoch ) )
andBool V.id inA ?SourceAttestations
andBool V.id inA ?TargetAttestations
andBool V.id inA   ?HeadAttestations
andBool ?FinalityDelay <=Int MIN_EPOCHS_TO_INACTIVITY_PENALTY
andBool implies(V.id inA ?SourceAttestations, V.id =/=Int minByInclusionDelay(V.id, ?SourceAttestations).proposer)
andBool implies(V.id inA ?SourceAttestations, minByInclusionDelay(V.id, ?SourceAttestations).inclusion_delay >=Int 1)

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
// consistency conditions
andBool V.id in VIDs andBool VM1[V.id]v ==K V
andBool implies(V.id inA ?SourceAttestations, minByInclusionDelay(V.id, ?SourceAttestations).proposer in VIDs)
ensures true
// ensures

andBool ?VM2[V.id]v.balance <=Int VM1[V.id]v.balance +Int ?BaseReward +Int ?BaseReward +Int ?BaseReward +Int ?BaseReward

andBool ?VM2[V.id]v.balance ==Int VM1[V.id]v.balance +Int (?BaseReward *Int (?SourceAttestingBalance /Int EFFECTIVE_BALANCE_INCREMENT)
                                                                       /Int (?TotalActiveBalance     /Int EFFECTIVE_BALANCE_INCREMENT))
                                                     +Int (?BaseReward *Int (?TargetAttestingBalance /Int EFFECTIVE_BALANCE_INCREMENT)
                                                                       /Int (?TotalActiveBalance     /Int EFFECTIVE_BALANCE_INCREMENT))
                                                     +Int (?BaseReward *Int (?HeadAttestingBalance   /Int EFFECTIVE_BALANCE_INCREMENT)
                                                                       /Int (?TotalActiveBalance     /Int EFFECTIVE_BALANCE_INCREMENT))
                                                     +Int ((?BaseReward -Int ?BaseReward /Int PROPOSER_REWARD_QUOTIENT) /Int minByInclusionDelay(V.id, ?SourceAttestations).inclusion_delay)

endmodule
