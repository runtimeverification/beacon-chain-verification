# Dynamic Abstract Model of Beacon Chain State Transition

This presents an abstract model of the Beacon chain state transition system.

This model is designed for the safety and liveness proofs of the Beacon chain finality mechanism. It abstracts aways certain unnecessary details of the system, including the cached history mechanism for the space efficiency, validation of cryptographic data (public keys, signatures, commitments, etc.), and the committee assignment mechanism.

## Data Types

The data types used in this model are defiend [here](dynamic-abstract-beacon-chain-syntax.md).

```k
require "dynamic-abstract-beacon-chain-syntax.md"

module DYNAMIC-ABSTRACT-BEACON-CHAIN

imports DYNAMIC-ABSTRACT-BEACON-CHAIN-SYNTAX
imports INT
imports MAP
imports LIST
imports K-REFLECTION
```

## Abstract Beacon Chain States

This configuration stores the history of all abstract Beacon chain states from the genesis block to the latest block.

For each slot, an abstract Beacon chain state represents the post-state of a (possibly empty) block associated with the slot. The abstract state records the current status of validators, and the full history of attestations and justified/finalized blocks. While the `BeaconState` of the concrete model stores the history of only the most recent `k` blocks for space efficiency, the abstract model records the full history for the simplicity of representation.

The Eth1 data and RANDAO mixes are omitted in this abstract model.

```k
// eth1_* and randao_mixes are omitted
configuration <T>
  <k> init ~> $PGM:Cmds </k>
  <currentSlot> 0 </currentSlot>
  <states>
    // a state of slot N is the post-state of a (possibly empty) block at slot N
    <state multiplicity="*" type="Map">
      <slot> 0 </slot>
      <validators> v(m(.BMap, .IMap, .IMap, .IMap, .IMap, .IMap, .IMap), .IntList) </validators>
      <slashedBalance> .IMap </slashedBalance> // epoch -> sum of slashed effective balance
      <attested> .Map </attested> // epoch -> attestations
      <justified> .BList </justified> // epoch -> bool
      <finalized> .BList </finalized> // epoch -> bool
    </state>
  </states>
  // historical
  <lastBlock> .IMap </lastBlock> // slot -> last block id
  <lastJustified> .IList </lastJustified> // epoch -> last justified block id
  <lastFinalized> .IList </lastFinalized> // epoch -> last finalized block id
  // blockchain
  <blocks> .BlockMap </blocks> // block id -> block
</T>
```

A dummy initialization for testing purposes.

```k
syntax KItem ::= "init"
rule <k> init => . ... </k>
     <currentSlot> 0 </currentSlot>
     <states> .Bag =>
       <state>
         <slot> 0 </slot>
         <validators> v(
           m(// slashed
             .BMap [ 0 <- false ]b [ 1 <- false ]b [ 2 <- false ]b [ 3 <- false ]b [ 4 <- false ]b [ 5 <- false ]b [ 6 <- false ]b
           , // balance
             .IMap [ 0 <- 1 ]i [ 1 <- 1 ]i [ 2 <- 1 ]i [ 3 <- 1 ]i [ 4 <- 1 ]i [ 5 <- 1 ]i [ 6 <- 1 ]i
           , // effective_balance
             .IMap [ 0 <- 1 ]i [ 1 <- 1 ]i [ 2 <- 1 ]i [ 3 <- 1 ]i [ 4 <- 1 ]i [ 5 <- 1 ]i [ 6 <- 1 ]i
           , // activation_eligibility_epoch
             .IMap [ 0 <- 0 ]i [ 1 <- 0 ]i [ 2 <- 0 ]i [ 3 <- 0 ]i [ 4 <- 0 ]i [ 5 <- 0 ]i [ 6 <- 0 ]i
           , // activation_epoch
             .IMap [ 0 <- 0 ]i [ 1 <- 0 ]i [ 2 <- 0 ]i [ 3 <- 0 ]i [ 4 <- 0 ]i [ 5 <- 0 ]i [ 6 <- 0 ]i
           , // exit_epoch
             .IMap [ 0 <- FAR_FUTURE_EPOCH ]i [ 1 <- FAR_FUTURE_EPOCH ]i [ 2 <- FAR_FUTURE_EPOCH ]i [ 3 <- FAR_FUTURE_EPOCH ]i [ 4 <- FAR_FUTURE_EPOCH ]i [ 5 <- FAR_FUTURE_EPOCH ]i [ 6 <- FAR_FUTURE_EPOCH ]i
           , // withdrawable_epoch
             .IMap [ 0 <- FAR_FUTURE_EPOCH ]i [ 1 <- FAR_FUTURE_EPOCH ]i [ 2 <- FAR_FUTURE_EPOCH ]i [ 3 <- FAR_FUTURE_EPOCH ]i [ 4 <- FAR_FUTURE_EPOCH ]i [ 5 <- FAR_FUTURE_EPOCH ]i [ 6 <- FAR_FUTURE_EPOCH ]i
           )
         ,
           0 1 2 3 4 5 6 .IntList
         ) </validators>
         <slashedBalance> .IMap </slashedBalance>
         <attested> 0 |-> .Attestations </attested>
         <justified> .BList [ 0 <- true ]bb </justified>
         <finalized> .BList [ 0 <- true ]bb </finalized>
       </state>
     </states>
     <lastBlock> .IMap => .IMap [ 0 <- 0 ]i </lastBlock>
     <lastJustified> .IList => .IList [ 0 <- 0 ]ii </lastJustified>
     <lastFinalized> .IList => .IList [ 0 <- 0 ]ii </lastFinalized>
     <blocks> .BlockMap => .BlockMap [ 0 <- #Block((0,0),(-1,-1),.Slashings,.Attestations,.Deposits,.VoluntaryExits) ]k </blocks>
```

## State Transition

The Beacon chain state transition function takes as input a state at slot `N` and a new proposed block, and produces a new state at slot `N+1` if the block is valid.

Validation of block signatures and state roots is omitted in the abstract model.

```k
// state_transition
rule <k> stateTransition(Block)
      => #assert(Slot <Int Block.slot) // TODO: <=Int or <Int ?
      ~> processSlots(Block.slot)
      ~> processBlock(Block) ... </k>
     <currentSlot> Slot </currentSlot>
```

The `process_epoch()` in the concrete model is called before increasing the slot number, while it is called after increasing `Slot` here.

```k
// process_slots
rule <k> processSlots(TargetSlot)
      => processSlot()
      ~> processEpoch()
      ~> processSlots(TargetSlot) ... </k>
     <currentSlot> Slot => Slot +Int 1 </currentSlot> // TODO: in the python spec, slot number is increased after processEpoch
     <states>
       <state> <slot> Slot        </slot> S </state>
     (
       .Bag
     =>
       <state> <slot> Slot +Int 1 </slot> S </state>
     )
       ...
     </states>
     <lastBlock> B => B [ Slot +Int 1 <- B[Slot]i ]i </lastBlock>
     requires Slot <Int TargetSlot

rule <k> processSlots(TargetSlot) => . ... </k>
     <currentSlot> Slot </currentSlot>
     requires Slot ==Int TargetSlot

rule <k> processSlots(TargetSlot) => #bottom ... </k>
     <currentSlot> Slot </currentSlot>
     requires Slot >Int TargetSlot
```

Updating the cached history is not required here since the full history is recorded in the abstract model.

```k
// process_slot
rule <k> processSlot() => . ... </k>
```

## Epoch Processing

Note that `Slot` is equal to `state.slot + 1` of the concrete model.

```k
// TODO: add process_slashings, process_final_updates (for updating effective balances with hysteresis)
// process_epoch
rule <k> processEpoch()
      => #assert(epochOf(Slot) >=Int 1) // genesis block/epoch is processed separately
      ~> processJustificationAndFinalization()  // effective for epoch >= 3
      ~> processRewardsPenalties()              // effective for epoch >= 2
      ~> processValidatorUpdates() ... </k>     // effective for epoch >= 1
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
```
```{.k .symbolic}
       <attested> epochOf(Slot) |-> (_ => .Attestations) ... </attested>
```
```{.k .concrete}
       <attested> A => A[epochOf(Slot) <- .Attestations] </attested>
```
```k
       <justified> J => J [ epochOf(Slot) <- false ]bb </justified>
       <finalized> F => F [ epochOf(Slot) <- false ]bb </finalized>
       ...
     </state>
     <lastJustified> LJ => LJ [ epochOf(Slot) <- LJ[epochOf(Slot) -Int 1]ii ]ii </lastJustified>
     <lastFinalized> LF => LF [ epochOf(Slot) <- LF[epochOf(Slot) -Int 1]ii ]ii </lastFinalized>
     requires isFirstSlotOfEpoch(Slot)

rule <k> processEpoch() => . ... </k>
     <currentSlot> Slot </currentSlot>
     requires notBool isFirstSlotOfEpoch(Slot)
```

### Justification and Finalization

```k
syntax KItem ::= processJustificationAndFinalization()

rule <k> processJustificationAndFinalization()
      => processJustification(epochOf(Slot) -Int 2)
      ~> processJustification(epochOf(Slot) -Int 1)
      ~> processFinalization(epochOf(Slot) -Int 2)
      ~> processFinalization(epochOf(Slot) -Int 1) ... </k>
     <currentSlot> Slot </currentSlot>
     requires epochOf(Slot) >=Int 3

rule <k> processJustificationAndFinalization() => . ... </k>
     <currentSlot> Slot </currentSlot>
     requires epochOf(Slot) <Int 3
```

### Justification

```k
syntax KItem ::= processJustification(Int)
rule <k> processJustification(Epoch)
      => #assert(Epoch >=Int 1) // due to the side condition of processJustificationAndFinalization
      ~> #it(
           isJustifiable(Epoch, EpochBoundaryBlock[firstSlotOf(Epoch)]i, Attestations, VM.slashed, VM.effective_balance, VM.activation_epoch, VM.exit_epoch, VIDs)
         ,
           justify(Epoch)
         ) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <attested>
         Epoch |-> Attestations:Attestations
         ...
       </attested>
     //<validators> v(VM, VIDs) </validators> // TODO: which validators to be considered?
       ...
     </state>
     <state>
       <slot> firstSlotOf(Epoch) </slot>
       <validators> v(VM, VIDs) </validators> // TODO: which validators to be considered?
       ...
     </state>
     <lastBlock> EpochBoundaryBlock </lastBlock>

syntax KItem ::= justify(Int)
rule <k> justify(Epoch) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <justified> J => J [ Epoch <- true ]bb </justified>
       ...
     </state>
     <lastJustified> LJ => LJ [ epochOf(Slot) <- Epoch ]ii </lastJustified>

syntax Bool ::= isJustifiable(Int, Int, Attestations, BMap, IMap, IMap, IMap, IntList) [function, functional, smtlib(isJustifiable)]
rule isJustifiable(Epoch, EpochBoundaryBlock, Attestations, SlashedMap, EffectiveBalanceMap, ActivationEpochMap, ExitEpochMap, VIDs)
  => isMajority(totalBalance(EffectiveBalanceMap, getUniqueValidators(filterByTarget(EpochBoundaryBlock, filterNotSlashed(SlashedMap, Attestations)))),
                totalBalance(EffectiveBalanceMap, activeValidators(VIDs, ActivationEpochMap, ExitEpochMap, Epoch)))
     orBool Epoch ==Int 0 // the genesis block is justified by default
     requires #isConcrete(Attestations) // TODO: drop this

syntax Bool ::= isMajority(Int, Int) [function, functional]
rule isMajority(X, Total) => (X *Int 3) >=Int (Total *Int 2)  // (X / Total) >= 2/3
                             andBool Total >Int 0             // ensure no div-by-zero
```

### Finalization

```k
syntax KItem ::= processFinalization(Int)
rule <k> processFinalization(TargetEpoch)
      => #assert(TargetEpoch >=Int 1) // due to the side condition of processJustificationAndFinalization
      ~> #it(
           isFinalizable(SourceEpoch[TargetEpoch]ii, TargetEpoch, Justified)
         ,
           finalize(SourceEpoch[TargetEpoch]ii)
         ) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <justified> Justified </justified>
       ...
     </state>
     <lastJustified> SourceEpoch </lastJustified>

syntax KItem ::= finalize(Int)
rule <k> finalize(Epoch) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <finalized> F => F [ Epoch <- true ]bb </finalized>
       ...
     </state>
     <lastFinalized> LF => LF [ epochOf(Slot) <- Epoch ]ii </lastFinalized>

// source : source+1 = target justified
// source : source+1 : source+2 = target justified
syntax Bool ::= isFinalizable(Int, Int, BList) [function] // not functional
rule isFinalizable(SourceEpoch, TargetEpoch, Justified)
  => Justified[SourceEpoch]bb andBool Justified[TargetEpoch]bb
     andBool (
                SourceEpoch +Int 1 ==Int TargetEpoch
       orBool ( SourceEpoch +Int 2 ==Int TargetEpoch andBool Justified[SourceEpoch +Int 1]bb )
     )
```

### Rewards and Penalties

```k
// process_rewards_and_penalties
syntax KItem ::= processRewardsPenalties()
rule <k> processRewardsPenalties()
      => #it(
           epochOf(Slot) >=Int 2
         ,
           processRewardsPenaltiesAux(epochOf(Slot) -Int 2)
         ) ... </k>
     <currentSlot> Slot </currentSlot>

syntax KItem ::= processRewardsPenaltiesAux(Int)
rule <k> processRewardsPenaltiesAux(Epoch)
      => #assert(Epoch >=Int 0) // due to the side condition of processRewardsPenalties
      ~> processRewardsPenaltiesAux1(
           VIDs, VM, Epoch, Epoch -Int LastFinalizedEpoch[epochOf(Slot)]ii,
                                                                                filterNotSlashed(VM.slashed, Attestations) ,
                                  filterByTarget(BlockMap[firstSlotOf(Epoch)]i, filterNotSlashed(VM.slashed, Attestations)),
           filterByHead(BlockMap, filterByTarget(BlockMap[firstSlotOf(Epoch)]i, filterNotSlashed(VM.slashed, Attestations)))
         ) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, VIDs) </validators>
       <attested>
         Epoch |-> Attestations:Attestations
         ...
       </attested>
       ...
     </state>
     <lastBlock> BlockMap </lastBlock>
     <lastFinalized> LastFinalizedEpoch </lastFinalized>

syntax KItem ::= processRewardsPenaltiesAux1(IntList, ValidatorMap, Int, Int, Attestations, Attestations, Attestations)
rule processRewardsPenaltiesAux1(VIDs, VM, Epoch, FinalityDelay, SourceAttestations, TargetAttestations, HeadAttestations)
  => processRewardsPenaltiesAux2(VIDs, VM, Epoch, FinalityDelay, SourceAttestations, TargetAttestations, HeadAttestations,
       lift(totalBalance(VM.effective_balance, getUniqueValidators(SourceAttestations))),
       lift(totalBalance(VM.effective_balance, getUniqueValidators(TargetAttestations))),
       lift(totalBalance(VM.effective_balance, getUniqueValidators(HeadAttestations))),
       lift(totalBalance(VM.effective_balance, activeValidators(VIDs, VM.activation_epoch, VM.exit_epoch, Epoch))) // TODO: in the python spec, the current epoch is considered when computing the total active balance
     )

syntax KItem ::= processRewardsPenaltiesAux2(IntList, ValidatorMap, Int, Int, Attestations, Attestations, Attestations, Int, Int, Int, Int)
rule processRewardsPenaltiesAux2(          VIDs, VM, Epoch, FinalityDelay, SourceAttestations, TargetAttestations, HeadAttestations, SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance)
  => processRewardsPenaltiesAux3(.IntList, VIDs, VM, Epoch, FinalityDelay, SourceAttestations, TargetAttestations, HeadAttestations, SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance)

syntax KItem ::= processRewardsPenaltiesAux3(IntList, IntList, ValidatorMap, Int, Int, Attestations, Attestations, Attestations, Int, Int, Int, Int)
rule (. => processRewardPenalty(VID, VM.slashed, VM.effective_balance, VM.activation_epoch, VM.exit_epoch, VM.withdrawable_epoch, Epoch, FinalityDelay, getBaseReward(VM.effective_balance[VID]i, TotalActiveBalance), SourceAttestations, TargetAttestations, HeadAttestations, SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance))
  ~> processRewardsPenaltiesAux3(G_VIDs => VID G_VIDs, VID VIDs => VIDs, VM, Epoch, FinalityDelay, SourceAttestations, TargetAttestations, HeadAttestations, SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance)
rule processRewardsPenaltiesAux3(_, .IntList, _, _, _, _, _, _, _, _, _, _) => .

syntax KItem ::= processRewardPenalty(Int, BMap, IMap, IMap, IMap, IMap, Int, Int, Int, Attestations, Attestations, Attestations, Int, Int, Int, Int)
rule processRewardPenalty(VID, SlashedMap, EffectiveBalanceMap, ActivationEpochMap, ExitEpochMap, WithdrawableEpochMap, Epoch, FinalityDelay, BaseReward,
                          SourceAttestations,     TargetAttestations,     HeadAttestations,
                          SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance)
  => #it(
       isActiveValidator(VID, ActivationEpochMap, ExitEpochMap, Epoch) orBool ( SlashedMap[VID]b andBool Epoch +Int 1 <Int WithdrawableEpochMap[VID]i )
     ,
       increaseBalance(VID,
       // Matching Rewards and Penalties
         #if VID inA SourceAttestations
         #then getMatchingReward(BaseReward, SourceAttestingBalance, TotalActiveBalance)
         #else 0 -Int BaseReward
         #fi
       +Int
         #if VID inA TargetAttestations
         #then getMatchingReward(BaseReward, TargetAttestingBalance, TotalActiveBalance)
         #else 0 -Int BaseReward
         #fi
       +Int
         #if VID inA HeadAttestations
         #then getMatchingReward(BaseReward, HeadAttestingBalance, TotalActiveBalance)
         #else 0 -Int BaseReward
         #fi
       +Int
       // Inclusion Rewards
         #if VID inA SourceAttestations
         #then getInclusionReward(BaseReward, minByInclusionDelay(VID, SourceAttestations).inclusion_delay)
         #else 0
         #fi
       // Inactivity Penalties
       +Int
         #if FinalityDelay >Int MIN_EPOCHS_TO_INACTIVITY_PENALTY
         #then (0 -Int BASE_REWARDS_PER_EPOCH *Int BaseReward)
               +Int #if notBool (VID inA TargetAttestations)
                    #then (0 -Int getInactivityPenalty(EffectiveBalanceMap[VID]i, FinalityDelay))
                    #else 0
                    #fi
         #else 0
         #fi
       )
       /* TODO: process proposer rewards
       ~>
       // Proposer Rewards
       #it(
         VID inA SourceAttestations
       ,
         increaseBalance(minByInclusionDelay(VID, SourceAttestations).proposer, BaseReward /Int PROPOSER_REWARD_QUOTIENT)
       )
       */
     )
     // TODO: due to the positive balance cap, the order of rewards/penalties matters.

// get_base_reward
syntax Int ::= getBaseReward(Int, Int) [function, smtlib(getBaseReward)]
rule getBaseReward(EffectiveBalance, TotalActiveBalance)
  => EffectiveBalance *Int BASE_REWARD_FACTOR
     /Int sqrtInt(TotalActiveBalance)
     /Int BASE_REWARDS_PER_EPOCH
     [concrete]

syntax Int ::= getMatchingReward(Int, Int, Int) [function, smtlib(getMatchingReward)]
rule getMatchingReward(BaseReward, AttestingBalance, TotalActiveBalance)
  => BaseReward *Int (AttestingBalance   /Int EFFECTIVE_BALANCE_INCREMENT)
                /Int (TotalActiveBalance /Int EFFECTIVE_BALANCE_INCREMENT)
     [concrete]

syntax Int ::= getInclusionReward(Int, Int) [function, smtlib(getInclusionReward)]
rule getInclusionReward(BaseReward, InclusionDelay)
  => (BaseReward -Int BaseReward /Int PROPOSER_REWARD_QUOTIENT) /Int InclusionDelay
     [concrete]

syntax Int ::= getInactivityPenalty(Int, Int) [function, smtlib(getInactivityPenalty)]
rule getInactivityPenalty(EffectiveBalance, FinalityDelay)
  => EffectiveBalance *Int FinalityDelay /Int INACTIVITY_PENALTY_QUOTIENT
     [concrete]

// increase_balance
syntax KItem ::= increaseBalance(Int, Int)
rule <k> increaseBalance(VID, N) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(
         m(SM
         , BM => BM [ VID <- maxInt(0, BM[VID]i +Int N) ]i // ensures balance to be positive
         , EBM
         , AEM
         , AM
         , EM
         , WM
         )
       ,
         VIDs
       ) </validators>
       ...
     </state>
     requires VID in VIDs
rule <k> increaseBalance(VID, N) => #bottom ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(_, VIDs) </validators>
       ...
     </state>
     requires notBool VID in VIDs

// decrease_balance
syntax KItem ::= decreaseBalance(Int, Int)
rule decreaseBalance(VID, N) => increaseBalance(VID, 0 -Int N)

syntax Int ::= totalBalance(IMap, IntList) [function, smtlib(totalBalance)]
rule totalBalance(EffectiveBalanceMap, VID VIDs) => EffectiveBalanceMap[VID]i +Int totalBalance(EffectiveBalanceMap, VIDs)
rule totalBalance(_, .IntList) => 0

syntax Int ::= lift(Int) [function, smtlib(lift)]
rule lift(B) => maxInt(EFFECTIVE_BALANCE_INCREMENT, B)
     [concrete]

syntax Attestations ::= filterByAttester(Int, Attestations) [function, smtlib(filterByAttester)]
rule filterByAttester(V, A As) => #if A.attester ==Int V
                                  #then A filterByAttester(V, As)
                                  #else   filterByAttester(V, As)
                                  #fi
rule filterByAttester(_, .Attestations) => .Attestations

syntax Attestations ::= filterByTarget(Int, Attestations) [function, smtlib(filterByTarget)]
rule filterByTarget(T, A As) => #if A.target_block ==Int T
                                #then A filterByTarget(T, As)
                                #else   filterByTarget(T, As)
                                #fi
rule filterByTarget(_, .Attestations) => .Attestations

syntax Attestations ::= filterByHead(IMap, Attestations) [function, smtlib(filterByHead)]
rule filterByHead(BlockMap, A As) => #if A.head_block ==Int BlockMap[A.slot]i
                               #then A filterByHead(BlockMap, As)
                               #else   filterByHead(BlockMap, As)
                               #fi
rule filterByHead(_, .Attestations) => .Attestations

syntax Attestations ::= filterNotSlashed(BMap, Attestations) [function, smtlib(filterNotSlashed)]
rule filterNotSlashed(SlashedMap, A As) => #if SlashedMap[A.attester]b
                                   #then   filterNotSlashed(SlashedMap, As)
                                   #else A filterNotSlashed(SlashedMap, As)
                                   #fi
rule filterNotSlashed(_, .Attestations) => .Attestations

syntax IntList ::= getUniqueValidators(Attestations) [function, smtlib(getUniqueValidators)]
rule getUniqueValidators(As) => getUniqueValidatorsAux2(getUniqueValidatorsAux1(As, .Map))
     [concrete]

syntax Map ::= getUniqueValidatorsAux1(Attestations, Map) [function]
rule getUniqueValidatorsAux1(A As => As, M => M [ A.attester <- true ])
rule getUniqueValidatorsAux1(.Attestations, M) => M

syntax IntList ::= getUniqueValidatorsAux2(Map) [function]
rule getUniqueValidatorsAux2(V |-> true M) => V getUniqueValidatorsAux2(M)
rule getUniqueValidatorsAux2(.Map) => .IntList

// `minByInclusionDelay(V, As)` returns the first included attestation attested by V
// it is defined only when `V inA As`
syntax Attestation ::= minByInclusionDelay(Int, Attestations) [function, klabel(minA), smtlib(minA)]
rule minByInclusionDelay(V, As) => minByInclusionDelayAux1(V, As) [concrete]

syntax Attestation ::= minByInclusionDelayAux1(Int, Attestations) [function]
rule minByInclusionDelayAux1(V, A As) => minByInclusionDelayAux2(A, As) requires V  ==Int A.attester
rule minByInclusionDelayAux1(V, A As) => minByInclusionDelayAux1(V, As) requires V =/=Int A.attester

syntax Attestation ::= minByInclusionDelayAux2(Attestation, Attestations) [function]
rule minByInclusionDelayAux2(A0, A As) => minByInclusionDelayAux2(#if A0.inclusion_delay <=Int A.inclusion_delay #then A0 #else A #fi, As) 
rule minByInclusionDelayAux2(A0, .Attestations) => A0
```

### Validator Updates

```k
// TODO: check if no mistake was made as this process is associated with the previous epoch
// process_registry_updates
syntax KItem ::= processValidatorUpdates()
rule <k> processValidatorUpdates()
      => processValidatorEjections(VIDs)    // TODO: processValidatorEjection comes after updateActivationEligibility in the concrete model
      ~> updateActivationEligibilities(VIDs)
      ~> processValidatorActivation() ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(_, VIDs) </validators>
       ...
     </state>

syntax KItem ::= processValidatorEjections(IntList)
rule <k> processValidatorEjections(VIDs) => processValidatorEjectionsAux(.IntList, VIDs, VM) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>

syntax KItem ::= processValidatorEjectionsAux(IntList, IntList, ValidatorMap)
rule processValidatorEjectionsAux(L, VID VIDs, VM0) => processValidatorEjection(VID) ~> processValidatorEjectionsAux(VID L, VIDs, VM0)
rule processValidatorEjectionsAux(_, .IntList, _) => .

syntax KItem ::= processValidatorEjection(Int)
rule <k> processValidatorEjection(VID)
      => #it(
           isActiveValidator(VID, VM.activation_epoch, VM.exit_epoch, epochOf(Slot) -Int 1) andBool VM.effective_balance[VID]i <=Int EJECTION_BALANCE
         ,
           initiateValidatorExit(VID)
         ) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>

syntax KItem ::= updateActivationEligibilities(IntList)
rule <k> updateActivationEligibilities(VIDs) => updateActivationEligibilitiesAux(.IntList, VIDs, VM) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>

syntax KItem ::= updateActivationEligibilitiesAux(IntList, IntList, ValidatorMap)
rule updateActivationEligibilitiesAux(L, VID VIDs, VM) => updateActivationEligibility(VID) ~> updateActivationEligibilitiesAux(VID L, VIDs, VM)
rule updateActivationEligibilitiesAux(_, .IntList, _) => .

syntax KItem ::= updateActivationEligibility(Int)
rule <k> updateActivationEligibility(VID)
      => #it(
           isActivationEligible(VID, VM.activation_eligibility_epoch, VM.effective_balance)
         ,
           setActivationEligibility(VID)
         ) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>

syntax KItem ::= setActivationEligibility(Int)
rule <k> setActivationEligibility(VID) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(
         m(SM
         , BM
         , EBM
         , AEM => AEM [ VID <- epochOf(Slot) ]i
         , AM
         , EM
         , WM
         )
       ,
         _
       ) </validators>
       ...
     </state>

// is_eligible_for_activation_queue
syntax Bool ::= isActivationEligible(Int, IMap, IMap) [function, functional]
rule isActivationEligible(VID, ActivationEligibilityEpochMap, EffectiveBalanceMap)
  => ActivationEligibilityEpochMap[VID]i ==Int FAR_FUTURE_EPOCH andBool
     EffectiveBalanceMap[VID]i ==Int MAX_EFFECTIVE_BALANCE

syntax Kitem ::= processValidatorActivation()
rule <k> processValidatorActivation()
      => activateValidators(activationQueueUptoChurnLimit(VIDs, VM.activation_eligibility_epoch, VM.activation_epoch, VM.exit_epoch, FinalizedEpoch[epochOf(Slot)]ii, epochOf(Slot) -Int 1)) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, VIDs) </validators>
       ...
     </state>
     <lastFinalized> FinalizedEpoch </lastFinalized>

syntax KItem ::= activateValidators(IntList)
rule <k> activateValidators(VIDs) => activateValidatorsAux(.IntList, VIDs, VM) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>

syntax KItem ::= activateValidatorsAux(IntList, IntList, ValidatorMap)
rule activateValidatorsAux(L, VID VIDs, VM0) => activateValidator(VID) ~> activateValidatorsAux(VID L, VIDs, VM0)
rule activateValidatorsAux(_, .IntList, _) => .

syntax KItem ::= activateValidator(Int)
rule <k> activateValidator(VID) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(
         m(SM
         , BM
         , EBM
         , AEM
         , AM => AM [ VID <- delayedActivationExitEpoch(epochOf(Slot) -Int 1) ]i
         , EM
         , WM
         )
       ,
         _
       ) </validators>
       ...
     </state>

syntax IntList ::= activationQueueUptoChurnLimit(IntList, IMap, IMap, IMap, Int, Int) [function, functional]
rule activationQueueUptoChurnLimit(VIDs, ActivationEligibilityEpochMap, ActivationEpochMap, ExitEpochMap, FinalizedEpoch, CurrentEpoch)
  => take(
       churnLimit(size(activeValidators(VIDs, ActivationEpochMap, ExitEpochMap, CurrentEpoch))),
       sortByActivationEligibility(activationQueue(VIDs, ActivationEligibilityEpochMap, ActivationEpochMap, FinalizedEpoch))
     )

syntax IntList ::= activationQueue(IntList, IMap, IMap, Int) [function, functional, smtlib(activationQueue)]
rule activationQueue(VID VIDs, ActivationEligibilityEpochMap, ActivationEpochMap, FinalizedEpoch)
  => #if isValidValidatorToActivate(VID, ActivationEligibilityEpochMap, ActivationEpochMap, FinalizedEpoch)
     #then VID activationQueue(VIDs, ActivationEligibilityEpochMap, ActivationEpochMap, FinalizedEpoch)
     #else     activationQueue(VIDs, ActivationEligibilityEpochMap, ActivationEpochMap, FinalizedEpoch)
     #fi
rule activationQueue(.IntList, _, _, _) => .IntList

syntax Bool ::= isValidValidatorToActivate(Int, IMap, IMap, Int) [function]
rule isValidValidatorToActivate(VID, ActivationEligibilityEpochMap, ActivationEpochMap, FinalizedEpoch)
  => ActivationEligibilityEpochMap[VID]i <=Int FinalizedEpoch andBool // is_eligible_for_activation
     ActivationEpochMap[VID]i ==Int FAR_FUTURE_EPOCH

// sort in the order of activation_eligibility_epoch
syntax IntList ::= sortByActivationEligibility(IntList) [function, klabel(sortI), smtlib(sortI)]
// TODO: implement with additional argument ActivationEligibilityEpochMap

rule sortByActivationEligibility(.IntList) => .IntList
```

## Block Processing

`process_randao` and `process_eth1_data` are omitted in the abstract model.

```k
// process_block, process_block_header, process_operations
rule <k> processBlock(#Block((Slot, ID), Parent, Slashings, Attestations, Deposits, VoluntaryExits))
      => processSlashings(Slashings)
      ~> processAttestations(Attestations)
      ~> processDeposits(Deposits)
      ~> processVoluntaryExits(VoluntaryExits) ... </k>
     <currentSlot> Slot </currentSlot>
     <lastBlock> B => B [ Slot <- ID ]i </lastBlock> // TODO: check Parent matches `B [ Slot - 1 ]`
     <blocks>
       BlockMap => BlockMap [ ID <- #Block((Slot, ID), Parent, Slashings, Attestations, Deposits, VoluntaryExits) ]k
     </blocks>
     // TODO: check if the block proposer is valid (assigned, not slashed)
```

### Slashings

```k
// capturing both proposer slashings and attester slashings

// process_proposer_slashing
// process_attester_slashing
syntax KItem ::= processSlashings(Slashings)
rule <k> processSlashings(Slashings) => processSlashingsAux(.IntList, Slashings, VM) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>

syntax KItem ::= processSlashingsAux(IntList, Slashings, ValidatorMap)
rule processSlashingsAux(L, S Slashings, VM0) => processSlashing(S) ~> processSlashingsAux(S.attestation_1.attester L, Slashings, VM0)
rule processSlashingsAux(_, .Slashings, _) => .

syntax KItem ::= processSlashing(Slashing)
rule <k> processSlashing(S)
      => #assert(isValidSlashing(S, VM.slashed, VM.activation_epoch, VM.withdrawable_epoch, epochOf(Slot)))
      ~> initiateValidatorExit(S.attestation_1.attester)
      ~> slashValidator(S.attestation_1.attester) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>

// slash_validator
syntax KItem ::= slashValidator(Int)
rule <k> slashValidator(VID) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <slashedBalance> SBM => SBM [ epochOf(Slot) <- SBM[epochOf(Slot)]i +Int EBM[VID]i ]i </slashedBalance>
       <validators> v(
         m(SM => SM [ VID <- true ]b
         , BM => BM [ VID <- maxInt(0, BM[VID]i -Int (EBM[VID]i /Int MIN_SLASHING_PENALTY_QUOTIENT)) ]i
         , EBM
         , AEM
         , AM
         , EM
         , WM => WM [ VID <- maxInt(WM[VID]i, epochOf(Slot) +Int EPOCHS_PER_SLASHINGS_VECTOR) ]i
         )
       ,
         _
       ) </validators>
       ...
     </state>
     // TODO: proposer and whistleblower rewards

syntax Bool ::= isValidSlashing(Slashing, BMap, IMap, IMap, Int) [function]
rule isValidSlashing(S, SM, AM, WM, Epoch)
  => S.attestation_1.attester ==Int S.attestation_2.attester
     andBool isSlashableValidator(S.attestation_1.attester, SM, AM, WM, Epoch)
     andBool isSlashableAttestation(S.attestation_1, S.attestation_2)

// is_slashable_validator
syntax Bool ::= isSlashableValidator(Int, BMap, IMap, IMap, Int) [function]
rule isSlashableValidator(VID, SM, AM, WM, Epoch)
  => SM[VID]b ==K false
     andBool AM[VID]i <=Int Epoch andBool Epoch <Int WM[VID]i // withdrawable_epoch instead of exit_epoch

// is_slashable_attestation_data
syntax Bool ::= isSlashableAttestation(Attestation, Attestation) [function, functional]
rule isSlashableAttestation(A1, A2)
  => ( A1 =/=K A2 andBool A1.target_epoch ==Int A2.target_epoch )
     orBool
     ( A1.source_epoch <Int A2.source_epoch andBool A2.target_epoch <Int A1.target_epoch )
     orBool
     ( A2.source_epoch <Int A1.source_epoch andBool A1.target_epoch <Int A2.target_epoch )
     // TODO: the last case is not considered in the python spec
```

### Attestations

```k
// process_attestation
syntax KItem ::= processAttestations(Attestations)
rule processAttestations(As) => processAttestationsAux(.Attestations, As)

syntax KItem ::= processAttestationsAux(Attestations, Attestations)
rule processAttestationsAux(L, A As) => processAttestation(A) ~> processAttestationsAux(A L, As)
rule processAttestationsAux(_, .Attestations) => .

syntax KItem ::= processAttestation(Attestation)
rule processAttestation(A)
  => checkAttestation(A)
  ~> addAttestation(A)

syntax KItem ::= addAttestation(Attestation)
rule <k> addAttestation(A) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <attested>
         epochOf(Slot) |-> (As:Attestations => A As)
         ...
       </attested>
       ...
     </state>
     requires A.target_epoch ==Int epochOf(Slot)
rule <k> addAttestation(A) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <attested>
         epochOf(Slot) -Int 1 |-> (As:Attestations => A As)
         ...
       </attested>
       ...
     </state>
     requires A.target_epoch ==Int epochOf(Slot) -Int 1
     // TODO: merge two rules into a single one

syntax KItem ::= checkAttestation(Attestation)
rule <k> checkAttestation(A)
      => #assert(isValidAttestation(A, Slot, JEpoch[A.target_epoch]ii, JBlock[firstSlotOf(JEpoch[A.target_epoch]ii)]i, VM.slashed[A.attester]b)) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>
     <lastJustified> JEpoch </lastJustified>
     <lastBlock> JBlock </lastBlock>

syntax Bool ::= isValidAttestation(Attestation, Int, Int, Int, Bool) [function, functional]
rule isValidAttestation(A, Slot, SourceEpoch, SourceBlock, Slashed)
  =>         A.source_epoch ==Int SourceEpoch
     andBool A.source_block ==Int SourceBlock
     andBool ( A.target_epoch ==Int epochOf(Slot) orBool A.target_epoch ==Int epochOf(Slot) -Int 1 )
     andBool A.target_epoch ==Int epochOf(A.slot)
     andBool A.slot +Int MIN_ATTESTATION_INCLUSION_DELAY <=Int Slot andBool Slot <=Int A.slot +Int MAX_ATTESTATION_INCLUSION_DELAY
     andBool A.inclusion_delay ==Int Slot -Int A.slot // TODO: in the python spec, this info is dynamically generated
     andBool notBool Slashed // TODO: this is not asserted in the python spec
     // TODO: check if A.attester is assigned to A.slot
```

### Deposits

```k
// process_deposit
syntax KItem ::= processDeposits(Deposits)
rule <k> processDeposits(Deposits) => processDepositsAux(.IntList, Deposits, Vs) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> Vs </validators>
       ...
     </state>

syntax KItem ::= processDepositsAux(IntList, Deposits, Validators)
rule processDepositsAux(L, D Deposits, Vs) => #assert(D.amount >=Int 0) ~> processDeposit(D) ~> processDepositsAux(D.sender L, Deposits, Vs)
rule processDepositsAux(_, .Deposits, _) => .

syntax KItem ::= processDeposit(Deposit)
rule <k> processDeposit(D) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(
         m(SM
         , BM => BM [ D.sender <- BM[D.sender]i +Int D.amount ]i // no change to effective_balance
         , EBM
         , AEM
         , AM
         , EM
         , WM
         )
       ,
         VIDs
       ) </validators>
       ...
     </state>
     requires D.sender in VIDs
rule <k> processDeposit(D) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(
         m(SM  => SM  [ D.sender <- false ]b
         , BM  => BM  [ D.sender <- D.amount ]i
         , EBM => EBM [ D.sender <- minInt(D.amount -Int (D.amount %Int EFFECTIVE_BALANCE_INCREMENT), MAX_EFFECTIVE_BALANCE) ]i // effective_balance cap
         , AEM => AEM [ D.sender <- FAR_FUTURE_EPOCH ]i
         , AM  => AM  [ D.sender <- FAR_FUTURE_EPOCH ]i
         , EM  => EM  [ D.sender <- FAR_FUTURE_EPOCH ]i
         , WM  => WM  [ D.sender <- FAR_FUTURE_EPOCH ]i
         )
       ,
         VIDs => D.sender VIDs
       ) </validators>
       ...
     </state>
     requires notBool D.sender in VIDs
```

### Voluntary Exits

```k
// process_voluntary_exit
syntax KItem ::= processVoluntaryExits(VoluntaryExits)
rule <k> processVoluntaryExits(Exits) => processVoluntaryExitsAux(.IntList, Exits, VM) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>

syntax KItem ::= processVoluntaryExitsAux(IntList, VoluntaryExits, ValidatorMap)
rule processVoluntaryExitsAux(L, E Exits, VM0) => processVoluntaryExit(E) ~> processVoluntaryExitsAux(E.validator L, Exits, VM0)
rule processVoluntaryExitsAux(_, .VoluntaryExits, _) => .

syntax KItem ::= processVoluntaryExit(VoluntaryExit)
rule <k> processVoluntaryExit(E)
      => #if isValidVoluntaryExit(E, VM.activation_epoch, VM.exit_epoch, epochOf(Slot))
         #then initiateValidatorExit(E.validator)
         #else #bottom
         #fi ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>

syntax Bool ::= isValidVoluntaryExit(VoluntaryExit, IMap, IMap, Int) [function]
rule isValidVoluntaryExit(E, ActivationEpochMap, ExitEpochMap, CurrEpoch)
  => isActiveValidator(E.validator, ActivationEpochMap, ExitEpochMap, CurrEpoch)
     andBool ExitEpochMap[E.validator]i ==Int FAR_FUTURE_EPOCH
     andBool CurrEpoch >=Int E.epoch
     andBool CurrEpoch >=Int ActivationEpochMap[E.validator]i +Int PERSISTENT_COMMITTEE_PERIOD

// is_active_validator
syntax Bool ::= isActiveValidator(Int, IMap, IMap, Int) [function, functional]
rule isActiveValidator(VID, ActivationEpochMap, ExitEpochMap, Epoch)
  => ActivationEpochMap[VID]i <=Int Epoch andBool Epoch <Int ExitEpochMap[VID]i

// initiate_validator_exit
syntax KItem ::= initiateValidatorExit(Int)
rule <k> initiateValidatorExit(VID)
      => #it(
           VM.exit_epoch[VID]i ==Int FAR_FUTURE_EPOCH
         ,
           setExitEpoch(VID, computeExitEpoch(VIDs, VM.activation_epoch, VM.exit_epoch, epochOf(Slot)))
         ) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, VIDs) </validators>
       ...
     </state>

syntax KItem ::= setExitEpoch(Int, Int)
rule <k> setExitEpoch(VID, ExitEpoch) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(
         m(SM
         , BM
         , EBM
         , AEM
         , AM
         , EM => EM [ VID <- ExitEpoch ]i
         , WM => WM [ VID <- ExitEpoch +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY ]i
         )
       ,
         _
       ) </validators>
       ...
     </state>

syntax Int ::= computeExitEpoch(IntList, IMap, IMap, Int) [function, functional]
             | computeExitEpochAux(IntList, IMap, Int, Int) [function, functional]
rule [computeExitEpoch]:
     computeExitEpoch(VIDs, ActivationEpochMap, ExitEpochMap, CurrentEpoch)
  => computeExitEpochAux(
       VIDs, ExitEpochMap,
       maxInt(maxExitEpoch(VIDs, ExitEpochMap), delayedActivationExitEpoch(CurrentEpoch)),
       size(activeValidators(VIDs, ActivationEpochMap, ExitEpochMap, CurrentEpoch))
     )
rule computeExitEpochAux(VIDs, ExitEpochMap, ExitEpoch, ActiveValidatorSize)
  => #if countValidatorsToExit(VIDs, ExitEpochMap, ExitEpoch) >=Int churnLimit(ActiveValidatorSize)
     #then ExitEpoch +Int 1
     #else ExitEpoch
     #fi

syntax Int ::= maxExitEpoch(IntList, IMap) [function, functional, smtlib(maxExitEpoch)]
rule maxExitEpoch(VID VIDs, ExitEpochMap) => maxInt(ExitEpochMap[VID]i, maxExitEpoch(VIDs, ExitEpochMap)) requires ExitEpochMap[VID]i =/=Int FAR_FUTURE_EPOCH
rule maxExitEpoch(VID VIDs, ExitEpochMap) =>                            maxExitEpoch(VIDs, ExitEpochMap)  requires ExitEpochMap[VID]i  ==Int FAR_FUTURE_EPOCH
rule maxExitEpoch(.IntList, _) => 0

syntax Int ::= countValidatorsToExit(IntList, IMap, Int) [function, functional, smtlib(countValidatorsToExit)]
rule countValidatorsToExit(VID VIDs, ExitEpochMap, ExitEpoch)
  => #if ExitEpochMap[VID]i ==Int ExitEpoch #then 1 #else 0 #fi +Int countValidatorsToExit(VIDs, ExitEpochMap, ExitEpoch)
rule countValidatorsToExit(.IntList, _, _) => 0

syntax IntList ::= activeValidators(IntList, IMap, IMap, Int) [function, functional, smtlib(activeValidators)]
rule activeValidators(VID VIDs, ActivationEpochMap, ExitEpochMap, Epoch)
  => #if isActiveValidator(VID, ActivationEpochMap, ExitEpochMap, Epoch)
     #then VID activeValidators(VIDs, ActivationEpochMap, ExitEpochMap, Epoch)
     #else     activeValidators(VIDs, ActivationEpochMap, ExitEpochMap, Epoch)
     #fi
rule activeValidators(.IntList, _, _, _) => .IntList

// compute_activation_exit_epoch
syntax Int ::= delayedActivationExitEpoch(Int) [function, functional]
rule delayedActivationExitEpoch(Epoch) => Epoch +Int 1 +Int ACTIVATION_EXIT_DELAY

// get_validator_churn_limit
syntax Int ::= churnLimit(Int) [function, functional]
rule churnLimit(ActiveValidatorSize)
  => maxInt(MIN_PER_EPOCH_CHURN_LIMIT, ActiveValidatorSize /Int CHURN_LIMIT_QUOTIENT)
```

```k
endmodule
```
