# Dynamic Abstract Model of Beacon Chain State Transition

This presents an abstract model of the Beacon chain state transition system.

This model is designed for the safety and liveness proofs of the Beacon chain finality mechanism. It abstracts aways certain unnecessary details of the system, including the cached history mechanism for the space efficiency, validation of cryptographic data (public keys, signatures, commitments, etc.), and the committee assignment mechanism.

## Data Types

The data types used in this model are defiend [here](dynamic-abstract-beacon-chain-syntax.md).

```k
require "dynamic-abstract-beacon-chain-syntax.k"

module DYNAMIC-ABSTRACT-BEACON-CHAIN

imports DYNAMIC-ABSTRACT-BEACON-CHAIN-SYNTAX
imports INT
imports MAP
imports LIST
```
```{.k .kast}
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
      <slashedBalance> 0 </slashedBalance> // slashed balance
      <attested> .Map </attested> // Epoch -> Attestations
      <justified> .Map </justified> // Epoch -> bool
      <finalized> .Map </finalized> // Epoch -> bool
      // derived info
      <lastBlock> (0,0) </lastBlock> // last block (slot, id)
      <lastJustified> 0 </lastJustified> // last justified (epoch, block id)
      <lastFinalized> 0 </lastFinalized> // last finalized (epoch, block id)
    </state>
  </states>
  // blockchain
  <blocks> .BlockMap </blocks> // slot -> block
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
         <slashedBalance> 0 </slashedBalance>
         <attested> 0 |-> .Attestations </attested>
         <justified> 0 |-> true </justified>
         <finalized> 0 |-> true </finalized>
         <lastBlock> (0,0) </lastBlock>
         <lastJustified> 0 </lastJustified>
         <lastFinalized> 0 </lastFinalized>
       </state>
     </states>
     <blocks> .BlockMap => .BlockMap [ 0 <- #Block((0,0),(-1,-1),.Slashings,.Attestations,.Deposits,.VoluntaryExits) ]k </blocks>
```

## State Transition

The Beacon chain state transition function takes as input a state at slot `N` and a new proposed block, and produces a new state at slot `N+1` if the block is valid.

Validation of block signatures and state roots is omitted in the abstract model.

```k
// state_transition
rule <k> stateTransition(NewBlock)
      => processSlots(NewBlock.slot)
      ~> processBlock(NewBlock) ... </k>
     <currentSlot> Slot </currentSlot>
     requires Slot <Int NewBlock.slot // TODO: <=Int or <Int ?
// TODO:
// rule stateTransition(NewBlock) => #bottom [owise]
```

The `process_epoch()` in the concrete model is called before increasing the slot number, while it is called after increasing `Slot` here.


```k
// process_slots
rule <k> (. => processSlot()
            ~> processEpoch())
      ~> processSlots(TargetSlot) ... </k>
     <currentSlot> Slot => Slot +Int 1 </currentSlot>
     <states>
       <state> <slot> Slot        </slot> S </state>
     (
       .Bag
     =>
       <state> <slot> Slot +Int 1 </slot> S </state>
     )
       ...
     </states>
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
      => processJustification(epochOf(Slot) -Int 2)
      ~> processJustification(epochOf(Slot) -Int 1)
      ~> processFinalization(epochOf(Slot) -Int 2)
      ~> processFinalization(epochOf(Slot) -Int 1)
```
```{.k .dynamic}
      ~> processRewardsPenalties(epochOf(Slot) -Int 2)
      ~> processValidatorUpdates()
```
```k
      ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <attested> A => A[epochOf(Slot) <- .Attestations] </attested>
       <justified> J => J[epochOf(Slot) <- false] </justified>
       <finalized> F => F[epochOf(Slot) <- false] </finalized>
       ...
     </state>
     requires isFirstSlotOfEpoch(Slot)

rule <k> processEpoch() => . ... </k>
     <currentSlot> Slot </currentSlot>
     requires notBool isFirstSlotOfEpoch(Slot)
```

### Justification

```k
syntax KItem ::= processJustification(Int)
rule <k> processJustification(Epoch)
      => isJustifiable(Epoch, EpochBoundaryBlock, Attestations, Validators)
      ~> justify(Epoch) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <attested>
         Epoch |-> Attestations:Attestations
         ...
       </attested>
     //<validators> Validators </validators> // TODO: which validators to be considered?
       ...
     </state>
     <state>
       <slot> firstSlotOf(Epoch) </slot>
       <lastBlock> (_, EpochBoundaryBlock) </lastBlock>
       <validators> Validators </validators> // TODO: which validators to be considered?
       ...
     </state>
     requires Epoch >=Int 1
rule <k> processJustification(Epoch) => . ... </k>
     requires Epoch <Int 1

syntax KItem ::= justify(Int)
rule <k> true ~> justify(Epoch) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <justified> Epoch |-> (_ => true) ... </justified>
       <lastJustified> _ => Epoch </lastJustified>
       ...
     </state>
rule <k> false ~> justify(_) => . ... </k>

syntax Bool ::= isJustifiable(Int, Int, Attestations, Validators) [function, functional]
rule isJustifiable(Epoch, EpochBoundaryBlock, Attestations, v(VM, VIDs))
  => isMajority(attestationsBalance(EpochBoundaryBlock, Attestations, VM), totalBalance(VM, VIDs))
     orBool Epoch ==Int 0 // the genesis block is justified by default
```
```{.k .kast}
  requires #isConcrete(Attestations) // TODO: drop this
```
```{.k .kore}
     [concrete]
```

```k
syntax Bool ::= isMajority(Int, Int) [function, functional]
rule isMajority(X, Total) => (X *Int 3) >=Int (Total *Int 2)  // (X / Total) >= 2/3
                             andBool Total >Int 0             // ensure no div-by-zero

syntax Int ::= attestationsBalance(Int, Attestations, ValidatorMap) [function, functional]
rule attestationsBalance(Target, A Attestations, VM)
  => #if A.target_block ==Int Target
     #then VM.effective_balance[A.attester]i
     #else 0
     #fi +Int attestationsBalance(Target, Attestations, VM)
rule attestationsBalance(_, .Attestations, _) => 0
```

### Finalization

```k
syntax KItem ::= processFinalization(Int)
rule <k> processFinalization(TargetEpoch)
      => isFinalizable(SourceEpoch, TargetEpoch, Justified)
      ~> finalize(SourceEpoch) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <justified> Justified </justified>
       ...
     </state>
     <state>
       <slot> firstSlotOf(TargetEpoch) </slot>
       <lastJustified> SourceEpoch </lastJustified>
       ...
     </state>
     requires TargetEpoch >=Int 1
rule <k> processFinalization(TargetEpoch) => . ... </k>
     requires TargetEpoch <Int 1

syntax KItem ::= finalize(Int)
rule <k> true ~> finalize(Epoch) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <finalized> Epoch |-> (_ => true) ... </finalized>
       <lastFinalized> _ => Epoch </lastFinalized>
       ...
     </state>
rule <k> false ~> finalize(_) => . ... </k>

// source : source+1 = target justified
// source : source+1 : source+2 = target justified
syntax Bool ::= isFinalizable(Int, Int, Map) [function] // not functional
rule isFinalizable(SourceEpoch, TargetEpoch, Justified)
  => isJustified(SourceEpoch, Justified) andBool isJustified(TargetEpoch, Justified)
     andBool (
                SourceEpoch +Int 1 ==Int TargetEpoch
       orBool ( SourceEpoch +Int 2 ==Int TargetEpoch andBool isJustified(SourceEpoch +Int 1, Justified) )
     )
// TODO: use rule priority
  requires TargetEpoch -Int SourceEpoch <=Int 2
rule isFinalizable(SourceEpoch, TargetEpoch, Justified) => false
  requires TargetEpoch -Int SourceEpoch >Int 2

syntax Bool ::= isJustified(Int, Map) [function] // not functional
rule isJustified(Epoch, Justified) => {Justified[Epoch]}:>Bool
/*
rule isJustified(Epoch, Epoch |-> true  _:Map) => true
rule isJustified(Epoch, Epoch |-> false _:Map) => false
*/
```

### Rewards and Penalties

```{.k .dynamic}
// process_rewards_and_penalties
syntax KItem ::= processRewardsPenalties(Int)
rule <k> processRewardsPenalties(Epoch)
      => processRewardsPenaltiesAux1(
           VIDs, VM, Epoch, Epoch -Int LastFinalizedEpoch,
                                                                     filterNotSlashed(VM, Attestations)  ,
                                  filterByTarget(EpochBoundaryBlock, filterNotSlashed(VM, Attestations)) ,
           filterByHead(BlockMap, filterByTarget(EpochBoundaryBlock, filterNotSlashed(VM, Attestations)))
         ) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, VIDs) </validators>
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
     <blocks> BlockMap </blocks>
     requires Epoch >=Int 2
rule processRewardsPenalties(Epoch) => .
     requires Epoch <Int 2

syntax KItem ::= processRewardsPenaltiesAux1(IntList, ValidatorMap, Int, Int, Attestations, Attestations, Attestations)
rule processRewardsPenaltiesAux1(VIDs, VM, Epoch, FinalityDelay, SourceAttestations, TargetAttestations, HeadAttestations)
  => processRewardsPenaltiesAux2(VIDs, VM, Epoch, FinalityDelay, SourceAttestations, TargetAttestations, HeadAttestations,
       lift(totalBalance(VM, getValidators(SourceAttestations))),
       lift(totalBalance(VM, getValidators(TargetAttestations))),
       lift(totalBalance(VM, getValidators(HeadAttestations))),
       lift(totalBalance(VM, activeValidators(v(VM,VIDs), Epoch)))
     )

syntax KItem ::= processRewardsPenaltiesAux2(IntList, ValidatorMap, Int, Int, Attestations, Attestations, Attestations, Int, Int, Int, Int)
rule processRewardsPenaltiesAux2(          VIDs, VM, Epoch, FinalityDelay, SourceAttestations, TargetAttestations, HeadAttestations, SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance)
  => processRewardsPenaltiesAux3(.IntList, VIDs, VM, Epoch, FinalityDelay, SourceAttestations, TargetAttestations, HeadAttestations, SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance)

syntax KItem ::= processRewardsPenaltiesAux3(IntList, IntList, ValidatorMap, Int, Int, Attestations, Attestations, Attestations, Int, Int, Int, Int)
rule (. => processRewardPenalty(VID, VM, Epoch, FinalityDelay, getBaseReward(VM.effective_balance[VID]i, TotalActiveBalance), SourceAttestations, TargetAttestations, HeadAttestations, SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance))
  ~> processRewardsPenaltiesAux3(G_VIDs => VID G_VIDs, VID VIDs => VIDs, VM, Epoch, FinalityDelay, SourceAttestations, TargetAttestations, HeadAttestations, SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance)
rule processRewardsPenaltiesAux3(_, .IntList, _, _, _, _, _, _, _, _, _, _) => .

syntax KItem ::= processRewardPenalty(Int, ValidatorMap, Int, Int, Int, Attestations, Attestations, Attestations, Int, Int, Int, Int)
/*
rule processRewardPenalty(V, Epoch, FinalityDelay, BaseReward,
                          SourceAttestations,     TargetAttestations,     HeadAttestations,
                          SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance)
  => #it(
       isActiveValidator(V, Epoch) orBool ( V.slashed andBool Epoch +Int 1 <Int V.withdrawable_epoch )
     ,
       // Matching Rewards and Penalties
       #ite(
         V.id inA SourceAttestations
       ,
         increaseBalance(V.id, getMatchingReward(BaseReward, SourceAttestingBalance, TotalActiveBalance))
       ,
         decreaseBalance(V.id, BaseReward)
       )
       ~>
       #ite(
         V.id inA TargetAttestations
       ,
         increaseBalance(V.id, getMatchingReward(BaseReward, TargetAttestingBalance, TotalActiveBalance))
       ,
         decreaseBalance(V.id, BaseReward)
       )
       ~>
       #ite(
         V.id inA HeadAttestations
       ,
         increaseBalance(V.id, getMatchingReward(BaseReward, HeadAttestingBalance, TotalActiveBalance))
       ,
         decreaseBalance(V.id, BaseReward)
       )
       ~>
       // Proposer Rewards
       #it(
         V.id inA SourceAttestations
       ,
         increaseBalance(minByInclusionDelay(V.id, SourceAttestations).proposer, BaseReward /Int PROPOSER_REWARD_QUOTIENT)
         ~>
         increaseBalance(V.id, getInclusionReward(BaseReward, minByInclusionDelay(V.id, SourceAttestations).inclusion_delay))
       )
       ~>
       // Inactivity Penalties
       #it(
         FinalityDelay >Int MIN_EPOCHS_TO_INACTIVITY_PENALTY
       ,
         decreaseBalance(V.id, BASE_REWARDS_PER_EPOCH *Int BaseReward)
         ~>
         #it(
           notBool (V.id inA TargetAttestations)
         ,
           decreaseBalance(V.id, getInactivityPenalty(V.effective_balance, FinalityDelay))
         )
       )
     )
*/

// TODO: process proposer rewards
rule processRewardPenalty(VID, VM, Epoch, FinalityDelay, BaseReward,
                          SourceAttestations,     TargetAttestations,     HeadAttestations,
                          SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance)
  => #it(
       isActiveValidator(VID, VM, Epoch) orBool ( VM.slashed[VID]b andBool Epoch +Int 1 <Int VM.withdrawable_epoch[VID]i )
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
                    #then (0 -Int getInactivityPenalty(VM.effective_balance[VID]i, FinalityDelay))
                    #else 0
                    #fi
         #else 0
         #fi
       )
     )

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
       //m(... balance: BM => BM [ VID <- BM[VID]i +Int N ]i)
         m(SM
         , BM => BM [ VID <- BM[VID]i +Int N ]i
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

syntax Int ::= totalBalance(ValidatorMap, IntList) [function, smtlib(totalBalance)]
rule totalBalance(VM, VID VIDs) => VM.effective_balance[VID]i +Int totalBalance(VM, VIDs)
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

syntax Attestations ::= filterByHead(BlockMap, Attestations) [function, smtlib(filterByHead)]
rule filterByHead(BlockMap, A As) => #if A.head_block ==Int BlockMap[A.slot]k.id
                               #then A filterByHead(BlockMap, As)
                               #else   filterByHead(BlockMap, As)
                               #fi
rule filterByHead(_, .Attestations) => .Attestations

syntax Attestations ::= filterNotSlashed(ValidatorMap, Attestations) [function, smtlib(filterNotSlashed)]
rule filterNotSlashed(VM, A As) => #if VM.slashed[A.attester]b
                                   #then   filterNotSlashed(VM, As)
                                   #else A filterNotSlashed(VM, As)
                                   #fi
rule filterNotSlashed(_, .Attestations) => .Attestations

syntax IntList ::= getValidators(Attestations) [function, smtlib(getValidators)]
rule getValidators(As) => getValidatorsAux2(getValidatorsAux1(As, .Map))
     [concrete]

syntax Map ::= getValidatorsAux1(Attestations, Map) [function]
rule getValidatorsAux1(A As => As, M => M [ A.attester <- true ])
rule getValidatorsAux1(.Attestations, M) => M

syntax IntList ::= getValidatorsAux2(Map) [function]
rule getValidatorsAux2(V |-> true M) => V getValidatorsAux2(M)
rule getValidatorsAux2(.Map) => .IntList
```

### Validator Updates

```{.k .dynamic}
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
           isActiveValidator(VID, VM, epochOf(Slot) -Int 1) andBool VM.effective_balance[VID]i <=Int EJECTION_BALANCE
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
           isActivationEligible(VID, VM)
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
       //m(... effective_balance: EBM
       //    , activation_eligibility: AEM => AEM [ VID <- epochOf(Slot) ]i
       //)
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
syntax Bool ::= isActivationEligible(Int, ValidatorMap) [function, functional]
rule isActivationEligible(VID, VM)
  => VM.activation_eligibility_epoch[VID]i ==Int FAR_FUTURE_EPOCH andBool
     VM.effective_balance[VID]i ==Int MAX_EFFECTIVE_BALANCE

syntax Kitem ::= processValidatorActivation()
rule <k> processValidatorActivation()
      => activateValidators(activationQueueUptoChurnLimit(Validators, FinalizedEpoch, epochOf(Slot) -Int 1)) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> Validators </validators>
       <lastFinalized> FinalizedEpoch </lastFinalized>
       ...
     </state>

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
       //m(... activation_epoch: AM => AM [ VID <- delayedActivationExitEpoch(epochOf(Slot) -Int 1) ]i)
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

syntax IntList ::= activationQueueUptoChurnLimit(Validators, Int, Int) [function, functional]
rule activationQueueUptoChurnLimit(Validators, FinalizedEpoch, CurrentEpoch)
  => take(
       churnLimit(size(activeValidators(Validators, CurrentEpoch))),
       sort(activationQueue(Validators, FinalizedEpoch))
     )

syntax IntList ::= activationQueue(Validators, Int) [function, functional, smtlib(activationQueue)]
rule activationQueue(v(VM, VID VIDs), FinalizedEpoch)
  => #if isValidValidatorToActivate(VID, VM, FinalizedEpoch)
     #then VID activationQueue(v(VM, VIDs), FinalizedEpoch)
     #else     activationQueue(v(VM, VIDs), FinalizedEpoch)
     #fi
rule activationQueue(v(_, .IntList), _) => .IntList

syntax Bool ::= isValidValidatorToActivate(Int, ValidatorMap, Int) [function]
rule isValidValidatorToActivate(VID, VM, FinalizedEpoch)
  => VM.activation_eligibility_epoch[VID]i <=Int FinalizedEpoch andBool // is_eligible_for_activation
     VM.activation_epoch[VID]i ==Int FAR_FUTURE_EPOCH
```

## Block Processing

```k
// process_block
// process_block_header
// process_operations
rule <k> processBlock(#Block((Slot, ID), Parent, Slashings, Attestations, Deposits, VoluntaryExits))
      => processSlashings(Slashings)
      ~> processAttestations(Attestations)
```
```{.k .dynamic}
      ~> processDeposits(Deposits)
      ~> processVoluntaryExits(VoluntaryExits)
```
```k
      ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <lastBlock> Parent => (Slot, ID) </lastBlock>
       ...
     </state>
     <blocks>
       BlockMap => BlockMap [ Slot <- #Block((Slot, ID), Parent, Slashings, Attestations, Deposits, VoluntaryExits) ]k
     </blocks>
     // TODO: check if the block proposer is valid (assigned, not slashed)
```

### Slashings

```k
// capturing both proposer slashings and attester slashings

// process_proposer_slashing
// process_attester_slashing
syntax KItem ::= processSlashings(Slashings)
rule processSlashings(S Slashings) => processSlashing(S) ~> processSlashings(Slashings)
rule processSlashings(.Slashings) => .

syntax KItem ::= processSlashing(Slashing)
rule <k> processSlashing(#Slashing(A1, A2))
      =>
```
```{.k .dynamic}
         initiateValidatorExit(A1.attester) ~>
```
```k
         slashValidator(A1.attester) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>
     requires isSlashableAttestation(A1, A2) // assertion
      andBool A1.attester ==Int A2.attester
// TODO:
// rule processSlashing(#Slashing(A1, A2)) => #bottom [owise]

// slash_validator
syntax KItem ::= slashValidator(Int)
rule <k> slashValidator(VID) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <slashedBalance> S => S +Int EBM[VID]i </slashedBalance> // TODO: store slashed balance for each epoch
       <validators> v(
       //m(... slashed: SM => SM [ VID <- true ]b
       //    , balance: BM => BM [ VID <- maxInt(0, BM[VID]i -Int (EBM[VID]i /Int MIN_SLASHING_PENALTY_QUOTIENT)) ]i
       //    , effective_balance: EBM
       //    , withdrawable_epoch: WM => WM [ VID <- maxInt(WM[VID]i, epochOf(Slot) +Int EPOCHS_PER_SLASHINGS_VECTOR) ]i
       //)
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

syntax Bool ::= isSlashableAttestation(Attestation, Attestation) [function, functional]
rule isSlashableAttestation(A1, A2)
  => ( A1 =/=K A2 andBool A1.target_epoch ==Int A2.target_epoch )
     orBool
     ( A1.source_epoch <Int A2.source_epoch andBool A2.target_epoch <Int A1.target_epoch )
  // TODO: the following case not needed?
  // orBool
  // ( A2.source_epoch <Int A1.source_epoch andBool A1.target_epoch <Int A2.target_epoch )
```

### Attestations

```k
// process_attestation
syntax KItem ::= processAttestations(Attestations)
rule processAttestations(A Attestations) => processAttestation(A) ~> processAttestations(Attestations)
rule processAttestations(.Attestations) => .

syntax KItem ::= processAttestation(Attestation)
rule processAttestation(A)
  => checkAttestation(A)
  ~> addAttestation(A)

syntax KItem ::= addAttestation(Attestation)
rule <k> true ~> addAttestation(A) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <attested>
         A.target_epoch |-> (As:Attestations => A As)
         ...
       </attested>
       ...
     </state>
rule <k> false ~> addAttestation(_) => #bottom ... </k>

syntax KItem ::= checkAttestation(Attestation)
rule <k> checkAttestation(A) => isValidAttestation(A, Slot, JEpoch, JBlock, VM.slashed[A.attester]b) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>
     <state>
       <slot> firstSlotOf(A.target_epoch) </slot>
       <lastJustified> JEpoch </lastJustified>
       ...
     </state>
     <state>
       <slot> firstSlotOf(JEpoch) </slot>
       <lastBlock> (_, JBlock) </lastBlock>
       ...
     </state>
     requires A.target_epoch >Int 0

rule <k> checkAttestation(A) => isValidAttestation(A, Slot, JEpoch, JBlock, VM.slashed[A.attester]b) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>
     <state>
       <slot> firstSlotOf(A.target_epoch) </slot>
       <lastJustified> JEpoch </lastJustified>
       <lastBlock> (_, JBlock) </lastBlock>
       ...
     </state>
     requires A.target_epoch ==Int 0

syntax Bool ::= isValidAttestation(Attestation, Int, Int, Int, Bool) [function, functional]
rule isValidAttestation(A, Slot, SourceEpoch, SourceBlock, Slashed)
  =>         A.source_epoch ==Int SourceEpoch
     andBool A.source_block ==Int SourceBlock
     andBool A.slot +Int MIN_ATTESTATION_INCLUSION_DELAY <=Int Slot andBool Slot <=Int A.slot +Int MAX_ATTESTATION_INCLUSION_DELAY
     andBool epochOf(A.slot) ==Int A.target_epoch
     andBool notBool Slashed // TODO: is this checked in spec?
     // TODO: check if A.attester is assigned to A.slot
```

### Deposits

```{.k .dynamic}
// process_deposit
syntax KItem ::= processDeposits(Deposits)
rule processDeposits(D Deposits) => processDeposit(D) ~> processDeposits(Deposits)
rule processDeposits(.Deposits) => .

syntax KItem ::= processDeposit(Deposit)
rule <k> processDeposit(D) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(
       //m(... balance: BM => BM [ D.sender <- BM[D.sender]i +Int D.amount ]i) // no change to effective_balance
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
       //m(... slashed:             SM => SM [ D.sender <- false ]b
       //    , balance:             BM => BM [ D.sender <- D.amount ]i
       //    , effective_balance: EBM => EBM [ D.sender <- minInt(D.amount, MAX_EFFECTIVE_BALANCE) ]i // effective_balance cap
       //    , activation_eligibility_epoch: FAR_FUTURE_EPOCH
       //    , activation_epoch:             FAR_FUTURE_EPOCH
       //    , exit_epoch:                   FAR_FUTURE_EPOCH
       //    , withdrawable_epoch:           FAR_FUTURE_EPOCH
       //)
         m(SM  => SM  [ D.sender <- false ]b
         , BM  => BM  [ D.sender <- D.amount ]i
         , EBM => EBM [ D.sender <- minInt(D.amount, MAX_EFFECTIVE_BALANCE) ]i // effective_balance cap
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

```{.k .dynamic}
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
      => #if isValidVoluntaryExit(E, VM, epochOf(Slot))
         #then initiateValidatorExit(E.validator)
         #else #bottom
         #fi ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>

syntax Bool ::= isValidVoluntaryExit(VoluntaryExit, ValidatorMap, Int) [function]
rule isValidVoluntaryExit(E, VM, CurrEpoch)
  => isActiveValidator(E.validator, VM, CurrEpoch)
     andBool VM.exit_epoch[E.validator]i ==Int FAR_FUTURE_EPOCH
     andBool CurrEpoch >=Int E.epoch
     andBool CurrEpoch >=Int VM.activation_epoch[E.validator]i +Int PERSISTENT_COMMITTEE_PERIOD

// is_active_validator
syntax Bool ::= isActiveValidator(Int, ValidatorMap, Int) [function, functional]
rule isActiveValidator(VID, VM, Epoch)
  => VM.activation_epoch[VID]i <=Int Epoch andBool Epoch <Int VM.exit_epoch[VID]i

// initiate_validator_exit
syntax KItem ::= initiateValidatorExit(Int)
rule <k> initiateValidatorExit(VID)
      => #it(
           VM.exit_epoch[VID]i ==Int FAR_FUTURE_EPOCH
         ,
           setExitEpoch(VID, computeExitEpoch(v(VM, VIDs), epochOf(Slot)))
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
       //m(... exit_epoch:         EM => EM [ VID <- ExitEpoch ]i
       //    , withdrawable_epoch: WM => WM [ VID <- ExitEpoch +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY ]i
       //)
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

syntax Int ::= computeExitEpoch(Validators, Int) [function, functional]
             | computeExitEpochAux(Validators, Int, Int) [function, functional]
rule [computeExitEpoch]:
     computeExitEpoch(v(VM, VIDs), CurrentEpoch)
  => computeExitEpochAux(
       v(VM, VIDs),
       maxInt(maxExitEpoch(VIDs, VM.exit_epoch), delayedActivationExitEpoch(CurrentEpoch)),
       size(activeValidators(v(VM, VIDs), CurrentEpoch))
     )
rule computeExitEpochAux(v(VM, VIDs), ExitEpoch, ActiveValidatorSize)
  => #if countValidatorsToExit(VIDs, VM.exit_epoch, ExitEpoch) >=Int churnLimit(ActiveValidatorSize)
     #then ExitEpoch +Int 1
     #else ExitEpoch
     #fi

syntax Int ::= maxExitEpoch(IntList, IMap) [function, functional, smtlib(maxExitEpoch)]
rule maxExitEpoch(VID VIDs, EM) => maxInt(EM[VID]i, maxExitEpoch(VIDs, EM)) requires EM[VID]i =/=Int FAR_FUTURE_EPOCH
rule maxExitEpoch(VID VIDs, EM) =>                  maxExitEpoch(VIDs, EM)  requires EM[VID]i  ==Int FAR_FUTURE_EPOCH
rule maxExitEpoch(.IntList, _) => 0

syntax Int ::= countValidatorsToExit(IntList, IMap, Int) [function, functional, smtlib(countValidatorsToExit)]
rule countValidatorsToExit(VID VIDs, EM, ExitEpoch)
  => #if EM[VID]i ==Int ExitEpoch #then 1 #else 0 #fi +Int countValidatorsToExit(VIDs, EM, ExitEpoch)
rule countValidatorsToExit(.IntList, _, _) => 0

syntax IntList ::= activeValidators(Validators, Int) [function, functional, smtlib(activeValidators)]
rule activeValidators(v(VM, VID VIDs), Epoch)
  => #if isActiveValidator(VID, VM, Epoch)
     #then VID activeValidators(v(VM, VIDs), Epoch)
     #else     activeValidators(v(VM, VIDs), Epoch)
     #fi
rule activeValidators(v(_, .IntList), _) => .IntList

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
