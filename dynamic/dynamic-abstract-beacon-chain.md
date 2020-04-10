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
      <validators> v(.ValidatorMap, .IntList) </validators> // ValidatorID -> ValidatorState
      <slashedBalance> 0 </slashedBalance> // slashed balance
      <attested> .Map </attested> // Epoch -> Attestations
      <justified> .Map </justified> // Epoch -> Block option
      <finalized> .Map </finalized> // Epoch -> Block option
      // derived info
      <lastBlock> (0,0) </lastBlock> // last block (slot, id)
      <lastJustified> 0 </lastJustified> // last justified (epoch, block id)
      <lastFinalized> 0 </lastFinalized> // last finalized (epoch, block id)
    </state>
  </states>
  // blockchain
  <blocks> .BlockMap </blocks>
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
           .ValidatorMap
           [ 90000 <- #Validator(90000,false,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH)) ]v
           [ 90001 <- #Validator(90001,false,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH)) ]v
           [ 90002 <- #Validator(90002,false,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH)) ]v
           [ 90003 <- #Validator(90003,false,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH)) ]v
           [ 90004 <- #Validator(90004,false,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH)) ]v
           [ 90005 <- #Validator(90005,false,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH)) ]v
           [ 90006 <- #Validator(90006,false,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH)) ]v
         ,
           90000 90001 90002 90003 90004 90005 90006 .IntList
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
     <blocks> .BlockMap => .BlockMap [ 0 <- #Block((0,0),(-1,-1),.Slashings,.Attestations,.Deposits,.VoluntaryExits) ]b </blocks>
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
rule isJustifiable(Epoch, EpochBoundaryBlock, Attestations, Validators)
  => isMajority(attestationsBalance(EpochBoundaryBlock, Attestations, Validators), totalBalance(Validators.vmap, Validators.vset))
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

syntax Int ::= attestationsBalance(Int, Attestations, Validators) [function, functional]
rule attestationsBalance(Target, A Attestations, Validators)
  => #if A.target_block ==Int Target
     #then Validators.vmap[A.attester]v.effective_balance
     #else 0
     #fi +Int attestationsBalance(Target, Attestations, Validators)
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
                                                               Attestations  ,
                            filterByTarget(EpochBoundaryBlock, Attestations ),
           filterByHead(BM, filterByTarget(EpochBoundaryBlock, Attestations))
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
     <blocks> BM </blocks>
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
rule (. => processRewardPenalty(VM[VID]v, Epoch, FinalityDelay, getBaseReward(VM[VID]v, TotalActiveBalance),
                                                                             SourceAttestations,     TargetAttestations,     HeadAttestations,
                                                                             SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance))
  ~> processRewardsPenaltiesAux2(VID VIDs => VIDs, VM, Epoch, FinalityDelay, SourceAttestations,     TargetAttestations,     HeadAttestations,
                                                                             SourceAttestingBalance, TargetAttestingBalance, HeadAttestingBalance, TotalActiveBalance)
rule processRewardsPenaltiesAux2(.IntList, _, _, _, _, _, _, _, _, _, _) => .

syntax KItem ::= processRewardPenalty(Validator, Int, Int, Int, Attestations, Attestations, Attestations, Int, Int, Int, Int)
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
         increaseBalance(V.id, BaseReward *Int (SourceAttestingBalance /Int EFFECTIVE_BALANCE_INCREMENT)
                                          /Int (TotalActiveBalance     /Int EFFECTIVE_BALANCE_INCREMENT))
       ,
         decreaseBalance(V.id, BaseReward)
       )
       ~>
       #ite(
         V.id inA TargetAttestations
       ,
         increaseBalance(V.id, BaseReward *Int (TargetAttestingBalance /Int EFFECTIVE_BALANCE_INCREMENT)
                                          /Int (TotalActiveBalance     /Int EFFECTIVE_BALANCE_INCREMENT))
       ,
         decreaseBalance(V.id, BaseReward)
       )
       ~>
       #ite(
         V.id inA HeadAttestations
       ,
         increaseBalance(V.id, BaseReward *Int (HeadAttestingBalance   /Int EFFECTIVE_BALANCE_INCREMENT)
                                          /Int (TotalActiveBalance     /Int EFFECTIVE_BALANCE_INCREMENT))
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
         increaseBalance(V.id, (BaseReward -Int BaseReward /Int PROPOSER_REWARD_QUOTIENT) /Int minByInclusionDelay(V.id, SourceAttestations).inclusion_delay)
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
           decreaseBalance(V.id, V.effective_balance *Int FinalityDelay /Int INACTIVITY_PENALTY_QUOTIENT)
         )
       )

     )

// get_base_reward
syntax Int ::= getBaseReward(Validator, Int) [function, smtlib(getBaseReward)]
rule getBaseReward(V, SafeTotalActiveBalance)
  => V.effective_balance *Int BASE_REWARD_FACTOR
     /Int sqrtInt(SafeTotalActiveBalance)
     /Int BASE_REWARDS_PER_EPOCH
     [concrete]

// increase_balance
syntax KItem ::= increaseBalance(Int, Int)
rule <k> increaseBalance(VID, N) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM => VM [ VID <- VM[VID]v with balance = VM[VID]v.balance +Int N ]v, VIDs) </validators>
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
rule totalBalance(VM, VID VIDs) => VM[VID]v.effective_balance +Int totalBalance(VM, VIDs)
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
rule filterByHead(BM, A As) => #if A.head_block ==Int BM[A.slot]b.id
                               #then A filterByHead(BM, As)
                               #else   filterByHead(BM, As)
                               #fi
rule filterByHead(_, .Attestations) => .Attestations

syntax IntList ::= getValidators(Attestations) [function, smtlib(getValidators)]
rule getValidators(A As) => A.attester getValidators(A As) // TODO: drop duplicates
rule getValidators(.Attestations) => .IntList
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
rule processValidatorEjections(VID VIDs) => processValidatorEjection(VID) ~> processValidatorEjections(VIDs)
rule processValidatorEjections(.IntList) => .

syntax KItem ::= processValidatorEjection(Int)
rule <k> processValidatorEjection(VID)
      => #if isActiveValidator(VM[VID]v, epochOf(Slot) -Int 1) andBool VM[VID]v.effective_balance <=Int EJECTION_BALANCE
         #then initiateValidatorExit(VM[VID]v)
         #else .
         #fi ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>

syntax KItem ::= updateActivationEligibilities(IntList)
rule updateActivationEligibilities(VID VIDs) => updateActivationEligibility(VID) ~> updateActivationEligibilities(VIDs)
rule updateActivationEligibilities(.IntList) => .

syntax KItem ::= updateActivationEligibility(Int)
rule <k> updateActivationEligibility(VID) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(
         VM
       =>
         #if isActivationEligible(VM[VID]v)
         #then VM [ VID <- VM[VID]v with activation_eligibility_epoch = epochOf(Slot) ]v
         #else VM
         #fi
       ,
         _
       ) </validators>
       ...
     </state>

// is_eligible_for_activation_queue
syntax Bool ::= isActivationEligible(Validator) [function, functional]
rule isActivationEligible(V)
  => V.activation_eligibility_epoch ==Int FAR_FUTURE_EPOCH andBool
     V.effective_balance ==Int MAX_EFFECTIVE_BALANCE

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

syntax KItem ::= activateValidators(ValidatorList)
rule activateValidators(V Vs) => activateValidator(V) ~> activateValidators(Vs)
rule activateValidators(.ValidatorList) => .

syntax KItem ::= activateValidator(Validator)
rule <k> activateValidator(V) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(
         VM => VM [ V.id <- V with activation_epoch = delayedActivationExitEpoch(epochOf(Slot) -Int 1) ]v
       ,
         _
       ) </validators>
       ...
     </state>

syntax ValidatorList ::= activationQueueUptoChurnLimit(Validators, Int, Int) [function, functional]
rule activationQueueUptoChurnLimit(Validators, FinalizedEpoch, CurrentEpoch)
  => take(
       churnLimit(size(activeValidators(Validators, CurrentEpoch))),
       sort(activationQueue(Validators, FinalizedEpoch))
     )

syntax ValidatorList ::= activationQueue(Validators, Int) [function, functional]
rule activationQueue(v(VM, VID VIDs), FinalizedEpoch)
  => #if VM[VID]v.activation_eligibility_epoch <=Int FinalizedEpoch andBool // is_eligible_for_activation
         VM[VID]v.activation_epoch ==Int FAR_FUTURE_EPOCH
     #then VM[VID]v activationQueue(v(VM, VIDs), FinalizedEpoch)
     #else          activationQueue(v(VM, VIDs), FinalizedEpoch)
     #fi
rule activationQueue(v(_, .IntList), _) => .ValidatorList
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
       BM => BM [ Slot <- #Block((Slot, ID), Parent, Slashings, Attestations, Deposits, VoluntaryExits) ]b
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
         initiateValidatorExit(VM[A1.attester]v) ~>
```
```k
         slashValidator(VM[A1.attester]v) ... </k>
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
syntax KItem ::= slashValidator(Validator)
rule <k> slashValidator(V) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <slashedBalance> S => S +Int V.effective_balance </slashedBalance> // TODO: store slashed balance for each epoch
       <validators> v(
         VM => VM [ V.id <- V with slashed = true
                              with withdrawable_epoch = maxInt(V.withdrawable_epoch, epochOf(Slot) +Int EPOCHS_PER_SLASHINGS_VECTOR)
                              with balance = maxInt(0, V.balance -Int (V.effective_balance /Int MIN_SLASHING_PENALTY_QUOTIENT)) ]v
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
rule <k> checkAttestation(A) => isValidAttestation(A, Slot, JEpoch, JBlock, VM[A.attester]v) ... </k>
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

rule <k> checkAttestation(A) => isValidAttestation(A, Slot, JEpoch, JBlock, VM[A.attester]v) ... </k>
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

syntax Bool ::= isValidAttestation(Attestation, Int, Int, Int, Validator) [function, functional]
rule isValidAttestation(A, Slot, SourceEpoch, SourceBlock, V)
  =>         A.source_epoch ==Int SourceEpoch
     andBool A.source_block ==Int SourceBlock
     andBool A.slot +Int MIN_ATTESTATION_INCLUSION_DELAY <=Int Slot andBool Slot <=Int A.slot +Int MAX_ATTESTATION_INCLUSION_DELAY
     andBool epochOf(A.slot) ==Int A.target_epoch
     andBool notBool V.slashed // TODO: is this checked in spec?
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
         VM => VM [ D.sender <- VM[D.sender]v with balance = VM[D.sender]v.balance +Int D.amount ]v // no change to effective_balance
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
         VM => VM [ D.sender <- #Validator(D.sender, false,
                                           (D.amount, minInt(D.amount, MAX_EFFECTIVE_BALANCE)), // effective_balance cap
                                           (FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH),
                                           (FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH)) ]v
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
rule processVoluntaryExits(E Exits) => processVoluntaryExit(E) ~> processVoluntaryExits(Exits)
rule processVoluntaryExits(.VoluntaryExits) => .

syntax KItem ::= processVoluntaryExit(VoluntaryExit)
rule <k> processVoluntaryExit(E)
      => initiateValidatorExit(VM[E.validator]v) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(VM, _) </validators>
       ...
     </state>
     requires isActiveValidator(VM[E.validator]v, epochOf(Slot))
      andBool VM[E.validator]v.exit_epoch ==Int FAR_FUTURE_EPOCH
      andBool epochOf(Slot) >=Int E.epoch
      andBool epochOf(Slot) >=Int VM[E.validator]v.activation_epoch +Int PERSISTENT_COMMITTEE_PERIOD
// TODO:
// rule processVoluntaryExit(E) => #bottom [owise]

// is_active_validator
syntax Bool ::= isActiveValidator(Validator, Int) [function, functional]
rule isActiveValidator(V, Epoch)
  => V.activation_epoch <=Int Epoch andBool Epoch <Int V.exit_epoch

// initiate_validator_exit
syntax KItem ::= initiateValidatorExit(Validator)
rule <k> initiateValidatorExit(V)
      => setExitEpoch(V, computeExitEpoch(Validators, epochOf(Slot))) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> Validators </validators>
       ...
     </state>
     requires V.exit_epoch ==Int FAR_FUTURE_EPOCH
rule initiateValidatorExit(V) => .
     requires V.exit_epoch =/=Int FAR_FUTURE_EPOCH

syntax KItem ::= setExitEpoch(Validator, Int)
rule <k> setExitEpoch(V, ExitEpoch) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(
         VM => VM [ V.id <- V with exit_epoch         = ExitEpoch
                              with withdrawable_epoch = ExitEpoch +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY ]v
       ,
         _
       ) </validators>
       ...
     </state>

syntax Int ::= computeExitEpoch(Validators, Int) [function, functional]
             | computeExitEpochAux(Validators, Int, Int) [function, functional]
rule computeExitEpoch(Validators, CurrentEpoch)
  => computeExitEpochAux(
       Validators,
       maxInt(maxExitEpoch(Validators), delayedActivationExitEpoch(CurrentEpoch)),
       size(activeValidators(Validators, CurrentEpoch))
     )
rule computeExitEpochAux(Validators, ExitEpoch, ActiveValidatorSize)
  => #if countValidatorsToExit(Validators, ExitEpoch) >=Int churnLimit(ActiveValidatorSize)
     #then ExitEpoch +Int 1
     #else ExitEpoch
     #fi

syntax Int ::= maxExitEpoch(Validators) [function, functional, smtlib(maxExitEpoch)]
rule maxExitEpoch(v(VM, VID VIDs)) => maxInt(VM[VID]v.exit_epoch, maxExitEpoch(v(VM, VIDs))) requires VM[VID]v.exit_epoch =/=Int FAR_FUTURE_EPOCH
rule maxExitEpoch(v(VM, VID VIDs)) =>                             maxExitEpoch(v(VM, VIDs))  requires VM[VID]v.exit_epoch  ==Int FAR_FUTURE_EPOCH
rule maxExitEpoch(v(_, .IntList)) => 0

syntax Int ::= countValidatorsToExit(Validators, Int) [function, functional, smtlib(countValidatorsToExit)]
rule countValidatorsToExit(v(VM, VID VIDs), ExitEpoch)
  => #if VM[VID]v.exit_epoch ==Int ExitEpoch #then 1 #else 0 #fi +Int countValidatorsToExit(v(VM, VIDs), ExitEpoch)
rule countValidatorsToExit(v(_, .IntList), _) => 0

syntax IntList ::= activeValidators(Validators, Int) [function, functional, smtlib(activeValidators)]
rule activeValidators(v(VM, VID VIDs), Epoch)
  => #if isActiveValidator(VM[VID]v, Epoch)
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
