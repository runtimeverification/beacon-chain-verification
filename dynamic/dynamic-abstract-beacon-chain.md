# Dynamic Abstract Model of Beacon Chain State Transition

This presents an abstract model of the Beacon chain state transition system.

This model is designed for the safety and liveness proofs of the Beacon chain finality mechanism. It abstracts aways certain unnecessary details of the system, including the cached history mechanism for the space efficiency, validation of cryptographic data (public keys, signatures, commitments, etc.), and the committee assignment mechanism.

The reward and penalty mechanism is not yet modeled here.

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
      <validators> v(.ValidatorMap, .Set) </validators> // ValidatorID -> ValidatorState
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
  <blocks>
    <block multiplicity="*" type="Map">
      <bSlot> 0 </bSlot> <bID> 0 </bID> // unique block id (e.g., hash)
      <parent> (0,0) </parent> // parent block (slot, id)
      <slashings> .Slashings </slashings>
      <attestations> .Attestations </attestations>
      <deposits> .Deposits </deposits>
      <exits> .VoluntaryExits </exits>
    </block>
  </blocks>
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
           SetItem(90000) SetItem(90001) SetItem(90002) SetItem(90003) SetItem(90004) SetItem(90005) SetItem(90006) .Set
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
     <blocks> .Bag =>
       <block>
         <bSlot> 0 </bSlot> <bID> 0 </bID>
         <parent> (-1,-1) </parent>
         <slashings> .Slashings </slashings>
         <attestations> .Attestations </attestations>
         <deposits> .Deposits </deposits>
         <exits> .VoluntaryExits </exits>
       </block>
     </blocks>
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
     requires Slot <Int NewBlock.slot
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
```

Updating the cached history is not required here since the full history is recorded in the abstract model.

```k
// process_slot
rule <k> processSlot() => . ... </k>
```

## Epoch Processing

Note that `Slot` is equal to `state.slot + 1` of the concrete model.

```k
// TODO: add process_rewards_and_penalties, process_slashings, process_final_updates (for updating effective balances with hysteresis)
// process_epoch
rule <k> processEpoch()
      => processJustification(epochOf(Slot) -Int 2)
      ~> processJustification(epochOf(Slot) -Int 1)
      ~> processFinalization(epochOf(Slot) -Int 2)
      ~> processFinalization(epochOf(Slot) -Int 1)
```
```{.k .dynamic}
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
  => isMajority(attestationsBalance(EpochBoundaryBlock, Attestations, Validators), totalBalance(Validators))
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

syntax Int ::= totalBalance(Validators) [function, functional]
rule totalBalance(v(VM, SetItem(VID) VIDs:Set)) => VM[VID]v.effective_balance +Int totalBalance(v(VM, VIDs))
rule totalBalance(v(_, .Set)) => 0
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

### Validator Updates

```{.k .dynamic}
// TODO: check if no mistake was made as this process is associated with the previous epoch
// process_registry_updates
syntax KItem ::= processValidatorUpdates()
rule <k> processValidatorUpdates()
      => processValidatorEjection(Validators)    // TODO: processValidatorEjection comes after updateActivationEligibility in the concrete model
      ~> updateActivationEligibility(Validators)
      ~> processValidatorActivation() ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> Validators </validators>
       ...
     </state>

syntax KItem ::= processValidatorEjection(Validators)
rule <k> processValidatorEjection(v(VM, SetItem(VID) VIDs:Set))
      => #if isActiveValidator(VM[VID]v, epochOf(Slot) -Int 1) andBool VM[VID]v.effective_balance <=Int EJECTION_BALANCE
         #then initiateValidatorExit(VM[VID]v)
         #else .
         #fi
      ~> processValidatorEjection(v(VM, VIDs)) ... </k>
     <currentSlot> Slot </currentSlot>
rule processValidatorEjection(v(_, .Set)) => .

syntax KItem ::= updateActivationEligibility(Validators)
rule <k> updateActivationEligibility(v(VM0, SetItem(VID) VIDs:Set))
      => updateActivationEligibility(v(VM0, VIDs)) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(
         VM
       =>
         #if isActivationEligible(VM[VID]v)
         #then VM [ VID <- VM[VID]v withInt "activation_eligibility_epoch" = epochOf(Slot) ]v
         #else VM
         #fi
       /*
         VM => VM [ VID <- #if isActivationEligible(VM[VID]v)
                           #then VM[VID]v withInt "activation_eligibility_epoch" = epochOf(Slot)
                           #else VM[VID]v
                           #fi ]v
       */
       ,
         _
       ) </validators>
       ...
     </state>
rule updateActivationEligibility(v(_, .Set)) => .

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

syntax KItem ::= activateValidators(List)
rule <k> activateValidators(ListItem(V:Validator) Vs)
      => activateValidators(                      Vs) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> v(
         VM => VM [ V.id <- V withInt "activation_epoch" = delayedActivationExitEpoch(epochOf(Slot) -Int 1) ]v
       ,
         _
       ) </validators>
       ...
     </state>
rule activateValidators(.List) => .

syntax List ::= activationQueueUptoChurnLimit(Validators, Int, Int) [function, functional]
rule activationQueueUptoChurnLimit(Validators, FinalizedEpoch, CurrentEpoch)
  => dropBeyondLimit(
       activationQueue(Validators, FinalizedEpoch),
       churnLimit(size(activeValidators(Validators, CurrentEpoch)))
     )

syntax List ::= activationQueue(Validators, Int) [function, functional]
rule activationQueue(v(VM, SetItem(VID) VIDs:Set), FinalizedEpoch)
  => #if VM[VID]v.activation_eligibility_epoch <=Int FinalizedEpoch andBool // is_eligible_for_activation
         VM[VID]v.activation_epoch ==Int FAR_FUTURE_EPOCH
     #then ListItem(VM[VID]v) activationQueue(v(VM, VIDs), FinalizedEpoch)
     #else                    activationQueue(v(VM, VIDs), FinalizedEpoch)
     #fi
rule activationQueue(v(_, .Set), _) => .List

syntax List ::= dropBeyondLimit(List, Int) [function] // functional only for Validators
rule dropBeyondLimit(Vs, Limit) => Vs requires size(Vs) <=Int Limit
rule dropBeyondLimit(Vs, Limit)
  => dropBeyondLimit(dropLastActivationEligibleValidator(Vs), Limit)
     requires size(Vs) >Int Limit

syntax List ::= dropLastActivationEligibleValidator(List)                     [function] // functional only for Validators
              | dropLastActivationEligibleValidatorAux(List, Validator, List) [function] // functional only for Validators
rule dropLastActivationEligibleValidator(ListItem(V:Validator) Vs)
  => dropLastActivationEligibleValidatorAux(Vs, V, .List)
rule dropLastActivationEligibleValidatorAux(ListItem(V:Validator) Vs, MaxV, AccVs)
  => #if V.activation_eligibility_epoch >Int MaxV.activation_eligibility_epoch
     #then dropLastActivationEligibleValidatorAux(Vs,    V, ListItem(MaxV) AccVs)
     #else dropLastActivationEligibleValidatorAux(Vs, MaxV, ListItem(   V) AccVs)
     #fi
rule dropLastActivationEligibleValidatorAux(.List, _, Vs) => Vs
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
     (
       .Bag
     =>
       <block>
         <bSlot> Slot </bSlot> <bID> ID </bID>
         <parent> Parent </parent>
         <slashings> Slashings </slashings>
         <attestations> Attestations </attestations>
         <deposits> Deposits </deposits>
         <exits> VoluntaryExits </exits>
       </block>
     )
       ...
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

// slash_validator
syntax KItem ::= slashValidator(Validator)
rule <k> slashValidator(V) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <slashedBalance> S => S +Int V.effective_balance </slashedBalance> // TODO: store slashed balance for each epoch
       <validators> v(
         VM => VM [ V.id <- V withBool "slashed" = true
                              withInt  "withdrawable_epoch" = maxInt(V.withdrawable_epoch, epochOf(Slot) +Int EPOCHS_PER_SLASHINGS_VECTOR)
                              withInt  "balance" = maxInt(0, V.balance -Int (V.effective_balance /Int MIN_SLASHING_PENALTY_QUOTIENT)) ]v
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
rule <k> false ~> addAttestation(_) => bottom ... </k>

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
         VM => VM [ D.sender <- VM[D.sender]v withInt "balance" = VM[D.sender]v.balance +Int D.amount ]v // no change to effective_balance
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
         VIDs (.Set => SetItem(D.sender))
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
         VM => VM [ V.id <- V withInt "exit_epoch"         = ExitEpoch
                              withInt "withdrawable_epoch" = ExitEpoch +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY ]v
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

syntax Int ::= maxExitEpoch(Validators) [function, functional]
rule maxExitEpoch(v(VM, SetItem(VID) VIDs:Set)) => maxInt(VM[VID]v.exit_epoch, maxExitEpoch(v(VM, VIDs)))
rule maxExitEpoch(v(_, .Set)) => 0

syntax Int ::= countValidatorsToExit(Validators, Int) [function, functional]
rule countValidatorsToExit(v(VM, SetItem(VID) VIDs:Set), ExitEpoch)
  => #if VM[VID]v.exit_epoch ==Int ExitEpoch #then 1 #else 0 #fi +Int countValidatorsToExit(v(VM, VIDs), ExitEpoch)
rule countValidatorsToExit(v(_, .Set), _) => 0

syntax List ::= activeValidators(Validators, Int) [function, functional]
rule activeValidators(v(VM, SetItem(VID) VIDs:Set), Epoch)
  => #if isActiveValidator(VM[VID]v, Epoch)
     #then ListItem(VM[VID]v) activeValidators(v(VM, VIDs), Epoch)
     #else                    activeValidators(v(VM, VIDs), Epoch)
     #fi
rule activeValidators(v(_, .Set), _) => .List

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
