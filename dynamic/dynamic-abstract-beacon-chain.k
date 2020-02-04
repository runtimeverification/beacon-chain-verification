require "dynamic-abstract-beacon-chain-syntax.k"

module DYNAMIC-ABSTRACT-BEACON-CHAIN

imports DYNAMIC-ABSTRACT-BEACON-CHAIN-SYNTAX
imports INT
imports MAP
imports LIST

configuration <T>
  <k> init ~> $PGM:Cmds </k>
  <currentSlot> 0 </currentSlot>
  <states>
    // a state of slot N is the post-state of a (possibly empty) block at slot N
    <state multiplicity="*" type="Map">
      <slot> 0 </slot>
      <validators> .Map </validators> // ValidatorID -> ValidatorState
      <attested> .Map </attested> // Epoch -> Attestations
      <justified> .Map </justified> // Epoch -> Block option
      <finalized> .Map </finalized> // Epoch -> Block option
      // blockchain
      <blocks>
        <block multiplicity="*" type="Map">
          <bSlot> 0 </bSlot> <bID> 0 </bID> // unique block id (e.g., hash)
          <parent> (0,0) </parent> // parent block id
          <attestations> .Attestations </attestations>
        </block>
      </blocks>
      // derived info
      <lastBlock> (0,0) </lastBlock> // last block (slot, id)
      <lastJustified> (0,0) </lastJustified> // last justified (epoch, block id)
      <lastFinalized> (0,0) </lastFinalized> // last finalized (epoch, block id)
    </state>
  </states>
</T>

syntax KItem ::= "init"
rule <k> init => . ... </k>
     <currentSlot> 0 </currentSlot>
     <states> .Bag =>
       <state>
         <slot> 0 </slot>
         <validators>
           90000 |-> #Validator(90000,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH))
           90001 |-> #Validator(90001,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH))
           90002 |-> #Validator(90002,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH))
           90003 |-> #Validator(90003,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH))
           90004 |-> #Validator(90004,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH))
           90005 |-> #Validator(90005,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH))
           90006 |-> #Validator(90006,(1,1),(0,0),(FAR_FUTURE_EPOCH,FAR_FUTURE_EPOCH))
         </validators>
         <attested> 0 |-> .Attestations </attested>
         <justified> 0 |-> some 0 </justified>
         <finalized> 0 |-> some 0 </finalized>
         <blocks>
           <block>
             <bSlot> 0 </bSlot> <bID> 0 </bID>
             <parent> (-1,-1) </parent>
             <attestations> .Attestations </attestations>
           </block>
         </blocks>
         <lastBlock> (0,0) </lastBlock>
         <lastJustified> (0,0) </lastJustified>
         <lastFinalized> (0,0) </lastFinalized>
       </state>
     </states>

// state_transition
rule <k> stateTransition(NewBlock)
      => processSlots(NewBlock.slot)
      ~> processBlock(NewBlock) ... </k>
     <currentSlot> Slot </currentSlot>
     requires Slot <Int NewBlock.slot

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

rule <k> processSlot() => . ... </k>

rule <k> processBlock(#Block((Slot, ID), Parent, Attestations, Deposits, VoluntaryExits))
      => processAttestations(Attestations)
      ~> processDeposits(Deposits) 
      ~> processVoluntaryExits(VoluntaryExits) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <blocks>
       (
         .Bag
       =>
         <block>
           <bSlot> Slot </bSlot> <bID> ID </bID>
           <parent> Parent </parent>
           <attestations> Attestations </attestations>
         </block>
       )
         ...
       </blocks>
       <lastBlock> Parent => (Slot, ID) </lastBlock>
       ...
     </state>
     // TODO: check if the block proposer is valid (assigned, not slashed)

syntax KItem ::= processAttestations(Attestations)
rule <k> processAttestations(A Attestations => Attestations) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <attested>
         A.target_epoch |-> (As:Attestations => A As)
         ...
       </attested>
       ...
     </state>
     <state>
       <slot> firstSlotOf(A.target_epoch) </slot>
       <lastJustified> (JEpoch, JBlock) </lastJustified>
       ...
     </state>
     requires A.source_epoch ==Int JEpoch
      andBool A.source_block ==Int JBlock
      andBool A.slot +Int MIN_ATTESTATION_INCLUSION_DELAY <=Int Slot andBool Slot <=Int A.slot +Int MAX_ATTESTATION_INCLUSION_DELAY
      andBool epochOf(A.slot) ==Int A.target_epoch
      // TODO: check if A.attester is assigned to A.slot, and not slashed
rule processAttestations(.Attestations) => .

syntax KItem ::= processDeposits(Deposits)
rule <k> processDeposits(D Deposits => Deposits) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators>
         D.sender |-> (V:Validator => V with balance = V.balance +Int D.amount) // no change to effective_balance
         ...
       </validators>
       ...
     </state>
rule <k> processDeposits(D Deposits => Deposits) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators>
         Validators => Validators[
           D.sender <- #Validator(D.sender,
                                  (D.amount, minInt(D.amount, MAX_EFFECTIVE_BALANCE)), // effective_balance cap
                                  (FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH),
                                  (FAR_FUTURE_EPOCH, FAR_FUTURE_EPOCH))
         ]
       </validators>
       ...
     </state>
     requires notBool D.sender in keys(Validators)
rule processDeposits(.Deposits) => .

syntax KItem ::= processVoluntaryExits(VoluntaryExits)
rule <k> processVoluntaryExits(E Exits)
      => initiateValidatorExit(V)
      ~> processVoluntaryExits(  Exits) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> E.validator |-> V:Validator ... </validators>
       ...
     </state>
     requires isActiveValidator(V, epochOf(Slot))
      andBool V.exit_epoch ==Int FAR_FUTURE_EPOCH
      andBool epochOf(Slot) >=Int E.epoch
      andBool epochOf(Slot) >=Int V.activation_epoch +Int PERSISTENT_COMMITTEE_PERIOD
rule processVoluntaryExits(.VoluntaryExits) => .

syntax Bool ::= isActiveValidator(Validator, Int) [function]
rule isActiveValidator(V, Epoch)
  => V.activation_epoch <=Int Epoch andBool Epoch <Int V.exit_epoch

syntax KItem ::= initiateValidatorExit(Validator)
rule <k> initiateValidatorExit(V)
      => setExitEpoch(V, computeExitEpoch(values_list(Validators), epochOf(Slot))) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> Validators </validators>
       ...
     </state>
     requires V.exit_epoch =/=Int FAR_FUTURE_EPOCH

syntax KItem ::= setExitEpoch(Validator, Int)
rule <k> setExitEpoch(V, ExitEpoch) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators>
         V.id |-> (V => V with exit_epoch         = ExitEpoch
                          with withdrawable_epoch = ExitEpoch +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY)
         ...
       </validators>
       ...
     </state>

syntax Int ::= computeExitEpoch(List, Int) [function]
             | computeExitEpochAux(List, Int, Int) [function]
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

syntax Int ::= maxExitEpoch(List) [function]
rule maxExitEpoch(ListItem(V:Validator) Vs:List) => maxInt(V.exit_epoch, maxExitEpoch(Vs))
rule maxExitEpoch(.List) => 0

syntax Int ::= countValidatorsToExit(List, Int) [function]
rule countValidatorsToExit(ListItem(V:Validator) Vs:List, ExitEpoch)
  => #if V.exit_epoch ==Int ExitEpoch #then 1 #else 0 #fi +Int countValidatorsToExit(Vs, ExitEpoch)
rule countValidatorsToExit(.List, _) => 0

syntax Map ::= activeValidators(List, Int) [function]
rule activeValidators(ListItem(V:Validator) Vs:List, Epoch)
  => #if isActiveValidator(V, Epoch)
     #then V.id |-> V activeValidators(Vs, Epoch)
     #else            activeValidators(Vs, Epoch)
     #fi
rule activeValidators(.List, _) => .Map

syntax Int ::= delayedActivationExitEpoch(Int) [function]
rule delayedActivationExitEpoch(Epoch) => Epoch +Int 1 +Int ACTIVATION_EXIT_DELAY

syntax Int ::= churnLimit(Int) [function]
rule churnLimit(ActiveValidatorSize)
  => maxInt(MIN_PER_EPOCH_CHURN_LIMIT, ActiveValidatorSize /Int CHURN_LIMIT_QUOTIENT)

rule <k> processEpoch()
      => processJustification(epochOf(Slot) -Int 2)
      ~> processJustification(epochOf(Slot) -Int 1)
      ~> processFinalization(epochOf(Slot) -Int 2)
      ~> processFinalization(epochOf(Slot) -Int 1)
      ~> processValidatorUpdates() ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <attested> A => A[epochOf(Slot) <- .Attestations] </attested>
       <justified> J => J[epochOf(Slot) <- none] </justified>
       <finalized> F => F[epochOf(Slot) <- none] </finalized>
       ...
     </state>
     requires isFirstSlotOfEpoch(Slot)

rule <k> processEpoch() => . ... </k>
     <currentSlot> Slot </currentSlot>
     requires notBool isFirstSlotOfEpoch(Slot)

syntax KItem ::= processJustification(Int)
rule <k> processJustification(Epoch)
      => isJustifiable(EpochBoundaryBlock, Attestations, Validators)
      ~> justify(Epoch, EpochBoundaryBlock) ... </k>
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

syntax Bool ::= isJustifiable(Int, Attestations, Map) [function]
rule isJustifiable(EpochBoundaryBlock, Attestations, Validators)
  => isMajority(attestationsBalance(EpochBoundaryBlock, Attestations, Validators), totalBalance(values_list(Validators)))

syntax Bool ::= isMajority(Int, Int) [function]
rule isMajority(X, Total) => (X *Int 3) >=Int (Total *Int 2)  // (X / Total) >= 2/3

syntax Int ::= attestationsBalance(Int, Attestations, Map) [function]
rule attestationsBalance(Target, A Attestations, Validators)
  => #if A.target_block ==Int Target
     #then balanceOf(A, Validators)
     #else 0
     #fi +Int attestationsBalance(Target, Attestations, Validators)
rule attestationsBalance(_, .Attestations, _) => 0

/*
syntax Int ::= balanceOf(Attestation, Map) [function]
rule balanceOf(A, A.attester |-> V:Validator _:Map) => V.effective_balance
*/
// TODO: use the above simpler version
syntax Int ::= balanceOf(Attestation, Map) [function]
             | balanceOf(K) [function]
rule balanceOf(A:Attestation, M) => balanceOf(M[A.attester])
rule balanceOf(V:Validator) => V.effective_balance

syntax Int ::= totalBalance(List) [function]
rule totalBalance(ListItem(V:Validator) Vs:List) => V.effective_balance +Int totalBalance(Vs)
rule totalBalance(.List) => 0

syntax KItem ::= justify(Int, Int)
rule <k> true ~> justify(Epoch,BlockID) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <justified> Epoch |-> (none => some BlockID) ... </justified>
       <lastJustified> _ => (Epoch, BlockID) </lastJustified>
       ...
     </state>
// can be justified multiple times
rule <k> true ~> justify(Epoch,BlockID) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <justified> Epoch |-> some BlockID ... </justified>
       <lastJustified> (Epoch, BlockID) </lastJustified>
       ...
     </state>
rule <k> false ~> justify(_,_) => . ... </k>

syntax KItem ::= processFinalization(Int)
rule <k> processFinalization(TargetEpoch)
      => isFinalizable(SourceEpoch, TargetEpoch, Justified)
      ~> finalize(SourceEpoch, SourceBlock) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <justified> Justified </justified>
       ...
     </state>
     <state>
       <slot> firstSlotOf(TargetEpoch) </slot>
       <lastJustified> (SourceEpoch, SourceBlock) </lastJustified>
       ...
     </state>
     requires TargetEpoch >=Int 1
rule <k> processFinalization(TargetEpoch) => . ... </k>
     requires TargetEpoch <Int 1

// source : source+1 = target justified
// source : source+1 : source+2 = target justified
syntax Bool ::= isFinalizable(Int, Int, Map) [function]
rule isFinalizable(SourceEpoch, TargetEpoch, Justified)
  => isJustified(SourceEpoch, Justified) andBool isJustified(TargetEpoch, Justified)
     andBool (
                SourceEpoch +Int 1 ==Int TargetEpoch
       orBool ( SourceEpoch +Int 2 ==Int TargetEpoch andBool isJustified(SourceEpoch +Int 1, Justified) )
     )

syntax Bool ::= isJustified(Int, Map) [function]
rule isJustified(Epoch, Epoch |-> (some _) _:Map) => true
rule isJustified(Epoch, Epoch |-> none     _:Map) => false

syntax KItem ::= finalize(Int, Int)
rule <k> true ~> finalize(Epoch, BlockID) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <finalized> Epoch |-> (none => some BlockID) ... </finalized>
       <lastFinalized> _ => (Epoch, BlockID) </lastFinalized>
       ...
     </state>
// can be finalized multiple times
rule <k> true ~> finalize(Epoch, BlockID) => . ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <finalized> Epoch |-> some BlockID ... </finalized>
       <lastFinalized> (Epoch, BlockID) </lastFinalized>
       ...
     </state>
rule <k> false ~> finalize(_, _) => . ... </k>

// TODO: check if no mistake was made as this process is associated with the previous epoch
syntax KItem ::= processValidatorUpdates()
rule <k> processValidatorUpdates()
      => processValidatorEjection(keys_list(Validators))
      ~> updateActivationEligibility(keys_list(Validators))
      ~> processValidatorActivation() ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> Validators </validators>
       ...
     </state>

syntax KItem ::= processValidatorEjection(List)
rule <k> processValidatorEjection(ListItem(VID) VIDS:List)
      => #if isActiveValidator(V, epochOf(Slot) -Int 1) andBool V.effective_balance <=Int EJECTION_BALANCE
         #then initiateValidatorExit(V)
         #else .
         #fi
      ~> processValidatorEjection(VIDS) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> VID |-> V:Validator ... </validators>
       ...
     </state>
rule processValidatorEjection(.List) => .

syntax KItem ::= updateActivationEligibility(List)
rule <k> updateActivationEligibility(ListItem(VID) VIDS:List)
      => updateActivationEligibility(VIDS) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators>
         VID |-> (V:Validator => #if isActivationEligible(V)
                                 #then V with activation_eligibility_epoch = epochOf(Slot) -Int 1
                                 #else V
                                 #fi)
         ...
       </validators>
       ...
     </state>
rule updateActivationEligibility(.List) => .

syntax Bool ::= isActivationEligible(Validator) [function]
rule isActivationEligible(V)
  => V.activation_eligibility_epoch ==Int FAR_FUTURE_EPOCH andBool
     V.effective_balance >=Int MAX_EFFECTIVE_BALANCE

syntax Kitem ::= processValidatorActivation()
rule <k> processValidatorActivation()
      => activateValidators(activationQueueUptoChurnLimit(values_list(Validators), FinalizedEpoch, epochOf(Slot) -Int 1)) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators> Validators </validators>
       <lastFinalized> (FinalizedEpoch, _) </lastFinalized>
       ...
     </state>

syntax KItem ::= activateValidators(List)
rule <k> activateValidators(ListItem(V:Validator) Vs)
      => activateValidators(                      Vs) ... </k>
     <currentSlot> Slot </currentSlot>
     <state>
       <slot> Slot </slot>
       <validators>
         Validators
       =>
         Validators[
           V.id <- #if V.activation_epoch ==Int FAR_FUTURE_EPOCH
                   #then V with activation_epoch = delayedActivationExitEpoch(epochOf(Slot) -Int 1)
                   #else V
                   #fi
         ]
       </validators>
       ...
     </state>
rule activateValidators(.List) => .

syntax List ::= activationQueueUptoChurnLimit(List, Int, Int) [function]
rule activationQueueUptoChurnLimit(Validators, FinalizedEpoch, CurrentEpoch)
  => dropBeyondLimit(
       activationQueue(Validators, FinalizedEpoch),
       churnLimit(size(activeValidators(Validators, CurrentEpoch)))
     )

syntax List ::= activationQueue(List, Int) [function]
rule activationQueue(ListItem(V:Validator) Vs:List, FinalizedEpoch)
  => #if V.activation_eligibility_epoch =/=Int FAR_FUTURE_EPOCH andBool
         V.activation_epoch >=Int delayedActivationExitEpoch(FinalizedEpoch) // TODO: why is this needed?
     #then ListItem(V) activationQueue(Vs, FinalizedEpoch)
     #else             activationQueue(Vs, FinalizedEpoch)
     #fi
rule activationQueue(.List, _) => .List

syntax List ::= dropBeyondLimit(List, Int) [function]
rule dropBeyondLimit(Vs, Limit) => Vs requires size(Vs) <=Int Limit
rule dropBeyondLimit(Vs, Limit)
  => dropBeyondLimit(dropLastActivationEligibleValidator(Vs), Limit)
     requires size(Vs) >Int Limit

syntax List ::= dropLastActivationEligibleValidator(List)                     [function]
              | dropLastActivationEligibleValidatorAux(List, Validator, List) [function]
rule dropLastActivationEligibleValidator(ListItem(V:Validator) Vs)
  => dropLastActivationEligibleValidatorAux(Vs, V, .List)
rule dropLastActivationEligibleValidatorAux(ListItem(V:Validator) Vs, MaxV, AccVs)
  => #if V.activation_eligibility_epoch >Int MaxV.activation_eligibility_epoch
     #then dropLastActivationEligibleValidatorAux(Vs,    V, ListItem(MaxV) AccVs)
     #else dropLastActivationEligibleValidatorAux(Vs, MaxV, ListItem(   V) AccVs)
     #fi
rule dropLastActivationEligibleValidatorAux(.List, _, Vs) => Vs

syntax List ::= "values_list" "(" Map ")" [function]
              | "values_list" "(" Map "," List "," List ")" [function]
rule values_list(M:Map) => values_list(M, keys_list(M), .List)
rule values_list(M, ListItem(K) Ks:List, Vs) => values_list(M, Ks, ListItem(M[K]) Vs)
rule values_list(_, .List, Vs) => Vs

endmodule
