# Data Types and Constants of Dynamic Abstract Model of Beacon Chain State Transition

```k
module DYNAMIC-ABSTRACT-BEACON-CHAIN-SYNTAX
imports INT

// libraries
syntax Int ::= hash(Int) [function, smtlib(hash)]

// functions
syntax Cmd ::= stateTransition(Block)
             | processSlots(Int)
             | processSlot()
             | processBlock(Block)
             | processEpoch()

// program
syntax Cmds ::= Cmd Cmds | Cmd
rule C:Cmd Cs:Cmds => C ~> Cs

// data structures
syntax Pair ::= "(" Int "," Int ")"
syntax Option ::= "none" | "some" Int
```

## Abstract Block

An abstract block consists of an assigned slot number, an abstract unique ID, its parent block's ID, the list of slashing evidences, the list of 

```k
// randao_reveal and eth1_data are omitted
syntax Block ::= #Block(Pair,Pair,Slashings,Attestations,Deposits,VoluntaryExits) // (slot,id), parent, slashings, attestations, deposits, voluntary exits
syntax Int            ::= Block ".slot"            [function]
syntax Int            ::= Block ".id"              [function]
syntax Pair           ::= Block ".parent"          [function]
syntax Slashings      ::= Block ".slashings"       [function]
syntax Attestations   ::= Block ".attestations"    [function]
syntax Deposits       ::= Block ".deposits"        [function]
syntax VoluntaryExits ::= Block ".voluntary_exits" [function]
rule #Block((X,_),_,_,_,_,_).slot            => X
rule #Block((_,X),_,_,_,_,_).id              => X
rule #Block((_,_),X,_,_,_,_).parent          => X
rule #Block((_,_),_,X,_,_,_).slashings       => X
rule #Block((_,_),_,_,X,_,_).attestations    => X
rule #Block((_,_),_,_,_,X,_).deposits        => X
rule #Block((_,_),_,_,_,_,X).voluntary_exits => X
```

## Slashings

```k
// abstract represention of both proposer slashings and attester slahsings
syntax Slashings ::= List{Slashing,""}
syntax Slashing  ::= #Slashing(Attestation,Attestation) // two conflict attestations
syntax Attestation ::= Slashing ".attestation_1" [function]
syntax Attestation ::= Slashing ".attestation_2" [function]
rule #Slashing(X,_).attestation_1 => X
rule #Slashing(_,X).attestation_2 => X
```

## Attestations

```k
// beacon_block_root (LMD GHOST vote) is omitted
syntax Attestations ::= List{Attestation,""}
syntax Attestation  ::= #Attestation(Int,Int,Pair,Pair) // attester, assigned slot, source epoch/block, target epoch/block
syntax Int ::= Attestation ".attester"     [function]
syntax Int ::= Attestation ".slot"         [function]
syntax Int ::= Attestation ".source_epoch" [function]
syntax Int ::= Attestation ".source_block" [function]
syntax Int ::= Attestation ".target_epoch" [function]
syntax Int ::= Attestation ".target_block" [function]
rule #Attestation(X,_,(_,_),(_,_)).attester     => X
rule #Attestation(_,X,(_,_),(_,_)).slot         => X
rule #Attestation(_,_,(X,_),(_,_)).source_epoch => X
rule #Attestation(_,_,(_,X),(_,_)).source_block => X
rule #Attestation(_,_,(_,_),(X,_)).target_epoch => X
rule #Attestation(_,_,(_,_),(_,X)).target_block => X
```

## Deposits

```k
syntax Deposits ::= List{Deposit,""}
syntax Deposit  ::= #Deposit(Int,Int) // sender, amount
syntax Int ::= Deposit ".sender" [function]
syntax Int ::= Deposit ".amount" [function]
rule #Deposit(X,_).sender => X
rule #Deposit(_,X).amount => X
```

## VoluntaryExits

```k
syntax VoluntaryExits ::= List{VoluntaryExit,""}
syntax VoluntaryExit  ::= #VoluntaryExit(Int,Int) // validator id, epoch to exit
syntax Int ::= VoluntaryExit ".validator" [function]
syntax Int ::= VoluntaryExit ".epoch"     [function]
rule #VoluntaryExit(X,_).validator => X
rule #VoluntaryExit(_,X).epoch     => X
```

## Validator

```k
syntax Validator ::= #Validator(Int,Bool,Pair,Pair,Pair) // id, slashed, (balance, effective_balance), join epoch (eligible, actual), (exit epoch, withdrawable epoch)
syntax Int  ::= Validator ".id"                           [function]
syntax Bool ::= Validator ".slashed"                      [function]
syntax Int  ::= Validator ".balance"                      [function]
syntax Int  ::= Validator ".effective_balance"            [function]
syntax Int  ::= Validator ".activation_eligibility_epoch" [function]
syntax Int  ::= Validator ".activation_epoch"             [function]
syntax Int  ::= Validator ".exit_epoch"                   [function]
syntax Int  ::= Validator ".withdrawable_epoch"           [function]
rule #Validator(X,_,(_,_),(_,_),(_,_)).id                           => X
rule #Validator(_,X,(_,_),(_,_),(_,_)).slashed                      => X
rule #Validator(_,_,(X,_),(_,_),(_,_)).balance                      => X
rule #Validator(_,_,(_,X),(_,_),(_,_)).effective_balance            => X
rule #Validator(_,_,(_,_),(X,_),(_,_)).activation_eligibility_epoch => X
rule #Validator(_,_,(_,_),(_,X),(_,_)).activation_epoch             => X
rule #Validator(_,_,(_,_),(_,_),(X,_)).exit_epoch                   => X
rule #Validator(_,_,(_,_),(_,_),(_,X)).withdrawable_epoch           => X
syntax Validator ::= Validator "with" "slashed"                      "=" Bool [function]
syntax Validator ::= Validator "with" "balance"                      "=" Int  [function]
syntax Validator ::= Validator "with" "effective_balance"            "=" Int  [function]
syntax Validator ::= Validator "with" "activation_eligibility_epoch" "=" Int  [function]
syntax Validator ::= Validator "with" "activation_epoch"             "=" Int  [function]
syntax Validator ::= Validator "with" "exit_epoch"                   "=" Int  [function]
syntax Validator ::= Validator "with" "withdrawable_epoch"           "=" Int  [function]
rule #Validator(A,S,(B,C),(D,E),(F,G)) with slashed                      = V => #Validator(A,V,(B,C),(D,E),(F,G))
rule #Validator(A,S,(B,C),(D,E),(F,G)) with balance                      = V => #Validator(A,S,(V,C),(D,E),(F,G))
rule #Validator(A,S,(B,C),(D,E),(F,G)) with effective_balance            = V => #Validator(A,S,(B,V),(D,E),(F,G))
rule #Validator(A,S,(B,C),(D,E),(F,G)) with activation_eligibility_epoch = V => #Validator(A,S,(B,C),(V,E),(F,G))
rule #Validator(A,S,(B,C),(D,E),(F,G)) with activation_epoch             = V => #Validator(A,S,(B,C),(D,V),(F,G))
rule #Validator(A,S,(B,C),(D,E),(F,G)) with exit_epoch                   = V => #Validator(A,S,(B,C),(D,E),(V,G))
rule #Validator(A,S,(B,C),(D,E),(F,G)) with withdrawable_epoch           = V => #Validator(A,S,(B,C),(D,E),(F,V))
```

## Constants

```k
// macros
syntax Int ::= "SLOTS_PER_EPOCH"                        rule SLOTS_PER_EPOCH                     =>      4 /*    32 */    [macro]
syntax Int ::= "MIN_ATTESTATION_INCLUSION_DELAY"        rule MIN_ATTESTATION_INCLUSION_DELAY     =>      1 /*     1 */    [macro]
syntax Int ::= "MAX_ATTESTATION_INCLUSION_DELAY"        rule MAX_ATTESTATION_INCLUSION_DELAY     => SLOTS_PER_EPOCH       [macro]
syntax Int ::= "FAR_FUTURE_EPOCH"                       rule FAR_FUTURE_EPOCH                    => 999999 /* 2^64 - 1 */ [macro]
syntax Int ::= "MIN_DEPOSIT_AMOUNT"                     rule MIN_DEPOSIT_AMOUNT                  =>      1 /*     1 */    [macro]
syntax Int ::= "MAX_EFFECTIVE_BALANCE"                  rule MAX_EFFECTIVE_BALANCE               =>      2 /*    32 */    [macro]
syntax Int ::= "EJECTION_BALANCE"                       rule EJECTION_BALANCE                    =>      0 /*    16 */    [macro]
syntax Int ::= "EFFECTIVE_BALANCE_INCREMENT"            rule EFFECTIVE_BALANCE_INCREMENT         =>      1 /*     1 */    [macro]
syntax Int ::= "PERSISTENT_COMMITTEE_PERIOD"            rule PERSISTENT_COMMITTEE_PERIOD         =>      1 /*  2048 */    [macro]
syntax Int ::= "ACTIVATION_EXIT_DELAY"                  rule ACTIVATION_EXIT_DELAY               =>      1 /*     4 */    [macro]
syntax Int ::= "MIN_VALIDATOR_WITHDRAWABILITY_DELAY"    rule MIN_VALIDATOR_WITHDRAWABILITY_DELAY =>      1 /*   256 */    [macro]
syntax Int ::= "MIN_PER_EPOCH_CHURN_LIMIT"              rule MIN_PER_EPOCH_CHURN_LIMIT           =>      1 /*     4 */    [macro]
syntax Int ::= "CHURN_LIMIT_QUOTIENT"                   rule CHURN_LIMIT_QUOTIENT                =>      1 /* 65536 */    [macro]
syntax Int ::= "EPOCHS_PER_SLASHINGS_VECTOR"            rule EPOCHS_PER_SLASHINGS_VECTOR         =>      1 /*  8192 */    [macro]
syntax Int ::= "MIN_SLASHING_PENALTY_QUOTIENT"          rule MIN_SLASHING_PENALTY_QUOTIENT       =>      1 /*    32 */    [macro]
```

## Macros

```k
syntax Int  ::= epochOf(Int)            [function]
              | firstSlotOf(Int)        [function]
              | lastSlotOf(Int)         [function]
syntax Bool ::= isFirstSlotOfEpoch(Int) [function]
rule epochOf(Slot)            => Slot /Int SLOTS_PER_EPOCH
rule firstSlotOf(Epoch)       => Epoch *Int SLOTS_PER_EPOCH
rule lastSlotOf(Epoch)        => firstSlotOf(Epoch) +Int SLOTS_PER_EPOCH -Int 1
rule isFirstSlotOfEpoch(Slot) => Slot %Int SLOTS_PER_EPOCH ==Int 0 // Slot is the first slot of an epoch?

endmodule
```
