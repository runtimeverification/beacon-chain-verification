# Data Types of Dynamic Abstract Model

```k
module DYNAMIC-ABSTRACT-BEACON-CHAIN-SYNTAX
imports INT

// libraries
syntax Int ::= hash(Int) [function, functional, smtlib(hash)]

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

syntax KItem ::= "bottom"
```

## Abstract Blocks

An abstract block consists of:
- `slot`: the slot number of the block
- `id`: an abstract unique ID
- `parent`: the link to the parent block, corresponding to `parent_root` of the concrete model
- `slashings`: the list of slashing evidences, capturing both `proposer_slashings` and `attester_slashings` of the concrete model
- `attestations`: the list of attestations
- `deposits`: the list of deposits
- `voluntary_exits`: the list of voluntary exits

The RANDAO reveal (`randao_reveal`) and Eth1 data vote (`eth1_data`) are omitted in the abstract model.

```k
syntax Block ::= #Block(Pair,Pair,Slashings,Attestations,Deposits,VoluntaryExits) // (slot,id), parent, slashings, attestations, deposits, voluntary exits
syntax Int            ::= Block ".slot"            [function, functional]
syntax Int            ::= Block ".id"              [function, functional]
syntax Pair           ::= Block ".parent"          [function, functional]
syntax Slashings      ::= Block ".slashings"       [function, functional]
syntax Attestations   ::= Block ".attestations"    [function, functional]
syntax Deposits       ::= Block ".deposits"        [function, functional]
syntax VoluntaryExits ::= Block ".voluntary_exits" [function, functional]
rule #Block((X,_),_,_,_,_,_).slot            => X
rule #Block((_,X),_,_,_,_,_).id              => X
rule #Block((_,_),X,_,_,_,_).parent          => X
rule #Block((_,_),_,X,_,_,_).slashings       => X
rule #Block((_,_),_,_,X,_,_).attestations    => X
rule #Block((_,_),_,_,_,X,_).deposits        => X
rule #Block((_,_),_,_,_,_,X).voluntary_exits => X
```

## Abstract Slashings

An abstract slashing evidence is a pair of two conflict attestations.

This captures both proposer and attester slashings of the concrete model.
- The proposer slashing can be abstracted as a pair of two attestations where their attester is the proposer, and their target block is the proposed block.
- The attester slashing that represents two *set* of attestations, can be abstracted as a set of pairs of two conflict attestations, i.e., a set of abstract slashings.

```k
// abstract represention of both proposer slashings and attester slahsings
syntax Slashings ::= List{Slashing,""}
syntax Slashing  ::= #Slashing(Attestation,Attestation) // two conflict attestations
syntax Attestation ::= Slashing ".attestation_1" [function, functional]
syntax Attestation ::= Slashing ".attestation_2" [function, functional]
rule #Slashing(X,_).attestation_1 => X
rule #Slashing(_,X).attestation_2 => X
```

## Abstract Attestations

An abstract attestation denotes a single attestation, consisting of an attester, an assigned slot, a source, and a target.

The `Attestation` of the concrete model can be represented as a set of abstract attestations whose slot, source, and target are the same.

```k
// beacon_block_root (LMD GHOST vote) is omitted
syntax Attestations ::= List{Attestation,""}
syntax Attestation  ::= #Attestation(Int,Int,Pair,Pair) // attester, assigned slot, source epoch/block, target epoch/block
syntax Int ::= Attestation ".attester"     [function, functional]
syntax Int ::= Attestation ".slot"         [function, functional]
syntax Int ::= Attestation ".source_epoch" [function, functional]
syntax Int ::= Attestation ".source_block" [function, functional]
syntax Int ::= Attestation ".target_epoch" [function, functional]
syntax Int ::= Attestation ".target_block" [function, functional]
rule #Attestation(X,_,(_,_),(_,_)).attester     => X
rule #Attestation(_,X,(_,_),(_,_)).slot         => X
rule #Attestation(_,_,(X,_),(_,_)).source_epoch => X
rule #Attestation(_,_,(_,X),(_,_)).source_block => X
rule #Attestation(_,_,(_,_),(X,_)).target_epoch => X
rule #Attestation(_,_,(_,_),(_,X)).target_block => X
```

## Abstract Deposits

An abstract deposit is simply a pair of the deposit owner and the deposit amount.

The extra data (e.g., signatures and Merkle proofs) for validating the deposit information is omitted in the abstract model.

```k
syntax Deposits ::= List{Deposit,""}
syntax Deposit  ::= #Deposit(Int,Int) // sender, amount
syntax Int ::= Deposit ".sender" [function, functional]
syntax Int ::= Deposit ".amount" [function, functional]
rule #Deposit(X,_).sender => X
rule #Deposit(_,X).amount => X
```

## Voluntary Exits

This is a pair of a validator ID and an epoch to exit requested.

This is the same with the concrete model.

```k
syntax VoluntaryExits ::= List{VoluntaryExit,""}
syntax VoluntaryExit  ::= #VoluntaryExit(Int,Int) // validator id, epoch to exit
syntax Int ::= VoluntaryExit ".validator" [function, functional]
syntax Int ::= VoluntaryExit ".epoch"     [function, functional]
rule #VoluntaryExit(X,_).validator => X
rule #VoluntaryExit(_,X).epoch     => X
```

## Abstract Validators

An abstract validator consists of:
- `id`: a unique ID, corresponding to `pubkey` of the concrete model
- `slashed`: whether the validator has been slashed or not
- `balance`: actual balance that the validator holds, corresponding to the entry of the `balances` map of `BeaconState` of the concrete model
- `effective_balance`: effective balance at stake
- join status epochs:
  - `activation_eligibility_epoch`: when the validator becomes eligible to join
  - `activation_epoch`: when the validator actually joins
- exit status epochs:
  - `exit_epoch`: when the validator actually exists
  - `withdrawable_epoch`: when the validator can withdraw funds

The cryptographic data (`pubkey` and `withdrawal_credentials`) is omitted in the abstract model.

```k
syntax Validator ::= #Validator(Int,Bool,Pair,Pair,Pair) // id, slashed, (balance, effective_balance), join epoch (eligible, actual), (exit epoch, withdrawable epoch)
syntax Int  ::= Validator ".id"                           [function, functional, klabel(v_id)                          , smtlib(v_id)                          ]
syntax Bool ::= Validator ".slashed"                      [function, functional, klabel(v_slashed)                     , smtlib(v_slashed)                     ]
syntax Int  ::= Validator ".balance"                      [function, functional, klabel(v_balance)                     , smtlib(v_balance)                     ]
syntax Int  ::= Validator ".effective_balance"            [function, functional, klabel(v_effective_balance)           , smtlib(v_effective_balance)           ]
syntax Int  ::= Validator ".activation_eligibility_epoch" [function, functional, klabel(v_activation_eligibility_epoch), smtlib(v_activation_eligibility_epoch)]
syntax Int  ::= Validator ".activation_epoch"             [function, functional, klabel(v_activation_epoc)             , smtlib(v_activation_epoc)             ]
syntax Int  ::= Validator ".exit_epoch"                   [function, functional, klabel(v_exit_epoch)                  , smtlib(v_exit_epoch)                  ]
syntax Int  ::= Validator ".withdrawable_epoch"           [function, functional, klabel(v_withdrawable_epoch)          , smtlib(v_withdrawable_epoch)          ]
rule #Validator(X,_,(_,_),(_,_),(_,_)).id                           => X
rule #Validator(_,X,(_,_),(_,_),(_,_)).slashed                      => X
rule #Validator(_,_,(X,_),(_,_),(_,_)).balance                      => X
rule #Validator(_,_,(_,X),(_,_),(_,_)).effective_balance            => X
rule #Validator(_,_,(_,_),(X,_),(_,_)).activation_eligibility_epoch => X
rule #Validator(_,_,(_,_),(_,X),(_,_)).activation_epoch             => X
rule #Validator(_,_,(_,_),(_,_),(X,_)).exit_epoch                   => X
rule #Validator(_,_,(_,_),(_,_),(_,X)).withdrawable_epoch           => X
syntax Validator ::= Validator "with" "slashed"                      "=" Bool [function, functional, klabel(v_with_slashed)                     , smtlib(v_with_slashed)                     ]
syntax Validator ::= Validator "with" "balance"                      "=" Int  [function, functional, klabel(v_with_balance)                     , smtlib(v_with_balance)                     ]
syntax Validator ::= Validator "with" "effective_balance"            "=" Int  [function, functional, klabel(v_with_effective_balance)           , smtlib(v_with_effective_balance)           ]
syntax Validator ::= Validator "with" "activation_eligibility_epoch" "=" Int  [function, functional, klabel(v_with_activation_eligibility_epoch), smtlib(v_with_activation_eligibility_epoch)]
syntax Validator ::= Validator "with" "activation_epoch"             "=" Int  [function, functional, klabel(v_with_activation_epoc)             , smtlib(v_with_activation_epoc)             ]
syntax Validator ::= Validator "with" "exit_epoch"                   "=" Int  [function, functional, klabel(v_with_exit_epoch)                  , smtlib(v_with_exit_epoch)                  ]
syntax Validator ::= Validator "with" "withdrawable_epoch"           "=" Int  [function, functional, klabel(v_with_withdrawable_epoch)          , smtlib(v_with_withdrawable_epoch)          ]
rule #Validator(A,S,(B,C),(D,E),(F,G)) with slashed                      = V => #Validator(A,V,(B,C),(D,E),(F,G))
rule #Validator(A,S,(B,C),(D,E),(F,G)) with balance                      = V => #Validator(A,S,(V,C),(D,E),(F,G))
rule #Validator(A,S,(B,C),(D,E),(F,G)) with effective_balance            = V => #Validator(A,S,(B,V),(D,E),(F,G))
rule #Validator(A,S,(B,C),(D,E),(F,G)) with activation_eligibility_epoch = V => #Validator(A,S,(B,C),(V,E),(F,G))
rule #Validator(A,S,(B,C),(D,E),(F,G)) with activation_epoch             = V => #Validator(A,S,(B,C),(D,V),(F,G))
rule #Validator(A,S,(B,C),(D,E),(F,G)) with exit_epoch                   = V => #Validator(A,S,(B,C),(D,E),(V,G))
rule #Validator(A,S,(B,C),(D,E),(F,G)) with withdrawable_epoch           = V => #Validator(A,S,(B,C),(D,E),(F,V))
```

```k
syntax Validators ::= v(ValidatorMap, IntList) [smtlib(v)]
syntax ValidatorMap ::= Validators ".vmap" [function]
syntax IntList      ::= Validators ".vset" [function]
rule v(M,S).vmap => M
rule v(M,S).vset => S
```

```k
syntax ValidatorList ::= ".ValidatorList"        [klabel(nilV),  smtlib(nilV)]
syntax ValidatorList ::= Validator ValidatorList [klabel(consV), smtlib(consV)]
syntax Int ::= size(ValidatorList) [function, klabel(sizeV), smtlib(sizeV)]
rule size(V Vs) => 1 +Int size(Vs)
rule size(.ValidatorList) => 0

// take the first N elements at most
syntax ValidatorList ::= take(Int, ValidatorList) [function, klabel(takeV), smtlib(takeV)]
rule take(N, V Vs) => V take(N -Int 1, Vs) requires N >Int 0
rule take(0, _) => .ValidatorList
rule take(_, .ValidatorList) => .ValidatorList

// sort in the order of activation_eligibility_epoch
syntax ValidatorList ::= sort(ValidatorList) [function, klabel(sortV), smtlib(sortV)]
// TODO: implement

// subset in set-like view
syntax Bool ::= subset(ValidatorList, ValidatorList) [function, klabel(subsetV), smtlib(subsetV)]
// TODO: implement
```

```k
syntax IntList ::= ".IntList"   [klabel(nilI),  smtlib(nilI)]
syntax IntList ::= Int IntList  [klabel(consI), smtlib(consI)]
syntax Bool ::= Int "in" IntList [function, klabel(inI), smtlib(inI)]
rule J in (I Is) => true    requires J  ==Int I
rule J in (I Is) => J in Is requires J =/=Int I
rule _ in .IntList => false
```

```k
syntax ValidatorMap ::= ".ValidatorMap"                          [          klabel(emptyV),  smtlib(emptyV)]
syntax ValidatorMap ::= ValidatorMap "[" Int "<-" Validator "]v" [function, klabel(storeV),  smtlib(storeV)]
syntax Validator    ::= ValidatorMap "[" Int "]v"                [function, klabel(selectV), smtlib(selectV)]

rule ( M [ K1 <- V ]v ) [ K2 ]v => V         requires K1  ==Int K2
rule ( M [ K1 <- V ]v ) [ K2 ]v => M [ K2 ]v requires K1 =/=Int K2
```

```k
/*
// in-place update

rule ( M [ K0 <- V0 ]v ) [ K1 <- V1 ]v => M [ K0 <- V1 ]v
  requires K0 ==Int K1

rule ( M [ K0 <- V0 ]v ) [ K1 <- V1 ]v => ( M [ K1 <- V1 ]v ) [ K0 <- V0 ]v
  requires K0 =/=Int K1 andBool K1 in keys(M)

syntax Set ::= keys(ValidatorMap) [function]

rule K1 in keys(M [ K2 <- _ ]v) => true          requires K1  ==Int K2
rule K1 in keys(M [ K2 <- _ ]v) => K1 in keys(M) requires K1 =/=Int K2
*/
```

## Constants

```k
// macros
syntax Int ::= "SLOTS_PER_EPOCH"
syntax Int ::= "MIN_ATTESTATION_INCLUSION_DELAY"
syntax Int ::= "MAX_ATTESTATION_INCLUSION_DELAY"
syntax Int ::= "FAR_FUTURE_EPOCH"
syntax Int ::= "MIN_DEPOSIT_AMOUNT"
syntax Int ::= "MAX_EFFECTIVE_BALANCE"
syntax Int ::= "EJECTION_BALANCE"
syntax Int ::= "EFFECTIVE_BALANCE_INCREMENT"
syntax Int ::= "PERSISTENT_COMMITTEE_PERIOD"
syntax Int ::= "ACTIVATION_EXIT_DELAY"
syntax Int ::= "MIN_VALIDATOR_WITHDRAWABILITY_DELAY"
syntax Int ::= "MIN_PER_EPOCH_CHURN_LIMIT"
syntax Int ::= "CHURN_LIMIT_QUOTIENT"
syntax Int ::= "EPOCHS_PER_SLASHINGS_VECTOR"
syntax Int ::= "MIN_SLASHING_PENALTY_QUOTIENT"
```

```{.k .concrete}
rule SLOTS_PER_EPOCH                     =>      4          [macro]
rule MIN_ATTESTATION_INCLUSION_DELAY     =>      1          [macro]
rule MAX_ATTESTATION_INCLUSION_DELAY     => SLOTS_PER_EPOCH [macro]
rule FAR_FUTURE_EPOCH                    => 999999          [macro]
rule MIN_DEPOSIT_AMOUNT                  =>      1          [macro]
rule MAX_EFFECTIVE_BALANCE               =>      2          [macro]
rule EJECTION_BALANCE                    =>      0          [macro]
rule EFFECTIVE_BALANCE_INCREMENT         =>      1          [macro]
rule PERSISTENT_COMMITTEE_PERIOD         =>      1          [macro]
rule ACTIVATION_EXIT_DELAY               =>      1          [macro]
rule MIN_VALIDATOR_WITHDRAWABILITY_DELAY =>      1          [macro]
rule MIN_PER_EPOCH_CHURN_LIMIT           =>      1          [macro]
rule CHURN_LIMIT_QUOTIENT                =>      1          [macro]
rule EPOCHS_PER_SLASHINGS_VECTOR         =>      1          [macro]
rule MIN_SLASHING_PENALTY_QUOTIENT       =>      1          [macro]
```

```{.k .symbolic}
rule SLOTS_PER_EPOCH                     =>    32            [macro]
rule MIN_ATTESTATION_INCLUSION_DELAY     =>     1            [macro]
rule MAX_ATTESTATION_INCLUSION_DELAY     => SLOTS_PER_EPOCH  [macro]
rule FAR_FUTURE_EPOCH                    => 2 ^Int 64 -Int 1 [macro]
rule MIN_DEPOSIT_AMOUNT                  =>     1            [macro] // TODO: Gwei
rule MAX_EFFECTIVE_BALANCE               =>    32            [macro] // TODO: Gwei
rule EJECTION_BALANCE                    =>    16            [macro] // TODO: Gwei
rule EFFECTIVE_BALANCE_INCREMENT         =>     1            [macro] // TODO: Gwei
rule PERSISTENT_COMMITTEE_PERIOD         =>  2048            [macro]
rule ACTIVATION_EXIT_DELAY               =>     4            [macro] // MAX_SEED_LOOKAHEAD
rule MIN_VALIDATOR_WITHDRAWABILITY_DELAY =>   256            [macro]
rule MIN_PER_EPOCH_CHURN_LIMIT           =>     4            [macro]
rule CHURN_LIMIT_QUOTIENT                => 65536            [macro]
rule EPOCHS_PER_SLASHINGS_VECTOR         =>  8192            [macro]
rule MIN_SLASHING_PENALTY_QUOTIENT       =>    32            [macro]
```

## Macros

```k
syntax Int  ::= epochOf(Int)
              | firstSlotOf(Int)
              | lastSlotOf(Int)
syntax Bool ::= isFirstSlotOfEpoch(Int) // Slot is the first slot of an epoch?
rule epochOf(Slot)            => Slot /Int SLOTS_PER_EPOCH                        [macro]
rule firstSlotOf(Epoch)       => Epoch *Int SLOTS_PER_EPOCH                       [macro]
rule lastSlotOf(Epoch)        => firstSlotOf(Epoch) +Int (SLOTS_PER_EPOCH -Int 1) [macro]
rule isFirstSlotOfEpoch(Slot) => Slot %Int SLOTS_PER_EPOCH ==Int 0                [macro]

endmodule
```
