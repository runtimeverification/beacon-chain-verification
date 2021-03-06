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

syntax KItem ::= "#bottom"

syntax KItem ::= #ite(Bool, K, K)
rule #ite(true,  K, _) => K
rule #ite(false, _, K) => K

syntax KItem ::= #it(Bool, K)
rule #it(true,  K) => K
rule #it(false, _) => .

syntax KItem ::= #assert(Bool)
rule #assert(true) => .
rule #assert(false) => #bottom
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

```k
syntax BlockMap ::= ".BlockMap"                          [          klabel(emptyK),  smtlib(emptyK)]
syntax BlockMap ::= BlockMap "[" Int "<-" Block "]k"     [function, klabel(storeK),  smtlib(storeK)]
syntax Block    ::= BlockMap "[" Int "]k"                [function, klabel(selectK), smtlib(selectK)]

rule ( M [ K1 <- V ]k ) [ K2 ]k => V         requires K1  ==Int K2
rule ( M [ K1 <- V ]k ) [ K2 ]k => M [ K2 ]k requires K1 =/=Int K2
```

## Abstract Slashings

An abstract slashing evidence is a pair of two conflict attestations.

This captures both proposer and attester slashings of the concrete model.
- The proposer slashing can be abstracted as a pair of two attestations where their attester is the proposer, and their target block is the proposed block.
- The attester slashing that represents two *set* of attestations, can be abstracted as a set of pairs of two conflict attestations, i.e., a set of abstract slashings.

```k
// abstract represention of both proposer slashings and attester slahsings
syntax Slashing  ::= #Slashing(Attestation,Attestation) // two conflict attestations
syntax Attestation ::= Slashing ".attestation_1" [function, functional, klabel(s_attestation_1), smtlib(s_attestation_1)]
syntax Attestation ::= Slashing ".attestation_2" [function, functional, klabel(s_attestation_2), smtlib(s_attestation_2)]
rule #Slashing(X,_).attestation_1 => X
rule #Slashing(_,X).attestation_2 => X

syntax Slashings ::= ".Slashings"       [klabel(nilS),  smtlib(nilS)]
syntax Slashings ::= Slashing Slashings [klabel(consS), smtlib(consS)]

syntax Bool ::= Slashing "inS" Slashings [function, klabel(inS), smtlib(inS)]
rule J inS (I Is) => true     requires J  ==K I [smt-lemma]
rule J inS (I Is) => J inS Is requires J =/=K I [smt-lemma]
rule _ inS .Slashings => false [smt-lemma]

syntax Int ::= sizeS(Slashings) [function, smtlib(sizeS)]
rule sizeS(_ Es) => 1 +Int sizeS(Es)
rule sizeS(.Slashings) => 0

rule sizeS(_) >=Int 0 => true [smt-lemma]
```

## Abstract Attestations

An abstract attestation denotes a single attestation, consisting of an attester, an assigned slot, a source, and a target.

The `Attestation` of the concrete model can be represented as a set of abstract attestations whose slot, source, and target are the same.

```k
syntax Attestation ::= #Attestation(Int,Int,Pair,Pair,Int,Int,Int) // attester, assigned slot, source epoch/block, target epoch/block, head block (LMD GHOST vote), proposer, inclusion delay
syntax Int ::= Attestation ".attester"        [function, functional, klabel(a_attester)       , smtlib(a_attester)       ]
syntax Int ::= Attestation ".slot"            [function, functional, klabel(a_slot)           , smtlib(a_slot)           ]
syntax Int ::= Attestation ".source_epoch"    [function, functional, klabel(a_source_epoch)   , smtlib(a_source_epoch)   ]
syntax Int ::= Attestation ".source_block"    [function, functional, klabel(a_source_block)   , smtlib(a_source_block)   ]
syntax Int ::= Attestation ".target_epoch"    [function, functional, klabel(a_target_epoch)   , smtlib(a_target_epoch)   ]
syntax Int ::= Attestation ".target_block"    [function, functional, klabel(a_target_block)   , smtlib(a_target_block)   ]
syntax Int ::= Attestation ".head_block"      [function, functional, klabel(a_head_block)     , smtlib(a_head_block)     ]
syntax Int ::= Attestation ".proposer"        [function, functional, klabel(a_proposer)       , smtlib(a_proposer)       ]
syntax Int ::= Attestation ".inclusion_delay" [function, functional, klabel(a_inclusion_delay), smtlib(a_inclusion_delay)]
rule #Attestation(X,_,(_,_),(_,_),_,_,_).attester        => X
rule #Attestation(_,X,(_,_),(_,_),_,_,_).slot            => X
rule #Attestation(_,_,(X,_),(_,_),_,_,_).source_epoch    => X
rule #Attestation(_,_,(_,X),(_,_),_,_,_).source_block    => X
rule #Attestation(_,_,(_,_),(X,_),_,_,_).target_epoch    => X
rule #Attestation(_,_,(_,_),(_,X),_,_,_).target_block    => X
rule #Attestation(_,_,(_,_),(_,_),X,_,_).head_block      => X
rule #Attestation(_,_,(_,_),(_,_),_,X,_).proposer        => X
rule #Attestation(_,_,(_,_),(_,_),_,_,X).inclusion_delay => X

syntax Attestations ::= ".Attestations"          [klabel(nilA),  smtlib(nilA)]
syntax Attestations ::= Attestation Attestations [klabel(consA), smtlib(consA)]

syntax Bool ::= Int "inA" Attestations [function, klabel(inA), smtlib(inA)]
rule V inA (A As) => true     requires V  ==Int A.attester
rule V inA (A As) => V inA As requires V =/=Int A.attester
rule V inA .Attestations => false

syntax Int ::= sizeA(Attestations) [function, smtlib(sizeA)]
rule sizeA(_ As) => 1 +Int sizeA(As)
rule sizeA(.Attestations) => 0

rule sizeA(_) >=Int 0 => true [smt-lemma]
```

## Abstract Deposits

An abstract deposit is simply a pair of the deposit owner and the deposit amount.

The extra data (e.g., signatures and Merkle proofs) for validating the deposit information is omitted in the abstract model.

```k
syntax Deposit ::= #Deposit(Int,Int) // sender, amount
syntax Int ::= Deposit ".sender" [function, functional, klabel(d_sender), smtlib(d_sender)]
syntax Int ::= Deposit ".amount" [function, functional, klabel(d_amount), smtlib(d_amount)]
rule #Deposit(X,_).sender => X
rule #Deposit(_,X).amount => X

syntax Deposits ::= List{Deposit,""}
```

## Voluntary Exits

This is a pair of a validator ID and an epoch to exit requested.

This is the same with the concrete model.

```k
syntax VoluntaryExit ::= #VoluntaryExit(Int,Int) // validator id, epoch to exit
syntax Int ::= VoluntaryExit ".validator" [function, functional, klabel(e_validator), smtlib(e_validator)]
syntax Int ::= VoluntaryExit ".epoch"     [function, functional, klabel(e_epoch)    , smtlib(e_epoch)    ]
rule #VoluntaryExit(X,_).validator => X
rule #VoluntaryExit(_,X).epoch     => X

syntax VoluntaryExits ::= ".VoluntaryExits"            [klabel(nilE), smtlib(nilE)]
syntax VoluntaryExits ::= VoluntaryExit VoluntaryExits [klabel(consE), smtlib(consE)]

syntax Bool ::= VoluntaryExit "inE" VoluntaryExits [function, klabel(inE), smtlib(inE)]
rule J inE (I Is) => true     requires J  ==K I [smt-lemma]
rule J inE (I Is) => J inE Is requires J =/=K I [smt-lemma]
rule _ inE .VoluntaryExits => false [smt-lemma]

syntax Int ::= sizeE(VoluntaryExits) [function, smtlib(sizeE)]
rule sizeE(_ Es) => 1 +Int sizeE(Es)
rule sizeE(.VoluntaryExits) => 0

rule sizeE(_) >=Int 0 => true [smt-lemma]
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
syntax Validators ::= v(ValidatorMap, IntList) [smtlib(v)]

syntax ValidatorMap ::= m(BMap, IMap, IMap, IMap, IMap, IMap, IMap) [smtlib(m)] // slashed, (balance, effective_balance), join epoch (eligible, actual), (exit epoch, withdrawable epoch)
syntax BMap ::= ValidatorMap ".slashed"                      [function, functional, klabel(v_slashed)                     , smtlib(v_slashed)                     ]
syntax IMap ::= ValidatorMap ".balance"                      [function, functional, klabel(v_balance)                     , smtlib(v_balance)                     ]
syntax IMap ::= ValidatorMap ".effective_balance"            [function, functional, klabel(v_effective_balance)           , smtlib(v_effective_balance)           ]
syntax IMap ::= ValidatorMap ".activation_eligibility_epoch" [function, functional, klabel(v_activation_eligibility_epoch), smtlib(v_activation_eligibility_epoch)]
syntax IMap ::= ValidatorMap ".activation_epoch"             [function, functional, klabel(v_activation_epoc)             , smtlib(v_activation_epoc)             ]
syntax IMap ::= ValidatorMap ".exit_epoch"                   [function, functional, klabel(v_exit_epoch)                  , smtlib(v_exit_epoch)                  ]
syntax IMap ::= ValidatorMap ".withdrawable_epoch"           [function, functional, klabel(v_withdrawable_epoch)          , smtlib(v_withdrawable_epoch)          ]
rule m(X,_,_,_,_,_,_).slashed                      => X
rule m(_,X,_,_,_,_,_).balance                      => X
rule m(_,_,X,_,_,_,_).effective_balance            => X
rule m(_,_,_,X,_,_,_).activation_eligibility_epoch => X
rule m(_,_,_,_,X,_,_).activation_epoch             => X
rule m(_,_,_,_,_,X,_).exit_epoch                   => X
rule m(_,_,_,_,_,_,X).withdrawable_epoch           => X
```

```k
syntax IntList ::= ".IntList"   [klabel(nilI),  smtlib(nilI)]
syntax IntList ::= Int IntList  [klabel(consI), smtlib(consI)]

syntax Bool ::= Int "in" IntList [function, klabel(inI), smtlib(inI)]
rule J in (I Is) => true    requires J  ==Int I [smt-lemma]
rule J in (I Is) => J in Is requires J =/=Int I [smt-lemma]
rule _ in .IntList => false [smt-lemma]

syntax Int ::= size(IntList) [function, klabel(sizeI), smtlib(sizeI)]
rule size(_ Is) => 1 +Int size(Is)
rule size(.IntList) => 0

rule size(_) >=Int 0 => true [smt-lemma]

// take the first N elements at most
syntax IntList ::= take(Int, IntList) [function, klabel(takeI), smtlib(takeI)]
rule take(N, V Vs) => V take(N -Int 1, Vs) requires N >Int 0
rule take(0, _) => .IntList
rule take(_, .IntList) => .IntList
```

```k
//syntax IMap [smt-prelude] // (define-sort IMap () (Array Int Int))
syntax IMap ::= ".IMap"                    [          klabel(emptyI),  smtlib(emptyI)]
syntax IMap ::= IMap "[" Int "<-" Int "]i" [function, klabel(storeI),  smtlib(storeI)]
syntax Int  ::= IMap "[" Int "]i"          [function, klabel(selectI), smtlib(selectI)]

rule ( M [ K1 <- V ]i ) [ K2 ]i => V         requires K1  ==Int K2 [smt-lemma]
rule ( M [ K1 <- V ]i ) [ K2 ]i => M [ K2 ]i requires K1 =/=Int K2 [smt-lemma]

// in-place update

rule ( M [ K0 <- V0 ]i ) [ K1 <- V1 ]i => M [ K0 <- V1 ]i
  requires K0 ==Int K1

rule ( M [ K0 <- V0 ]i ) [ K1 <- V1 ]i => ( M [ K1 <- V1 ]i ) [ K0 <- V0 ]i
  requires K0 =/=Int K1 andBool K1 in keys(M)

syntax IntList ::= keys(IMap) [function, klabel(keysI), smtlib(keysI)]

rule K1 in keys(M [ K2 <- _ ]i) => true          requires K1  ==Int K2
rule K1 in keys(M [ K2 <- _ ]i) => K1 in keys(M) requires K1 =/=Int K2
```

```k
//syntax BMap [smt-prelude] // (define-sort BMap () (Array Int Bool))
syntax BMap ::= ".BMap"                     [          klabel(emptyB),  smtlib(emptyB)]
syntax BMap ::= BMap "[" Int "<-" Bool "]b" [function, klabel(storeB),  smtlib(storeB)]
syntax Bool ::= BMap "[" Int "]b"           [function, klabel(selectB), smtlib(selectB)]

rule ( M [ K1 <- V ]b ) [ K2 ]b => V         requires K1  ==Int K2 [smt-lemma]
rule ( M [ K1 <- V ]b ) [ K2 ]b => M [ K2 ]b requires K1 =/=Int K2 [smt-lemma]
```

```k
syntax IList ::= ".IList"
syntax IList ::= "(" Int "," Int ")" IList

syntax IList ::= IList "[" Int "<-" Int "]ii" [function]
syntax Int   ::= IList "[" Int          "]ii" [function]

rule ( (K1, V) M ) [ K2 ]ii => V          requires K1 ==Int K2
rule ( (K1, _) M ) [ K2 ]ii => M [ K2 ]ii requires K1  >Int K2

rule ( (K1, _ ) M ) [ K2 <- V2 ]ii => (K1, V2)   M                  requires K1 ==Int K2
rule ( (K1, V1) M ) [ K2 <- V2 ]ii => (K1, V1) ( M [ K2 <- V2 ]ii ) requires K1  >Int K2
rule ( (K1, V1) M ) [ K2 <- V2 ]ii => (K2, V2) (K1, V1) M           requires K1  <Int K2

rule .IList [ K <- V ]ii => (K, V) .IList
```

```k
syntax BList ::= ".BList"
syntax BList ::= "(" Int "," Bool ")" BList

syntax BList ::= BList "[" Int "<-" Bool "]bb" [function]
syntax Bool  ::= BList "[" Int           "]bb" [function]

rule ( (K1, V) M ) [ K2 ]bb => V          requires K1 ==Int K2
rule ( (K1, _) M ) [ K2 ]bb => M [ K2 ]bb requires K1  >Int K2

rule ( (K1, _ ) M ) [ K2 <- V2 ]bb => (K1, V2)   M                  requires K1 ==Int K2
rule ( (K1, V1) M ) [ K2 <- V2 ]bb => (K1, V1) ( M [ K2 <- V2 ]bb ) requires K1  >Int K2
rule ( (K1, V1) M ) [ K2 <- V2 ]bb => (K2, V2) (K1, V1) M           requires K1  <Int K2

rule .BList [ K <- V ]bb => (K, V) .BList
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
syntax Int ::= "BASE_REWARD_FACTOR"
syntax Int ::= "BASE_REWARDS_PER_EPOCH"
syntax Int ::= "INACTIVITY_PENALTY_QUOTIENT"
syntax Int ::= "MIN_EPOCHS_TO_INACTIVITY_PENALTY"
syntax Int ::= "PROPOSER_REWARD_QUOTIENT"
```

```{.k .symbolic}
rule SLOTS_PER_EPOCH                     =>    32                   [macro]
rule MIN_ATTESTATION_INCLUSION_DELAY     =>     1                   [macro]
rule MAX_ATTESTATION_INCLUSION_DELAY     =>       SLOTS_PER_EPOCH   [macro]
rule FAR_FUTURE_EPOCH                    =>       2 ^Int 64 -Int 1  [macro]
rule MIN_DEPOSIT_AMOUNT                  =>     1 *Int (10 ^Int 9)  [macro]
rule MAX_EFFECTIVE_BALANCE               =>    32 *Int (10 ^Int 9)  [macro]
rule EJECTION_BALANCE                    =>    16 *Int (10 ^Int 9)  [macro]
rule EFFECTIVE_BALANCE_INCREMENT         =>     1 *Int (10 ^Int 9)  [macro]
rule PERSISTENT_COMMITTEE_PERIOD         =>  2048                   [macro]
rule ACTIVATION_EXIT_DELAY               =>     4                   [macro] // MAX_SEED_LOOKAHEAD
rule MIN_VALIDATOR_WITHDRAWABILITY_DELAY =>   256                   [macro]
rule MIN_PER_EPOCH_CHURN_LIMIT           =>     4                   [macro]
rule CHURN_LIMIT_QUOTIENT                => 65536                   [macro]
rule EPOCHS_PER_SLASHINGS_VECTOR         =>  8192                   [macro]
rule MIN_SLASHING_PENALTY_QUOTIENT       =>    32                   [macro]
```
```k
rule BASE_REWARD_FACTOR                  =>    64                   [macro]
rule BASE_REWARDS_PER_EPOCH              =>     4                   [macro]
rule INACTIVITY_PENALTY_QUOTIENT         =>       2 ^Int 25         [macro]
rule MIN_EPOCHS_TO_INACTIVITY_PENALTY    =>     4                   [macro]
rule PROPOSER_REWARD_QUOTIENT            =>     8                   [macro]
```

```{.k .concrete}
rule SLOTS_PER_EPOCH                     =>      4                  [macro]
rule MIN_ATTESTATION_INCLUSION_DELAY     =>      1                  [macro]
rule MAX_ATTESTATION_INCLUSION_DELAY     =>        SLOTS_PER_EPOCH  [macro]
rule FAR_FUTURE_EPOCH                    => 999999                  [macro]
rule MIN_DEPOSIT_AMOUNT                  =>      1                  [macro]
rule MAX_EFFECTIVE_BALANCE               =>      2                  [macro]
rule EJECTION_BALANCE                    =>      0                  [macro]
rule EFFECTIVE_BALANCE_INCREMENT         =>      1                  [macro]
rule PERSISTENT_COMMITTEE_PERIOD         =>      1                  [macro]
rule ACTIVATION_EXIT_DELAY               =>      1                  [macro]
rule MIN_VALIDATOR_WITHDRAWABILITY_DELAY =>      1                  [macro]
rule MIN_PER_EPOCH_CHURN_LIMIT           =>      1                  [macro]
rule CHURN_LIMIT_QUOTIENT                =>      1                  [macro]
rule EPOCHS_PER_SLASHINGS_VECTOR         =>      1                  [macro]
rule MIN_SLASHING_PENALTY_QUOTIENT       =>      1                  [macro]
```

## Macros

```k
syntax Int  ::= epochOf(Int)            [function, smtlib(epochOf)]
              | firstSlotOf(Int)        [function, smtlib(firstSlotOf)]
              | lastSlotOf(Int)         [function, smtlib(lastSlotOf)]
syntax Bool ::= isFirstSlotOfEpoch(Int) [function, smtlib(isFirstSlotOfEpoch)] // Slot is the first slot of an epoch?
```
```{.k .concrete}
rule epochOf(Slot)            => Slot /Int SLOTS_PER_EPOCH                        [macro]
rule firstSlotOf(Epoch)       => Epoch *Int SLOTS_PER_EPOCH                       [macro]
rule lastSlotOf(Epoch)        => firstSlotOf(Epoch) +Int (SLOTS_PER_EPOCH -Int 1) [macro]
rule isFirstSlotOfEpoch(Slot) => Slot %Int SLOTS_PER_EPOCH ==Int 0                [macro]
```
```{.k .symbolic}
rule epochOf(firstSlotOf(Epoch)) => Epoch [smt-lemma] // NOTE: this ensures the injectivity of firstSlotOf as well!
rule firstSlotOf(epochOf(Slot)) <=Int Slot => true [concrete, smt-lemma]
rule lastSlotOf(epochOf(Slot)) >=Int Slot => true [concrete, smt-lemma]
rule isFirstSlotOfEpoch(firstSlotOf(_)) => true [smt-lemma]

rule epochOf(Slot)      >=Int 0 => true requires Slot  >=Int 0 [concrete, smt-lemma]
rule firstSlotOf(Epoch) >=Int 0 => true requires Epoch >=Int 0 [concrete, smt-lemma]
rule lastSlotOf(Epoch)  >=Int 0 => true requires Epoch >=Int 0 [concrete, smt-lemma]

rule epochOf(Slot) <=Int Slot => true requires Slot >=Int 0 [concrete, smt-lemma]
rule firstSlotOf(Epoch) >=Int Epoch => true requires Epoch >=Int 0 [concrete, smt-lemma]
rule lastSlotOf(Epoch) >=Int Epoch => true requires Epoch >=Int 0 [concrete, smt-lemma]
rule lastSlotOf(Epoch) >=Int firstSlotOf(Epoch) => true [concrete, smt-lemma]

/*
// injectivity of firstSlotOf
rule implies(firstSlotOf(E1) ==K firstSlotOf(E2), E1 ==K E2) => true [concrete, smt-lemma]
*/
```

```k
syntax Int ::= sqrtInt(Int) [function, smtlib(sqrtInt)]
rule sqrtInt(N) => sqrtIntAux(N, N, (N +Int 1) /Int 2) [concrete]

syntax Int ::= sqrtIntAux(Int, Int, Int) [function]
rule sqrtIntAux(N, X, Y) => sqrtIntAux(N, Y, (Y +Int (N /Int Y)) /Int 2) requires Y <Int X
rule sqrtIntAux(N, X, Y) => X requires Y >=Int X
```

```k
endmodule
```
