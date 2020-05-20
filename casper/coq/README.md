# Modeling and Verifying Casper in Coq

This part of the repository gives a formalization in Coq of the most recent version of Casper FFG, which is one of two main ingredients of the Gasper protocol (an abstraction of the Beacon Chain specification described [here](https://arxiv.org/abs/2003.03052)). With this formalization, we mechanize proofs of three main results of Casper:

- Accountable safety: No two conflicting blocks are finalized without having at least 1/3 of validator deposits slashed.

- Plausible liveness: Assuming that at least 2/3 of validators (by deposit) follow the protocol, it is always possible to continue to finalize new blocks irrespective of what has happened before.

- Slashable bound: Even when the set of active validators is dynamic, a lower bound (given in terms of validator activation and exit policies) on what stake worth of validators is provably slashable can be guaranteed.

This development is based on previously developed models and proofs of Casper in Coq [here](https://github.com/runtimeverification/casper-proofs). It extends that work in three significant ways:

- It unifies the two distinct models built sepearately for safey and liveness, and proves both properties in the same unified model.

- It generalizes the definition of finalization to k-finalization (as defined in the [Gasper protocol](https://arxiv.org/abs/2003.03052)), along with the accountable safety proof.

- It generalizes the protocol to dynamic validator sets, generalizes the safety and liveness proofs and proves the slashable bound theorem.

A more detailed explanation of the models and proofs can be found in the technical report:

<img src="../../resources/pdf-icon.png" alt="PDF" width="2%" /> *[Formal Modeling and Verification of Casper FFG in Coq - TBA](#)*

## Model Layout

### Utility files

- [NatExt.v](theories/NatExt.v): some additional properties of natural numbers
- [SetTheoryProps.v](theories/SetTheoryProps.v): some additional set-theoretic properties
- [StrongInductionLtn.v](theories/StrongInductionLtn.v): some strong induction principles on natural numbers, adapted from work by Tej Chajed

### Casper abstract model

These files define an abstract view of Casper's validators, blocks and votes, and specify its justification and finalization mechanisms.

- [Validator.v](theories/Validator.v): validators and their stake
- [Weight.v](theories/Weight.v): weights of validator sets and their properties
- [HashTree.v](theories/HashTree.v): the checkpoint block trees and their properties
- [State.v](theories/State.v): the state as a set of votes cast
- [Slashing.v](theories/Slashing.v): the slashing conditions
- [Quorums.v](theories/Quorums.v): Quorum predicates and properties
- [Justification.v](theories/Justification.v): justification and finalization definitions and their properties


### Casper properties

These files contain the major theorems about Casper.

- [AccountableSafety.v](theories/AccountableSafety.v): Proof of the Accountable Safety theorem
- [PlausibleLiveness.v](theories/PlausibleLiveness.v): Proof of the Plausible Liveness theorem
- [SlashableBound.v](theories/SlashableBound.v): Proof of the Slashable Bound theorem

## Requirements

* [Coq 8.9 or 8.10](https://coq.inria.fr)
* [Mathematical Components 1.8 or 1.9](http://math-comp.github.io/math-comp/) (`ssreflect`)
* [CoqHammer 1.0.9](https://github.com/lukaszcz/coqhammer)
* [finmap](https://github.com/math-comp/finmap)

## Building

We recommend installing dependencies via [OPAM](http://opam.ocaml.org/doc/Install.html):

```
opam repo add coq-released https://coq.inria.fr/opam/released
opam install coq coq-mathcomp-ssreflect coq-hammer coq-mathcomp-finmap
```

Then, run `make` in the directory of this README to check all definitions and proofs.

## Getting Help

Feel free to report GitHub issues here or to contact us at: [contact@runtimeverification.com](contact@runtimeverification.com).
