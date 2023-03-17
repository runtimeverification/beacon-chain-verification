# Formal Verification of Beacon Chain Specification

This repository consists of the following developments:

1. Mechanized proofs of key properties of finality in [the "Gasper" protocol](https://arxiv.org/abs/2003.03052):
	- Model and proofs (in Coq): [`casper/coq/`](casper/coq)
	- A technical report describing the model and the proofs: [`casper/report/`](casper/report)

2. _(ongoing)_ Mechanized proofs of the refinement soundness of [the state transition (Phase 0)](https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md) w.r.t. the Gasper protocol:
	- Model (in K): [`dynamic/dynamic-abstract-beacon-chain.md`](dynamic/dynamic-abstract-beacon-chain.md)
	- Proofs (in K): `*-spec.k` files in [`dynamic/`](dynamic)

3. Analysis on the weak subjectivity period for Ethereum 2.0:
    - Report:  [[PDF](weak-subjectivity/weak-subjectivity-analysis.pdf)] [[Source](weak-subjectivity)]

4. Preliminary analysis on the fork choice rule for the Beacon chain:
    - Report:  [[PDF](fork-choice-rule/preliminary-analysis-fork-choice-rule.pdf)] [[Source](https://docs.google.com/document/d/1xiSWfuqssGatVSzYobPhPR-BxgW9Q_5rydyfQvWJW-U/)]
