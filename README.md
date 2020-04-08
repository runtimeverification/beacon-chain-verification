# Formal Verification of Beacon Chain Specification

Mechanized proofs of the accountable safety and the plausible liveness of [the Gasper protocol](https://arxiv.org/abs/2003.03052):
- Model and proofs (in Coq): https://github.com/runtimeverification/beacon-chain-verification/tree/master/casper/coq

Mechanized proofs of the refinement soundness of [the state transition (Phase 0)](https://github.com/ethereum/eth2.0-specs/blob/dev/specs/phase0/beacon-chain.md) w.r.t. the Gasper protocol:
- Model (in K): https://github.com/runtimeverification/beacon-chain-verification/blob/master/dynamic/dynamic-abstract-beacon-chain.md
- Proofs (in K): `*-spec.k` files in https://github.com/runtimeverification/beacon-chain-verification/tree/master/dynamic
