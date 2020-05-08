require "verification.k"

module PROCESS-ATTESTATION-SPEC

imports VERIFICATION

rule
<T>
  <k> processAttestations(As) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(VM, _) </validators>
      <attested>
        ?Epoch -Int 1 |-> (PrevAs1:Attestations => ?PrevAs2)
        ?Epoch        |-> (CurrAs1:Attestations => ?CurrAs2)
        ...
      </attested>
      ...
    </state>
    <state>
      <slot> Slot -Int 1 </slot>
      <validators> v(ORIG_VM, ORIG_VIDs) </validators>
      ...
    </state>
    ...
  </states>
  <lastJustified> LastJustifiedEpoch </lastJustified>
  <lastBlock> BlockMap </lastBlock>
  ...
</T>
requires true
// types
andBool Slot >=Int 1
// let-bindings
andBool ?Epoch ==Int epochOf(Slot)
// pre-conditions
andBool ?Epoch >=Int 1
andBool isValidAttestationListPartial(As, Slot, LastJustifiedEpoch, BlockMap)
andBool forall(x, getValidatorsA(As), VM.slashed[x]b ==K false)
// invariants
ensures true
// post-conditions
andBool ?PrevAs2 ==K revA(getAttestations(As, ?Epoch -Int 1)) ++A PrevAs1
andBool ?CurrAs2 ==K revA(getAttestations(As, ?Epoch       )) ++A CurrAs1

rule
<T>
  <k> processAttestationsAux(L_As, As) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(VM, _) </validators>
      <attested>
        ?Epoch -Int 1 |-> (getAttestations(L_As, ?Epoch -Int 1) ++A PrevAs0:Attestations => ?PrevAs2)
        ?Epoch        |-> (getAttestations(L_As, ?Epoch       ) ++A CurrAs0:Attestations => ?CurrAs2)
        ...
      </attested>
      ...
    </state>
    <state>
      <slot> Slot -Int 1 </slot>
      <validators> v(ORIG_VM, ORIG_VIDs) </validators>
      ...
    </state>
    ...
  </states>
  <lastJustified> LastJustifiedEpoch </lastJustified>
  <lastBlock> BlockMap </lastBlock>
  ...
</T>
requires true
// types
andBool Slot >=Int 1
// let-bindings
andBool ?Epoch ==Int epochOf(Slot)
andBool ?PrevAs1 ==K getAttestations(L_As, ?Epoch -Int 1) ++A PrevAs0
andBool ?CurrAs1 ==K getAttestations(L_As, ?Epoch       ) ++A CurrAs0
// pre-conditions
andBool ?Epoch >=Int 1
andBool isValidAttestationListPartial(As, Slot, LastJustifiedEpoch, BlockMap)
andBool forall(x, getValidatorsA(As), VM.slashed[x]b ==K false)
// invariants
ensures true
// post-conditions
andBool ?PrevAs2 ==K revA(getAttestations(As, ?Epoch -Int 1)) ++A ?PrevAs1
andBool ?CurrAs2 ==K revA(getAttestations(As, ?Epoch       )) ++A ?CurrAs1
[matching(concatA)]

endmodule
