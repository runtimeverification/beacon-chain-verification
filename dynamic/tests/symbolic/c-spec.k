require "../../verification.k"

module C-SPEC

imports VERIFICATION

// if e has not yet been justified,
// processJustification(e) updates the <justified> entry according to the justifiability of e.
rule
<T>
  <k> processJustification(Epoch) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> Vs </validators>
      <attested> AM </attested>
      <justified> JM => ?JM2 </justified>
      <lastJustified> LastJustifiedEpoch => ?NewJustifiedEpoch </lastJustified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, EpochBoundaryBlock) </lastBlock>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires isValidators(Vs)
 andBool Epoch >=Int 1
 andBool Epoch ==Int epochOf(Slot) -Int 1
 andBool Epoch >Int LastJustifiedEpoch
 andBool select(JM, Epoch) ==K false
ensures (
(
            isJustifiable(EpochBoundaryBlock, selectA(AM, Epoch), Vs)
    andBool select(?JM2, Epoch) ==K true
    andBool ?NewJustifiedEpoch ==Int Epoch
) orBool (
    notBool isJustifiable(EpochBoundaryBlock, selectA(AM, Epoch), Vs)
    andBool select(?JM2, Epoch) ==K false
    andBool ?NewJustifiedEpoch ==Int LastJustifiedEpoch
)
)
// andBool JM ==BMap ?JM2 except SetItem(Epoch)

// if e has already been justified,
// processJustification(e) does nothing even if e is justifiable.
rule
<T>
  <k> processJustification(Epoch) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> Vs </validators>
      <attested> AM </attested>
      <justified> JM => ?JM2 </justified>
      <lastJustified> Epoch </lastJustified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, EpochBoundaryBlock) </lastBlock>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires isValidators(Vs)
 andBool Epoch >=Int 1
 andBool Epoch ==Int epochOf(Slot) -Int 1
 andBool isJustifiable(EpochBoundaryBlock, selectA(AM, Epoch), Vs)
 andBool select(JM, Epoch) ==K true
ensures  select(?JM2, Epoch) ==K true
// andBool JM ==BMap ?JM2 except SetItem(Epoch)

endmodule
