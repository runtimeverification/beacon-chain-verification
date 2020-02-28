require "../../verification.k"

module B-SPEC

imports VERIFICATION

// once processJustification(e) justifies e, then the subsequent processJustification(e) alters nothing.
rule
<T>
  <k> processJustification(Epoch) ~> processJustification(Epoch) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> Vs </validators>
      <attested> AM </attested>
      <justified> JM => ?JM2 </justified>
      <lastJustified> _ => Epoch </lastJustified>
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
requires Slot ==Int firstSlotOf(Epoch +Int 1)
 andBool Epoch >=Int 1
 andBool isValidators(Vs)
 andBool isJustifiable(EpochBoundaryBlock, selectA(AM, Epoch), Vs)
 andBool select(JM, Epoch) ==K false
ensures  select(?JM2, Epoch) ==K true
// andBool JM ==BMap ?JM2 except SetItem(Epoch)

endmodule
