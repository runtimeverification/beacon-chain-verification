require "../../verification.k"

module A-SPEC

imports VERIFICATION

// processJustification(e) justifies e if e is justifiable.
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
 //
 andBool select(JM, Epoch) ==K false
ensures  select(?JM2, Epoch) ==K true
// andBool JM ==BMap ?JM2 except SetItem(Epoch)
// andBool (?X:Int ==Int Epoch orBool select(JM, ?X) ==K select(?JM2, ?X))

endmodule
