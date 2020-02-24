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
      <attested>
        Epoch |-> Attestations:Attestations
        ...
      </attested>
      <justified>
        Epoch |-> (none => some EpochBoundaryBlock)
        ...
      </justified>
      <lastJustified> _ => (Epoch, EpochBoundaryBlock) </lastJustified>
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
 andBool isJustifiable(EpochBoundaryBlock, Attestations, Vs)

endmodule
