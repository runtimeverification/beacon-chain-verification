require "../../verification.k"

module D-SPEC

imports VERIFICATION

// processJustification(e) updates the <justified> entry properly according to the justifiability of e,
// even when e has been already justified.
rule
<T>
  <k> case(xor2(
                LastJustifiedEpoch <Int Epoch
        andBool OldEpochJustifiedBlock ==K none
      ,
                LastJustifiedEpoch ==Int Epoch
        andBool OldEpochJustifiedBlock ==K some EpochBoundaryBlock
        andBool LastJustifiedBlock ==K EpochBoundaryBlock
      ))
   ~> processJustification(Epoch) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> Vs </validators>
      <attested>
        Epoch |-> Attestations
        ...
      </attested>
      <justified>
        Epoch |-> (OldEpochJustifiedBlock:Option => ?NewEpochJustifiedBlock:Option)
        ...
      </justified>
      <lastJustified>
        (LastJustifiedEpoch, LastJustifiedBlock)
      =>
        (?NewJustifiedEpoch, ?NewJustifiedBlock)
      </lastJustified>
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
ensures (
    LastJustifiedEpoch <Int Epoch andBool (
        (
                    isJustifiable(EpochBoundaryBlock, Attestations, Vs)
            andBool ?NewEpochJustifiedBlock ==K some EpochBoundaryBlock
            andBool ?NewJustifiedEpoch ==Int Epoch
            andBool ?NewJustifiedBlock ==Int EpochBoundaryBlock
        ) orBool (
            notBool isJustifiable(EpochBoundaryBlock, Attestations, Vs)
            andBool ?NewEpochJustifiedBlock ==K none
            andBool ?NewJustifiedEpoch ==Int LastJustifiedEpoch
            andBool ?NewJustifiedBlock ==Int LastJustifiedBlock
        )
    )
) orBool (
    LastJustifiedEpoch ==Int Epoch andBool (
                ?NewEpochJustifiedBlock ==K OldEpochJustifiedBlock
        andBool ?NewJustifiedEpoch ==Int LastJustifiedEpoch
        andBool ?NewJustifiedBlock ==Int LastJustifiedBlock
    )
)

endmodule
