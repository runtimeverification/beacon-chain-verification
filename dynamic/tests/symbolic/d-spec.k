require "../../verification.k"

module D-SPEC

imports VERIFICATION

// processJustification(e) updates the <justified> entry properly according to the justifiability of e,
// even when e has been already justified.
rule
<T>
  <k> case(xor2(
                LastJustifiedEpoch <Int Epoch
        andBool OldEpochJustifiedBlock ==K false
      ,
                LastJustifiedEpoch ==Int Epoch
        andBool OldEpochJustifiedBlock ==K true
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
        Epoch |-> (OldEpochJustifiedBlock:Bool => ?NewEpochJustifiedBlock:Bool)
        ...
      </justified>
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
ensures (
    LastJustifiedEpoch <Int Epoch andBool (
        (
                    isJustifiable(EpochBoundaryBlock, Attestations, Vs)
            andBool ?NewEpochJustifiedBlock ==K true
            andBool ?NewJustifiedEpoch ==Int Epoch
        ) orBool (
            notBool isJustifiable(EpochBoundaryBlock, Attestations, Vs)
            andBool ?NewEpochJustifiedBlock ==K false
            andBool ?NewJustifiedEpoch ==Int LastJustifiedEpoch
        )
    )
) orBool (
    LastJustifiedEpoch ==Int Epoch andBool (
                ?NewEpochJustifiedBlock ==K OldEpochJustifiedBlock
        andBool ?NewJustifiedEpoch ==Int LastJustifiedEpoch
    )
)

endmodule
