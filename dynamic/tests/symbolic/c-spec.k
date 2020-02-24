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
      <attested>
        Epoch |-> Attestations
        ...
      </attested>
      <justified>
        Epoch |-> (none => ?EpochJustifiedBlock:Option)
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
 andBool Epoch >Int LastJustifiedEpoch
ensures (
            isJustifiable(EpochBoundaryBlock, Attestations, Vs)
    andBool ?EpochJustifiedBlock ==K some EpochBoundaryBlock
    andBool ?NewJustifiedEpoch ==Int Epoch
    andBool ?NewJustifiedBlock ==Int EpochBoundaryBlock
) orBool (
    notBool isJustifiable(EpochBoundaryBlock, Attestations, Vs)
    andBool ?EpochJustifiedBlock ==K none
    andBool ?NewJustifiedEpoch ==Int LastJustifiedEpoch
    andBool ?NewJustifiedBlock ==Int LastJustifiedBlock
)

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
      <attested>
        Epoch |-> Attestations
        ...
      </attested>
      <justified>
        Epoch |-> some EpochBoundaryBlock
        ...
      </justified>
      <lastJustified>
        (Epoch, EpochBoundaryBlock)
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
 andBool isJustifiable(EpochBoundaryBlock, Attestations, Vs)

endmodule
