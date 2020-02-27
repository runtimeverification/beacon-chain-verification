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
        Epoch |-> (false => ?EpochJustifiedBlock:Bool)
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
 andBool Epoch >Int LastJustifiedEpoch
ensures (
            isJustifiable(EpochBoundaryBlock, Attestations, Vs)
    andBool ?EpochJustifiedBlock ==K true
    andBool ?NewJustifiedEpoch ==Int Epoch
) orBool (
    notBool isJustifiable(EpochBoundaryBlock, Attestations, Vs)
    andBool ?EpochJustifiedBlock ==K false
    andBool ?NewJustifiedEpoch ==Int LastJustifiedEpoch
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
        Epoch |-> true
        ...
      </justified>
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
 andBool isJustifiable(EpochBoundaryBlock, Attestations, Vs)

endmodule
