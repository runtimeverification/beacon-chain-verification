requires "verification.k"

module SIMPLE-SPEC

imports VERIFICATION

// processSlot() does nothing.
rule
<T>
  <k> processSlot() => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    ...
    <state>
      <slot> Slot </slot>
      <validators> Vs </validators>
      <slashedBalance> Ss </slashedBalance>
      <attested> As </attested>
      <justified> Js </justified>
      <finalized> Fs </finalized>
      <lastBlock> (LastBlockSlot, LastBlockID) </lastBlock>
      <lastJustified> (LastJustifiedEpoch, LastJustifiedBlock) </lastJustified>
      <lastFinalized> (LastFinalizedEpoch, LastFinalizedBlock) </lastFinalized>
    </state>
  </states>
  <blocks>
    ...
    <block>
      <bSlot> LastBlockSlot </bSlot> <bID> LastBlockID </bID>
      <parent> (ParentSlot, ParentID) </parent>
      <slashings> .Slashings </slashings>
      <attestations> .Attestations </attestations>
      <deposits> .Deposits </deposits>
      <exits> .VoluntaryExits </exits>
    </block>
  </blocks>
</T>

// processSlots(s) does nothing if s is the current slot.
rule
<T>
  <k> processSlots(Slot) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    ...
    <state>
      <slot> Slot </slot>
      <validators> Vs </validators>
      <slashedBalance> Ss </slashedBalance>
      <attested> As </attested>
      <justified> Js </justified>
      <finalized> Fs </finalized>
      <lastBlock> (LastBlockSlot, LastBlockID) </lastBlock>
      <lastJustified> (LastJustifiedEpoch, LastJustifiedBlock) </lastJustified>
      <lastFinalized> (LastFinalizedEpoch, LastFinalizedBlock) </lastFinalized>
    </state>
  </states>
  <blocks>
    ...
    <block>
      <bSlot> LastBlockSlot </bSlot> <bID> LastBlockID </bID>
      <parent> (ParentSlot, ParentID) </parent>
      <slashings> .Slashings </slashings>
      <attestations> .Attestations </attestations>
      <deposits> .Deposits </deposits>
      <exits> .VoluntaryExits </exits>
    </block>
  </blocks>
</T>

// processJustification(e) does nothing if no validator exist.
rule
<T>
  <k> processJustification(Epoch) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    ...
    <state>
      <slot> firstSlotOf(Epoch) </slot>
      <validators> .Map </validators>
      <lastBlock> (_, EpochBoundaryBlock) </lastBlock>
      ...
    </state>
    <state>
      <slot> Slot </slot>
      <validators> .Map </validators>
      <attested>
        Epoch |-> .Attestations
        ...
      </attested>
      ...
    </state>
  </states>
  ...
</T>
// TODO: why is this condition not needed?
// requires Slot ==Int firstSlotOf(Epoch +Int 1)

endmodule
