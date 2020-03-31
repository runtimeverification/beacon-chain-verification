require "../../verification.k"

module K1B-SPEC

imports VERIFICATION

// Slot + 1 == TargetSlot
// using `_`
rule
<T>
  <k> processSlots(TargetSlot) => . </k>
  <currentSlot> Slot => Slot +Int 1 </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> Vs </validators>
      <slashedBalance> SB </slashedBalance>
      <attested> AttestedMap </attested>
      <justified> JustifiedMap </justified>
      <finalized> FinalizedMap </finalized>
      <lastBlock> (LastBlockSlot, LastBlockID) </lastBlock>
      <lastJustified> LastJustifiedEpoch </lastJustified>
      <lastFinalized> LastFinalizedEpoch </lastFinalized>
    </state>
  (
    .Bag
  =>
    <state>
      <slot> Slot +Int 1 </slot>
      <validators> Vs </validators>
      <slashedBalance> SB </slashedBalance>
      <attested> AttestedMap </attested>
      <justified> JustifiedMap </justified>
      <finalized> FinalizedMap </finalized>
      <lastBlock> (LastBlockSlot, LastBlockID) </lastBlock>
      <lastJustified> LastJustifiedEpoch </lastJustified>
      <lastFinalized> LastFinalizedEpoch </lastFinalized>
    </state>
  )
    _  // NOTE: `_` instead of `...`
  </states>
  ...
</T>
requires true
andBool TargetSlot ==Int Slot +Int 1
andBool isFirstSlotOfEpoch(TargetSlot) ==K false
// types
andBool Slot >=Int 0
andBool LastBlockSlot >=Int 0
andBool LastJustifiedEpoch >=Int 0
andBool LastFinalizedEpoch >=Int 0
ensures true

endmodule
