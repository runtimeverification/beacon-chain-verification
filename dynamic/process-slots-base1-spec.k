require "verification.k"

module PROCESS-SLOTS-BASE1-SPEC

imports VERIFICATION

// Slot == TargetSlot - 1
rule
<T>
  <k> processSlots(TargetSlot) => . </k>
  <currentSlot> Slot => TargetSlot </currentSlot>
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
      <slot> TargetSlot </slot>
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
    ...
  </states>
  ...
</T>
requires true
andBool Slot +Int 1 ==Int TargetSlot
andBool isFirstSlotOfEpoch(Slot +Int 1) ==K false
// types
andBool isValidators(Vs)
andBool Slot >=Int 0
andBool LastBlockSlot >=Int 0
andBool LastJustifiedEpoch >=Int 0
andBool LastFinalizedEpoch >=Int 0
ensures true

endmodule
