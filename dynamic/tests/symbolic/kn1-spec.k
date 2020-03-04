require "../../verification.k"

module KN1-SPEC

imports VERIFICATION

// TODO: when Slot == Target, the additional <state> cell should be idempotent
//       when Slot < Target, it needs to know that: lastSlotOf(epochOf(Slot)) == lastSlotOf(epochOf(Slot + 1))
/*
rule lastSlotOf(epochOf(Slot)) ==K lastSlotOf(epochOf(Slot +Int 1)) => true
    requires Slot < lastSlotOf(epochOf(Slot))

rule lastSlotOf(epochOf(Slot +Int 1)) ==K lastSlotOf(epochOf(Slot)) => true
    requires Slot < lastSlotOf(epochOf(Slot))
*/

// Slot + N == TargetSlot
// where 0 <= N <=  SLOTS_PER_EPOCH - 1
// loop invariant
// Slot <= TargetSlot
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
    ?_  // NOTE: this captures (zero or more) other <state>s
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
    _
  </states>
  ...
</T>
requires true
andBool Slot <=Int TargetSlot
andBool TargetSlot ==Int lastSlotOf(epochOf(Slot)) // NOTE: this already implies Slot <=Int TargetSlot
// types
andBool isValidators(Vs)
andBool Slot >=Int 0
andBool TargetSlot >=Int 0
andBool LastBlockSlot >=Int 0
andBool LastJustifiedEpoch >=Int 0
andBool LastFinalizedEpoch >=Int 0
ensures true

endmodule
