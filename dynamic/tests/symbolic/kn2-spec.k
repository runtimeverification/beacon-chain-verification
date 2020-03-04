require "../../verification.k"

module KN2-SPEC

imports VERIFICATION

// TODO: it needs to know that: Slot + N == lastSlotOf(epochOf(Slot))
/*
rule (Slot +Int N) %Int SLOTS_PER_EPOCH ==K 0 => false  // isFirstSlotOfEpoch(Slot +Int N) => false
    requires (Slot +Int N) <=Int lastSlotOf(epochOf(Slot))
*/
/* not needed
rule Slot +Int (SLOTS_PER_EPOCH -Int 1) <Int lastSlotOf(epochOf(Slot)) => false
*/

// Slot + N == TargetSlot
// where 1 <= N <= SLOTS_PER_EPOCH - 1
// loop invariant
// Slot < TargetSlot
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
andBool Slot <Int TargetSlot
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
