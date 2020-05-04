require "verification.k"

module PROCESS-SLOTS-BASE0-SPEC

imports VERIFICATION

// Slot == TargetSlot
rule
<T>
  <k> processSlots(TargetSlot) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> Vs </validators>
      <slashedBalance> SB </slashedBalance>
      <attested> AttestedMap </attested>
      <justified> JustifiedMap </justified>
      <finalized> FinalizedMap </finalized>
    </state>
    ...
  </states>
  ...
</T>
requires true
andBool Slot ==Int TargetSlot
// types
andBool Slot >=Int 0
ensures true

endmodule
