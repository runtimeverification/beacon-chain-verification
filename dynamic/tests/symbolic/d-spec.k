require "../../verification.k"

module D-SPEC

imports VERIFICATION

// processJustification(e) updates the <justified> entry properly according to the justifiability of e,
// even when e has been already justified.
rule
<T>
  <k> case(xor2(
                LastJustifiedEpoch <Int Epoch
        andBool select(JM, Epoch) ==K false
      ,
                LastJustifiedEpoch ==Int Epoch
        andBool select(JM, Epoch) ==K true
      ))
   ~> processJustification(Epoch) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> Vs </validators>
      <attested> AM </attested>
      <justified> JM => ?JM2 </justified>
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
 // invariant
 andBool (notBool LastJustifiedEpoch <Int Epoch orBool select(JM, Epoch) ==K false)
 andBool (notBool LastJustifiedEpoch ==Int Epoch orBool select(JM, Epoch) ==K true)
 andBool LastJustifiedEpoch <=Int Epoch
ensures 
(
(
    LastJustifiedEpoch <Int Epoch andBool (
        (
                    isJustifiable(EpochBoundaryBlock, selectA(AM, Epoch), Vs)
            andBool select(?JM2, Epoch) ==K true
            andBool ?NewJustifiedEpoch ==Int Epoch
        ) orBool (
            notBool isJustifiable(EpochBoundaryBlock, selectA(AM, Epoch), Vs)
            andBool select(?JM2, Epoch) ==K false
            andBool ?NewJustifiedEpoch ==Int LastJustifiedEpoch
        )
    )
) orBool (
    LastJustifiedEpoch ==Int Epoch andBool (
                select(?JM2, Epoch) ==K select(JM, Epoch)
        andBool ?NewJustifiedEpoch ==Int LastJustifiedEpoch
    )
)
)
 andBool JM ==BMap ?JM2 except SetItem(Epoch)

endmodule
