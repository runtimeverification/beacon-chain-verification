require "../../verification.k"

module F-SPEC

imports VERIFICATION

// processJustification(e - 2) followed by processJustification(e - 1)
// update the <justified> entries properly according to the justifiability of e - 2 and e - 1,
// where e is the current epoch.
rule
<T>
  <k> case(xor2(
                LastJustifiedEpoch <Int Epoch2
        andBool select(Epoch1JustifiedMap, Epoch2) ==K false
      ,
                LastJustifiedEpoch ==Int Epoch2
        andBool select(Epoch1JustifiedMap, Epoch2) ==K true
        andBool isJustifiable(Epoch2BoundaryBlock, selectA(Epoch1Attested, Epoch2), Vs)
      ))
   ~> processJustification(Epoch2)
   ~> processJustification(Epoch1) => . </k>
  <currentSlot> firstSlotOf(Epoch) </currentSlot>
  <states>
    <state>
      <slot> firstSlotOf(Epoch2) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, Epoch2BoundaryBlock) </lastBlock>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch1) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, Epoch1BoundaryBlock) </lastBlock>
      <attested> Epoch1Attested </attested>
      <justified> Epoch1JustifiedMap </justified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch) </slot>
      <validators> Vs </validators>
      <attested> AM </attested>
      <justified> JM => ?JM2 </justified>
      <lastJustified> LastJustifiedEpoch => ?NewJustifiedEpoch </lastJustified>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires isValidators(Vs)
 andBool Epoch1 ==Int Epoch -Int 1
 andBool Epoch2 ==Int Epoch -Int 2
 // ranges
 andBool Epoch >=Int 0
 andBool Epoch1 >=Int 0
 andBool Epoch2 >=Int 0
 andBool LastJustifiedEpoch >=Int 0
 andBool selectA(AM, Epoch2) ==K super(selectA(Epoch1Attested, Epoch2))
 // invariant
 andBool select(JM, Epoch2) ==K select(Epoch1JustifiedMap, Epoch2)
 andBool select(JM, Epoch1) ==K false
 //
 andBool (notBool LastJustifiedEpoch <Int Epoch2 orBool select(Epoch1JustifiedMap, Epoch2) ==K false)
 andBool (notBool LastJustifiedEpoch ==Int Epoch2 orBool select(Epoch1JustifiedMap, Epoch2) ==K true)
// andBool (notBool select(Epoch1JustifiedMap, Epoch2) ==K true orBool isJustifiable(Epoch2BoundaryBlock, selectA(Epoch1Attested, Epoch2), Vs))
 andBool select(Epoch1JustifiedMap, Epoch2) ==K isJustifiable(Epoch2BoundaryBlock, selectA(Epoch1Attested, Epoch2), Vs)
 andBool LastJustifiedEpoch <=Int Epoch2

ensures ?NewJustifiedEpoch >=Int 0 andBool
(
    (
            (
                        isJustifiable(Epoch2BoundaryBlock, selectA(AM, Epoch2), Vs)
                andBool select(?JM2, Epoch2) ==K true
            ) orBool (
                notBool isJustifiable(Epoch2BoundaryBlock, selectA(AM, Epoch2), Vs)
                andBool select(?JM2, Epoch2) ==K false
            )
    ) orBool (
            (
                        isJustifiable(Epoch1BoundaryBlock, selectA(AM, Epoch1), Vs)
                andBool select(?JM2, Epoch1) ==K true
            ) orBool (
                notBool isJustifiable(Epoch1BoundaryBlock, selectA(AM, Epoch1), Vs)
                andBool select(?JM2, Epoch1) ==K false
            )
    )
) andBool (
    (
                        notBool isJustifiable(Epoch2BoundaryBlock, selectA(AM, Epoch2), Vs)
                andBool notBool isJustifiable(Epoch1BoundaryBlock, selectA(AM, Epoch1), Vs)
                andBool ?NewJustifiedEpoch ==Int LastJustifiedEpoch
    ) orBool (
                                isJustifiable(Epoch2BoundaryBlock, selectA(AM, Epoch2), Vs)
                andBool notBool isJustifiable(Epoch1BoundaryBlock, selectA(AM, Epoch1), Vs)
                andBool ?NewJustifiedEpoch ==Int Epoch2
    ) orBool (
                                isJustifiable(Epoch1BoundaryBlock, selectA(AM, Epoch1), Vs)
                andBool ?NewJustifiedEpoch ==Int Epoch1
    )
)
 andBool JM ==BMap ?JM2 except SetItem(Epoch1) SetItem(Epoch2)

endmodule
