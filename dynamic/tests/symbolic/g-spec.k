require "../../verification.k"

module G-SPEC

imports VERIFICATION

// processJustification(e - 2) followed by processJustification(e - 1)
// update the <justified> entries properly according to the justifiability of e - 2 and e - 1,
// where e is the current epoch.
rule
<T>
  <k> case(xor3(
                notBool isJustifiable(Epoch3BoundaryBlock, selectA(Epoch1AttestedMap, Epoch3), Vs)
        andBool notBool isJustifiable(Epoch2BoundaryBlock, selectA(Epoch1AttestedMap, Epoch2), Vs)
        andBool PrevLastJustifiedEpoch <Int Epoch3
        andBool select(Epoch1JustifiedMap, Epoch3) ==K false
        andBool select(Epoch1JustifiedMap, Epoch2) ==K false
      ,
                        isJustifiable(Epoch3BoundaryBlock, selectA(Epoch1AttestedMap, Epoch3), Vs)
        andBool notBool isJustifiable(Epoch2BoundaryBlock, selectA(Epoch1AttestedMap, Epoch2), Vs)
        andBool PrevLastJustifiedEpoch ==Int Epoch3
        andBool select(Epoch1JustifiedMap, Epoch3) ==K true
        andBool select(Epoch1JustifiedMap, Epoch2) ==K false
      ,
                        isJustifiable(Epoch2BoundaryBlock, selectA(Epoch1AttestedMap, Epoch2), Vs)
        andBool PrevLastJustifiedEpoch ==Int Epoch2
        andBool select(Epoch1JustifiedMap, Epoch2) ==K true
      ))
   ~> processJustification(Epoch2)
   ~> processJustification(Epoch1) => . </k>
  <currentSlot> firstSlotOf(Epoch) </currentSlot>
  <states>
    <state>
      <slot> firstSlotOf(Epoch3) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, Epoch3BoundaryBlock) </lastBlock>
      ...
    </state>
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
      <attested> Epoch1AttestedMap </attested>
      <justified> Epoch1JustifiedMap </justified>
      <lastJustified> PrevLastJustifiedEpoch </lastJustified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch) </slot>
      <validators> Vs </validators>
      <attested> AttestedMap </attested>
      <justified> PrevJustifiedMap => ?PostJustifiedMap </justified>
      <lastJustified> LastJustifiedEpoch => ?NewLastJustifiedEpoch </lastJustified>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires isValidators(Vs)
 andBool Epoch1 ==Int Epoch -Int 1
 andBool Epoch2 ==Int Epoch -Int 2
 andBool Epoch3 ==Int Epoch -Int 3
 //
 andBool select(PrevJustifiedMap, Epoch2) ==K select(Epoch1JustifiedMap, Epoch2)
 andBool LastJustifiedEpoch ==Int PrevLastJustifiedEpoch
 // ranges
 andBool Epoch >=Int 0
 andBool Epoch1 >=Int 0
 andBool Epoch2 >=Int 0
 andBool Epoch3 >=Int 0
 andBool PrevLastJustifiedEpoch >=Int 0
 andBool selectA(AttestedMap, Epoch2) ==K super(selectA(Epoch1AttestedMap, Epoch2))
 // inv
 andBool select(PrevJustifiedMap, Epoch1) ==K false

 andBool PrevLastJustifiedEpoch <=Int Epoch2
 andBool (notBool PrevLastJustifiedEpoch  <Int Epoch3 orBool (select(Epoch1JustifiedMap, Epoch3) ==K false andBool select(Epoch1JustifiedMap, Epoch2) ==K false))
 andBool (notBool PrevLastJustifiedEpoch ==Int Epoch3 orBool (select(Epoch1JustifiedMap, Epoch3) ==K true  andBool select(Epoch1JustifiedMap, Epoch2) ==K false))
 andBool (notBool PrevLastJustifiedEpoch ==Int Epoch2 orBool select(Epoch1JustifiedMap, Epoch2) ==K true)
 andBool select(Epoch1JustifiedMap, Epoch3) ==K isJustifiable(Epoch3BoundaryBlock, selectA(Epoch1AttestedMap, Epoch3), Vs)
 andBool select(Epoch1JustifiedMap, Epoch2) ==K isJustifiable(Epoch2BoundaryBlock, selectA(Epoch1AttestedMap, Epoch2), Vs)


ensures ?NewLastJustifiedEpoch >=Int 0 andBool
(
      (
                notBool isJustifiable(Epoch2BoundaryBlock, selectA(AttestedMap, Epoch2), Vs)
        andBool notBool isJustifiable(Epoch1BoundaryBlock, selectA(AttestedMap, Epoch1), Vs)
        andBool ?NewLastJustifiedEpoch <Int Epoch2
        andBool select(?PostJustifiedMap, Epoch2) ==K false
        andBool select(?PostJustifiedMap, Epoch1) ==K false
      ) orBool (
                        isJustifiable(Epoch2BoundaryBlock, selectA(AttestedMap, Epoch2), Vs)
        andBool notBool isJustifiable(Epoch1BoundaryBlock, selectA(AttestedMap, Epoch1), Vs)
        andBool ?NewLastJustifiedEpoch ==Int Epoch2
        andBool select(?PostJustifiedMap, Epoch2) ==K true
        andBool select(?PostJustifiedMap, Epoch1) ==K false
      ) orBool (
                        isJustifiable(Epoch1BoundaryBlock, selectA(AttestedMap, Epoch1), Vs)
        andBool ?NewLastJustifiedEpoch ==Int Epoch1
        andBool select(?PostJustifiedMap, Epoch1) ==K true
      )
)
 andBool PrevJustifiedMap ==BMap ?PostJustifiedMap except SetItem(Epoch1) SetItem(Epoch2)

endmodule
