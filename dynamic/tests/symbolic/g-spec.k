require "../../verification.k"

module G-SPEC

imports VERIFICATION

// processJustification(e - 2) followed by processJustification(e - 1)
// update the <justified> entries properly according to the justifiability of e - 2 and e - 1,
// where e is the current epoch.
rule
<T>
  <k> case(xor3(
                notBool isJustifiable(Epoch3BoundaryBlock, PrevAttestations3, Vs)
        andBool notBool isJustifiable(Epoch2BoundaryBlock, PrevAttestations2, Vs)
        andBool PrevLastJustifiedEpoch <Int Epoch3
        andBool PrevEpoch3JustifiedBlock ==K false
        andBool PrevEpoch2JustifiedBlock ==K false
      ,
                        isJustifiable(Epoch3BoundaryBlock, PrevAttestations3, Vs)
        andBool notBool isJustifiable(Epoch2BoundaryBlock, PrevAttestations2, Vs)
        andBool PrevLastJustifiedEpoch ==Int Epoch3
        andBool PrevEpoch3JustifiedBlock ==K true
        andBool PrevEpoch2JustifiedBlock ==K false
      ,
                        isJustifiable(Epoch2BoundaryBlock, PrevAttestations2, Vs)
        andBool PrevLastJustifiedEpoch ==Int Epoch2
        andBool PrevEpoch2JustifiedBlock ==K true
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
      <attested>
        Epoch3 |-> PrevAttestations3:Attestations
        Epoch2 |-> PrevAttestations2:Attestations
        ...
      </attested>
      <justified>
        Epoch3 |-> PrevEpoch3JustifiedBlock:Bool
        Epoch2 |-> PrevEpoch2JustifiedBlock:Bool
        ...
      </justified>
      <lastJustified> PrevLastJustifiedEpoch </lastJustified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch) </slot>
      <validators> Vs </validators>
      <attested>
        Epoch2 |-> Attestations2:Attestations
        Epoch1 |-> Attestations1:Attestations
        ...
      </attested>
      <justified>
        Epoch2 |-> (Epoch2JustifiedBlock:Bool => ?NewEpoch2JustifiedBlock:Bool)
        Epoch1 |-> (false                     => ?NewEpoch1JustifiedBlock:Bool)
        ...
      </justified>
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
 andBool Epoch2JustifiedBlock ==K PrevEpoch2JustifiedBlock
 andBool LastJustifiedEpoch ==Int PrevLastJustifiedEpoch
 // ranges
 andBool Epoch >=Int 0
 andBool Epoch1 >=Int 0
 andBool Epoch2 >=Int 0
 andBool Epoch3 >=Int 0
 andBool PrevLastJustifiedEpoch >=Int 0
 andBool Attestations2 ==K super(PrevAttestations2)
ensures ?NewLastJustifiedEpoch >=Int 0 andBool
(
      (
                notBool isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs)
        andBool notBool isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs)
        andBool ?NewLastJustifiedEpoch <Int Epoch2
        andBool ?NewEpoch2JustifiedBlock ==K false
        andBool ?NewEpoch1JustifiedBlock ==K false
      ) orBool (
                        isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs)
        andBool notBool isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs)
        andBool ?NewLastJustifiedEpoch ==Int Epoch2
        andBool ?NewEpoch2JustifiedBlock ==K true
        andBool ?NewEpoch1JustifiedBlock ==K false
      ) orBool (
                        isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs)
        andBool ?NewLastJustifiedEpoch ==Int Epoch1
        andBool ?NewEpoch1JustifiedBlock ==K true
      )
)

endmodule
