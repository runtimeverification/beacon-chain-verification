require "../../verification.k"

module G-SPEC

imports VERIFICATION

// processJustification(e - 2) followed by processJustification(e - 1)
// update the <justified> entries properly according to the justifiability of e - 2 and e - 1,
// where e is the current epoch.
rule
<T>
  <k> case(xor3(
        PrevLastJustifiedEpoch  <Int Epoch3
      ,
        PrevLastJustifiedEpoch ==Int Epoch3
      ,
        PrevLastJustifiedEpoch ==Int Epoch2
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
requires true
 andBool Epoch1 ==Int Epoch -Int 1
 andBool Epoch2 ==Int Epoch -Int 2
 andBool Epoch3 ==Int Epoch -Int 3
 // invariant
 andBool iff(PrevEpoch3JustifiedBlock ==K true, isJustifiable(Epoch3, Epoch3BoundaryBlock, PrevAttestations3, Vs))
 andBool iff(PrevEpoch2JustifiedBlock ==K true, isJustifiable(Epoch2, Epoch2BoundaryBlock, PrevAttestations2, Vs))
 andBool implies(PrevLastJustifiedEpoch  <Int Epoch3, PrevEpoch3JustifiedBlock ==K false andBool PrevEpoch2JustifiedBlock ==K false)
 andBool implies(PrevLastJustifiedEpoch ==Int Epoch3, PrevEpoch3JustifiedBlock ==K true  andBool PrevEpoch2JustifiedBlock ==K false)
 andBool implies(PrevLastJustifiedEpoch ==Int Epoch2,                                            PrevEpoch2JustifiedBlock ==K true )
 andBool         PrevLastJustifiedEpoch <=Int Epoch2
 //
 andBool Epoch2JustifiedBlock ==K PrevEpoch2JustifiedBlock
 andBool LastJustifiedEpoch ==Int PrevLastJustifiedEpoch
 andBool Attestations2 ==K super(PrevAttestations2)
 // ranges
 andBool Epoch >=Int 0
 andBool Epoch1 >=Int 0
 andBool Epoch2 >=Int 0
 andBool Epoch3 >=Int 0
 andBool PrevLastJustifiedEpoch >=Int 0
 ensures ?NewLastJustifiedEpoch >=Int 0
//
// ensures
//
// justification of e-2 and e-1
andBool iff(?NewEpoch2JustifiedBlock ==K true, isJustifiable(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs))
andBool iff(?NewEpoch1JustifiedBlock ==K true, isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, Vs))
// last justified epoch
andBool implies(?NewLastJustifiedEpoch  <Int Epoch2, ?NewEpoch2JustifiedBlock ==K false andBool ?NewEpoch1JustifiedBlock ==K false)
andBool implies(?NewLastJustifiedEpoch ==Int Epoch2, ?NewEpoch2JustifiedBlock ==K true  andBool ?NewEpoch1JustifiedBlock ==K false)
andBool implies(?NewLastJustifiedEpoch ==Int Epoch1,                                            ?NewEpoch1JustifiedBlock ==K true )
andBool         ?NewLastJustifiedEpoch <=Int Epoch1

endmodule
