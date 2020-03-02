require "../../verification.k"

module F2-SPEC

imports VERIFICATION

// processJustification(e - 2) followed by processJustification(e - 1)
// update the <justified> entries properly according to the justifiability of e - 2 and e - 1,
// where e is the current epoch.
rule
<T>
  <k> case(xor2(
        LastJustifiedEpoch  <Int Epoch2
      ,
        LastJustifiedEpoch ==Int Epoch2
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
      <attested>
        Epoch2 |-> PrevAttestations2:Attestations
        ...
      </attested>
      <justified>
        Epoch2 |-> OldEpoch2JustifiedBlock:Bool
        ...
      </justified>
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
        Epoch2 |-> (OldEpoch2JustifiedBlock:Bool => ?NewEpoch2JustifiedBlock:Bool)
        Epoch1 |-> (false                        => ?NewEpoch1JustifiedBlock:Bool)
        ...
      </justified>
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
 // invariant
 andBool LastJustifiedEpoch <=Int Epoch2
 andBool implies(LastJustifiedEpoch  <Int Epoch2, OldEpoch2JustifiedBlock ==K false)
 andBool implies(LastJustifiedEpoch ==Int Epoch2, OldEpoch2JustifiedBlock ==K true)
 andBool implies(OldEpoch2JustifiedBlock ==K true, isJustifiable(Epoch2BoundaryBlock, PrevAttestations2, Vs))
 // ranges
 andBool Epoch >=Int 0
 andBool Epoch1 >=Int 0
 andBool Epoch2 >=Int 0
 andBool LastJustifiedEpoch >=Int 0
 andBool Attestations2 ==K super(PrevAttestations2)
 ensures ?NewJustifiedEpoch >=Int 0
//
// ensures
//
// justification of e-2 and e-1
andBool iff(?NewEpoch2JustifiedBlock ==K true, isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs))
andBool iff(?NewEpoch1JustifiedBlock ==K true, isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs))
// last justified epoch
andBool implies(?NewJustifiedEpoch  <Int Epoch2, ?NewEpoch2JustifiedBlock ==K false andBool ?NewEpoch1JustifiedBlock ==K false)
andBool implies(?NewJustifiedEpoch ==Int Epoch2, ?NewEpoch2JustifiedBlock ==K true  andBool ?NewEpoch1JustifiedBlock ==K false)
andBool implies(?NewJustifiedEpoch ==Int Epoch1,                                            ?NewEpoch1JustifiedBlock ==K true )
andBool         ?NewJustifiedEpoch <=Int Epoch1

endmodule
