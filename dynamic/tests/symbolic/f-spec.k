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
requires true
 andBool Epoch1 ==Int Epoch -Int 1
 andBool Epoch2 ==Int Epoch -Int 2
 // invariant
 andBool LastJustifiedEpoch <=Int Epoch2
 andBool implies(LastJustifiedEpoch  <Int Epoch2, OldEpoch2JustifiedBlock ==K false)
 andBool implies(LastJustifiedEpoch ==Int Epoch2, OldEpoch2JustifiedBlock ==K true)
 andBool implies(OldEpoch2JustifiedBlock ==K true, isJustifiable(Epoch2, Epoch2BoundaryBlock, PrevAttestations2, Vs))
 // ranges
 andBool Epoch >=Int 0
 andBool Epoch1 >=Int 0
 andBool Epoch2 >=Int 0
 andBool LastJustifiedEpoch >=Int 0
 andBool Attestations2 ==K super(PrevAttestations2)
 ensures ?NewJustifiedEpoch >=Int 0
// ensures
// justification of e - 2
andBool bool(xor2(
            isJustifiable(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs)
    andBool ?NewEpoch2JustifiedBlock ==K true
,
    notBool isJustifiable(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs)
    andBool ?NewEpoch2JustifiedBlock ==K false
))
// justification of e - 1
andBool bool(xor2(
            isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, Vs)
    andBool ?NewEpoch1JustifiedBlock ==K true
,
    notBool isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, Vs)
    andBool ?NewEpoch1JustifiedBlock ==K false
))
// last justified epoch
andBool bool(xor3(
            ?NewEpoch2JustifiedBlock ==K false
    andBool ?NewEpoch1JustifiedBlock ==K false
    andBool ?NewJustifiedEpoch ==Int LastJustifiedEpoch
,
            ?NewEpoch2JustifiedBlock ==K true
    andBool ?NewEpoch1JustifiedBlock ==K false
    andBool ?NewJustifiedEpoch ==Int Epoch2
,
            ?NewEpoch1JustifiedBlock ==K true
    andBool ?NewJustifiedEpoch ==Int Epoch1
))

endmodule
