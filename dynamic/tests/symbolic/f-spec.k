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
        andBool OldEpoch2JustifiedBlock ==K false
      ,
                LastJustifiedEpoch ==Int Epoch2
        andBool OldEpoch2JustifiedBlock ==K true
        andBool isJustifiable(Epoch2BoundaryBlock, PrevAttestations2, Vs)
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
 // ranges
 andBool Epoch >=Int 0
 andBool Epoch1 >=Int 0
 andBool Epoch2 >=Int 0
 andBool LastJustifiedEpoch >=Int 0
 andBool Attestations2 ==K super(PrevAttestations2)
ensures ?NewJustifiedEpoch >=Int 0 andBool
(
    (
            (
                        isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs)
                andBool ?NewEpoch2JustifiedBlock ==K true
            ) orBool (
                notBool isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs)
                andBool ?NewEpoch2JustifiedBlock ==K false
            )
    ) orBool (
            (
                        isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs)
                andBool ?NewEpoch1JustifiedBlock ==K true
            ) orBool (
                notBool isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs)
                andBool ?NewEpoch1JustifiedBlock ==K false
            )
    )
) andBool (
    (
                        notBool isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs)
                andBool notBool isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs)
                andBool ?NewJustifiedEpoch ==Int LastJustifiedEpoch
    ) orBool (
                                isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs)
                andBool notBool isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs)
                andBool ?NewJustifiedEpoch ==Int Epoch2
    ) orBool (
                                isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs)
                andBool ?NewJustifiedEpoch ==Int Epoch1
    )
)

endmodule
