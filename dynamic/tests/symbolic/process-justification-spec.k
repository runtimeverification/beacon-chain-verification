require "../../verification.k"

module PROCESS-JUSTIFICATION-SPEC

imports VERIFICATION

// for the given current epoch 1,
// processJustification(-1) followed by processJustification(0)
// update the <justified> entries properly according to the justifiability of epoch 0.
rule
<T>
  <k> processJustification(-1)
   ~> processJustification(0) => . </k>
  <currentSlot> firstSlotOf(1) </currentSlot>
  <states>
    <state>
      <slot> firstSlotOf(0) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, GenesisBlock) </lastBlock>
      <lastJustified> 0 </lastJustified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(1) </slot>
      <validators> Vs </validators>
      <attested>
        0 |-> Attestations:Attestations
        ...
      </attested>
      <justified>
        0 |-> true
        ...
      </justified>
      <lastJustified> 0 </lastJustified>
      ...
    </state>
    ...
  </states>
  ...
</T>

// for the given current epoch 2,
// processJustification(0) followed by processJustification(1)
// update the <justified> entries properly according to the justifiability of epoch 0 and epoch 1.
rule
<T>
  <k> processJustification(0)
   ~> processJustification(1) => . </k>
  <currentSlot> firstSlotOf(2) </currentSlot>
  <states>
    <state>
      <slot> firstSlotOf(0) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, GenesisBlock) </lastBlock>
      <lastJustified> 0 </lastJustified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(1) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, EpochBoundaryBlock1) </lastBlock>
      <attested>
        0 |-> PrevAttestations0:Attestations
        ...
      </attested>
      <justified>
        0 |-> true
        ...
      </justified>
      <lastJustified> 0 </lastJustified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(2) </slot>
      <validators> Vs </validators>
      <attested>
        0 |-> Attestations0:Attestations
        1 |-> Attestations1:Attestations
        ...
      </attested>
      <justified>
        0 |-> (true  => ?NewEpochJustified0:Bool)
        1 |-> (false => ?NewEpochJustified1:Bool)
        ...
      </justified>
      <lastJustified> 0 => ?NewLastJustifiedEpoch </lastJustified>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
 andBool isJustifiable(0, GenesisBlock, PrevAttestations0, Vs) // because the genesis block is justified by default
 andBool Attestations0 ==K super(PrevAttestations0)
 ensures isGoodState(0, GenesisBlock,        Attestations0, Vs, ?NewEpochJustified0,
                     1, EpochBoundaryBlock1, Attestations1, Vs, ?NewEpochJustified1,
                     ?NewLastJustifiedEpoch)
 andBool ?NewEpochJustified0 ==K true
 andBool ?NewLastJustifiedEpoch >=Int 0

/*
For the given current epoch e >= 3,
processJustification(e - 2) followed by processJustification(e - 1)
update the <justified> entries properly according to the justifiability of e - 2 and e - 1.

More formally,
if the pre-state satisfies:
    isGoodState(Epoch3, Epoch3BoundaryBlock, PrevAttestations3, Vs, PrevEpoch3JustifiedBlock,
                        Epoch2, Epoch2BoundaryBlock, PrevAttestations2, Vs, PrevEpoch2JustifiedBlock,
                        PrevLastJustifiedEpoch, PrevLastJustifiedBlock),
then the post-state of `processJustification(e - 2) followed by processJustification(e - 1)` satisfies:
    isGoodState(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs, ?NewEpoch2JustifiedBlock,
                        Epoch1, Epoch1BoundaryBlock, Attestations1, Vs, ?NewEpoch1JustifiedBlock,
                        ?NewLastJustifiedEpoch, ?NewLastJustifiedBlock))
where Epoch3 = e - 3
      Epoch2 = e - 2
      Epoch1 = e - 1
*/
rule
<T>
  <k> case(xor2(
        PrevLastJustifiedEpoch  <Int Epoch2
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
        Epoch3 |-> PrevEpoch3Justified:Bool
        Epoch2 |-> PrevEpoch2Justified:Bool
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
        Epoch2 |-> (Epoch2Justified:Bool => ?NewEpoch2Justified:Bool)
        Epoch1 |-> (false                => ?NewEpoch1Justified:Bool)
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
 //
 // invariant
 //
 andBool isGoodState(Epoch3, Epoch3BoundaryBlock, PrevAttestations3, Vs, PrevEpoch3Justified,
                     Epoch2, Epoch2BoundaryBlock, PrevAttestations2, Vs, PrevEpoch2Justified,
                     PrevLastJustifiedEpoch)
 //
 andBool Epoch2Justified ==K PrevEpoch2Justified
 andBool LastJustifiedEpoch ==Int PrevLastJustifiedEpoch
 andBool Attestations2 ==K super(PrevAttestations2)
 //
 // ranges
 //
 andBool Epoch >=Int 0
 andBool Epoch1 >=Int 0
 andBool Epoch2 >=Int 0
 andBool Epoch3 >=Int 0
 andBool PrevLastJustifiedEpoch >=Int 0
 ensures ?NewLastJustifiedEpoch >=Int 0
 //
 // ensures
 //
 andBool isGoodState(Epoch2, Epoch2BoundaryBlock, Attestations2, Vs, ?NewEpoch2Justified,
                     Epoch1, Epoch1BoundaryBlock, Attestations1, Vs, ?NewEpoch1Justified,
                     ?NewLastJustifiedEpoch)
 andBool implies(Epoch2Justified, ?NewEpoch2Justified)
 andBool LastJustifiedEpoch <=Int ?NewLastJustifiedEpoch

endmodule
