```k
require "verification.k"

module PROCESS-JUSTIFICATION-FINALIZATION-SPEC

imports VERIFICATION

rule
<T>
  <k>
```
```{.k .proof}
        case(xor3(
            Epoch2LastJustifiedEpoch  <Int Epoch4
        ,
            Epoch2LastJustifiedEpoch ==Int Epoch4
        ,
            Epoch2LastJustifiedEpoch ==Int Epoch3
        ))
    ~>
        case(xor3(
            Epoch1LastJustifiedEpoch  <Int Epoch3
        ,
            Epoch1LastJustifiedEpoch ==Int Epoch3
        ,
            Epoch1LastJustifiedEpoch ==Int Epoch2
        ))
    ~>
        case(xor2(
            Epoch4Justified ==K true
        ,
            Epoch4Justified ==K false
        ))
    ~>
        case(xor2(
            Epoch3Justified ==K true
        ,
            Epoch3Justified ==K false
        ))
   ~>
```
```k
      processJustification(Epoch2)
   ~> processJustification(Epoch1)
   ~> processFinalization(Epoch2)
   ~> processFinalization(Epoch1) => .K ... </k>
  <currentSlot> Slot /* firstSlotOf(Epoch) */ </currentSlot>
  <states>
    <state>
      <slot> firstSlotOf(Epoch3) </slot>
      <validators> v(m(Epoch3SM, _, Epoch3EBM, _, Epoch3AM, Epoch3EM, _), Epoch3VIDs) </validators>
      <justified>
        ( Epoch3 , _ )
        ( Epoch4 , Epoch3Epoch4Justified:Bool )
        _
      </justified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch2) </slot>
      <validators> v(m(Epoch2SM, _, Epoch2EBM, _, Epoch2AM, Epoch2EM, _), Epoch2VIDs) </validators>
      <justified>
        ( Epoch2 , _ )
        ( Epoch3 , Epoch2Epoch3Justified:Bool )
        ( Epoch4 , Epoch2Epoch4Justified:Bool )
        _
      </justified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch1) </slot>
      <validators> v(m(Epoch1SM, _, Epoch1EBM, _, Epoch1AM, Epoch1EM, _), Epoch1VIDs) </validators>
      <attested>
        Epoch3 |-> Epoch1Attestations3:Attestations
        Epoch2 |-> Epoch1Attestations2:Attestations
        ...
      </attested>
      <justified>
        ( Epoch1 , _ )
        ( Epoch2 , Epoch1Epoch2Justified:Bool )
        ( Epoch3 , Epoch1Epoch3Justified:Bool )
        ( Epoch4 , Epoch1Epoch4Justified:Bool )
        _
      </justified>
      <finalized>
        ( Epoch1 , _ )
        ( Epoch2 , false )
        ( Epoch3 , Epoch1Epoch3Finalized:Bool )
        ( Epoch4 , Epoch1Epoch4Finalized:Bool )
        _
      </finalized>
      ...
    </state>
    <state>
      <slot> Slot /* firstSlotOf(Epoch) */ </slot>
      <validators> v(m(SM, _, EBM, _, AM, EM, _), VIDs) </validators>
      <attested>
        Epoch2 |-> Attestations2:Attestations
        Epoch1 |-> Attestations1:Attestations
        Epoch  |-> .Attestations
        ...
      </attested>
      <justified>
        ( Epoch  , false                                                )
        ( Epoch1 , false                    => ?NewEpoch1Justified:Bool )
        ( Epoch2 , PrevEpoch2Justified:Bool => ?NewEpoch2Justified:Bool )
        ( Epoch3 , Epoch3Justified:Bool                                 )
        ( Epoch4 , Epoch4Justified:Bool                                 )
        _
      </justified>
      <finalized>
        ( Epoch  , false                                                )
        ( Epoch1 , false                                                )
        ( Epoch2 , false                    => ?NewEpoch2Finalized:Bool )
        ( Epoch3 , PrevEpoch3Finalized:Bool => ?NewEpoch3Finalized:Bool )
        ( Epoch4 , PrevEpoch4Finalized:Bool => ?NewEpoch4Finalized:Bool )
        _
      </finalized>
      ...
    </state>
    ...
  </states>
  <lastBlock> EpochBoundaryBlock </lastBlock>
  <lastJustified>
    ( Epoch  ,   PrevLastJustifiedEpoch => ?NewLastJustifiedEpoch )
    ( Epoch1 , Epoch1LastJustifiedEpoch )
    ( Epoch2 , Epoch2LastJustifiedEpoch )
    _
  </lastJustified>
  <lastFinalized>
    ( Epoch  ,   PrevLastFinalizedEpoch => ?NewLastFinalizedEpoch )
    ( Epoch1 , Epoch1LastFinalizedEpoch )
    _
  </lastFinalized>
  ...
</T>
requires true

// types
andBool Slot   >=Int 0
andBool Epoch  >=Int 0
andBool Epoch1 >=Int 0
andBool Epoch2 >=Int 0
andBool Epoch3 >=Int 0
andBool Epoch4 >=Int 0
andBool Epoch1LastJustifiedEpoch >=Int 0
andBool Epoch2LastJustifiedEpoch >=Int 0
andBool Epoch1LastFinalizedEpoch >=Int 0
andBool PrevLastJustifiedEpoch >=Int 0
andBool PrevLastFinalizedEpoch >=Int 0

// let-bindings
andBool Epoch4 ==Int Epoch -Int 4
andBool Epoch3 ==Int Epoch -Int 3
andBool Epoch2 ==Int Epoch -Int 2
andBool Epoch1 ==Int Epoch -Int 1
andBool Epoch  ==Int epochOf(Slot)
andBool ?Epoch4BoundaryBlock ==Int EpochBoundaryBlock[firstSlotOf(Epoch4)]i
andBool ?Epoch3BoundaryBlock ==Int EpochBoundaryBlock[firstSlotOf(Epoch3)]i
andBool ?Epoch2BoundaryBlock ==Int EpochBoundaryBlock[firstSlotOf(Epoch2)]i
andBool ?Epoch1BoundaryBlock ==Int EpochBoundaryBlock[firstSlotOf(Epoch1)]i

// pre-conditions

andBool Slot ==Int firstSlotOf(Epoch)
// process slots increase attestations
andBool subsetA(Epoch1Attestations2, Attestations2)
// process slots preserve justification/finalization
andBool Epoch4Justified ==K Epoch1Epoch4Justified
andBool Epoch3Justified ==K Epoch1Epoch3Justified
andBool PrevEpoch2Justified ==K Epoch1Epoch2Justified
andBool PrevEpoch4Finalized ==K Epoch1Epoch4Finalized
andBool PrevEpoch3Finalized ==K Epoch1Epoch3Finalized
andBool PrevLastJustifiedEpoch ==Int Epoch1LastJustifiedEpoch
andBool PrevLastFinalizedEpoch ==Int Epoch1LastFinalizedEpoch
// justification result propagation
andBool implies(Epoch3Epoch4Justified, Epoch2Epoch4Justified)
andBool implies(Epoch2Epoch3Justified, Epoch1Epoch3Justified)
andBool Epoch1Epoch4Justified ==K Epoch2Epoch4Justified
// state validness of e-1
andBool iff(Epoch1Epoch3Justified, isJustifiable(Epoch3, ?Epoch3BoundaryBlock, Epoch1Attestations3, Epoch3SM, Epoch3EBM, Epoch3AM, Epoch3EM, Epoch3VIDs))
andBool iff(Epoch1Epoch2Justified, isJustifiable(Epoch2, ?Epoch2BoundaryBlock, Epoch1Attestations2, Epoch2SM, Epoch2EBM, Epoch2AM, Epoch2EM, Epoch2VIDs))
andBool iff(Epoch1Epoch3Finalized, Epoch2LastJustifiedEpoch ==Int Epoch3 andBool Epoch1Epoch2Justified andBool Epoch1Epoch3Justified)
andBool isCorrectLastJustifiedEpoch(Epoch1LastJustifiedEpoch, Epoch1, Epoch1Epoch2Justified, Epoch1Epoch3Justified)
andBool isCorrectLastFinalizedEpoch(Epoch1LastFinalizedEpoch, Epoch1, Epoch1Epoch3Finalized, Epoch1Epoch4Finalized)
// state validness of e-2
andBool isCorrectLastJustifiedEpoch(Epoch2LastJustifiedEpoch, Epoch2, Epoch2Epoch3Justified, Epoch2Epoch4Justified)

ensures true

// types
andBool ?NewLastJustifiedEpoch >=Int 0
andBool ?NewLastFinalizedEpoch >=Int 0

// post-conditions

// justification of e-1 and e-2
andBool iff(?NewEpoch2Justified, isJustifiable(Epoch2, ?Epoch2BoundaryBlock, Attestations2, Epoch2SM, Epoch2EBM, Epoch2AM, Epoch2EM, Epoch2VIDs))
andBool iff(?NewEpoch1Justified, isJustifiable(Epoch1, ?Epoch1BoundaryBlock, Attestations1, Epoch1SM, Epoch1EBM, Epoch1AM, Epoch1EM, Epoch1VIDs))
// finalization of e-4
andBool implies(PrevEpoch4Finalized ==K false,
            iff(?NewEpoch4Finalized, Epoch2LastJustifiedEpoch ==Int Epoch4 andBool ?NewEpoch2Justified andBool Epoch3Justified andBool Epoch4Justified)
        )
// finalization of e-3
andBool implies(PrevEpoch3Finalized ==K false,
            iff(?NewEpoch3Finalized,
                    ( Epoch1LastJustifiedEpoch ==Int Epoch3 andBool ?NewEpoch1Justified andBool ?NewEpoch2Justified andBool Epoch3Justified )
                orBool
                    ( Epoch2LastJustifiedEpoch ==Int Epoch3 andBool                             ?NewEpoch2Justified andBool Epoch3Justified )
            )
        )
// finalization of e-2
andBool iff(?NewEpoch2Finalized, Epoch1LastJustifiedEpoch ==Int Epoch2 andBool ?NewEpoch1Justified andBool ?NewEpoch2Justified)
// last justified epoch
andBool isCorrectLastJustifiedEpoch(?NewLastJustifiedEpoch, Epoch, ?NewEpoch1Justified, ?NewEpoch2Justified)
// last finalized epoch
andBool isCorrectLastFinalizedEpoch(?NewLastFinalizedEpoch, Epoch, ?NewEpoch2Finalized, ?NewEpoch3Finalized, ?NewEpoch4Finalized)
// propagation
andBool implies(PrevEpoch2Justified, ?NewEpoch2Justified)
andBool implies(PrevEpoch4Finalized, ?NewEpoch4Finalized)
andBool implies(PrevEpoch3Finalized, ?NewEpoch3Finalized)
andBool PrevLastJustifiedEpoch <=Int ?NewLastJustifiedEpoch
andBool PrevLastFinalizedEpoch <=Int ?NewLastFinalizedEpoch
```
```{.k .lemma}
[trusted]
```

```k
endmodule
```
