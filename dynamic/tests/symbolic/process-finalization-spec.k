require "../../verification.k"

module PROCESS-FINALIZATION-SPEC

imports VERIFICATION

rule
<T>
  <k>
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
        case(xor2(
            Epoch2Justified ==K true
        ,
            Epoch2Justified ==K false
        ))
    ~>
        case(xor2(
            Epoch1Justified ==K true
        ,
            Epoch1Justified ==K false
        ))
   ~> processFinalization(Epoch2)
   ~> processFinalization(Epoch1) => . </k>
  <currentSlot> firstSlotOf(Epoch) </currentSlot>
  <states>
    <state>
      <slot> firstSlotOf(Epoch4) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, Epoch4BoundaryBlock) </lastBlock>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch3) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, Epoch3BoundaryBlock) </lastBlock>
      <justified>
        Epoch4 |-> Epoch4JustifiedPrev:Bool
        ...
      </justified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch2) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, Epoch2BoundaryBlock) </lastBlock>
      <lastJustified> Epoch2LastJustifiedEpoch </lastJustified>
      <justified>
        Epoch4 |-> Epoch4Justified:Bool
        Epoch3 |-> Epoch3JustifiedPrev:Bool
        ...
      </justified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch1) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, Epoch1BoundaryBlock) </lastBlock>
      <lastJustified> Epoch1LastJustifiedEpoch </lastJustified>
      <justified>
        Epoch4 |-> Epoch4Justified:Bool
        Epoch3 |-> Epoch3Justified:Bool
        Epoch2 |-> Epoch2JustifiedPrev:Bool
        ...
      </justified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch) </slot>
      <validators> Vs </validators>
      <justified>
        Epoch4 |-> Epoch4Justified:Bool
        Epoch3 |-> Epoch3Justified:Bool
        Epoch2 |-> Epoch2Justified:Bool
        Epoch1 |-> Epoch1Justified:Bool
        ...
      </justified>
      <finalized>
        Epoch4 |-> (Epoch4Finalized:Bool => ?NewEpoch4Finalized:Bool)
        Epoch3 |-> (Epoch3Finalized:Bool => ?NewEpoch3Finalized:Bool)
        Epoch2 |-> (false                => ?NewEpoch2Finalized:Bool)
        Epoch1 |-> false
        ...
      </finalized>
      <lastFinalized> LastFinalizedEpoch => ?NewLastFinalizedEpoch </lastFinalized>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
andBool isValidators(Vs)
andBool Epoch4 ==Int Epoch -Int 4
andBool Epoch3 ==Int Epoch -Int 3
andBool Epoch2 ==Int Epoch -Int 2
andBool Epoch1 ==Int Epoch -Int 1
//
// invariant
//
andBool implies(Epoch2LastJustifiedEpoch  <Int Epoch4, Epoch4Justified ==K false andBool Epoch3JustifiedPrev ==K false)
andBool implies(Epoch2LastJustifiedEpoch ==Int Epoch4, Epoch4Justified ==K true  andBool Epoch3JustifiedPrev ==K false)
andBool implies(Epoch2LastJustifiedEpoch ==Int Epoch3,                                   Epoch3JustifiedPrev ==K true)
andBool         Epoch2LastJustifiedEpoch  <Int Epoch2
//
andBool implies(Epoch1LastJustifiedEpoch  <Int Epoch4, Epoch4Justified ==K false andBool Epoch3Justified ==K false andBool Epoch2JustifiedPrev ==K false)
andBool implies(Epoch1LastJustifiedEpoch ==Int Epoch4, Epoch4Justified ==K true  andBool Epoch3Justified ==K false andBool Epoch2JustifiedPrev ==K false)
andBool implies(Epoch1LastJustifiedEpoch ==Int Epoch3,                                   Epoch3Justified ==K true  andBool Epoch2JustifiedPrev ==K false)
andBool implies(Epoch1LastJustifiedEpoch ==Int Epoch2,                                                                     Epoch2JustifiedPrev ==K true)
andBool         Epoch1LastJustifiedEpoch  <Int Epoch1
//
andBool implies(LastFinalizedEpoch  <Int Epoch4, Epoch4Finalized ==K false andBool Epoch3Finalized ==K false)
andBool implies(LastFinalizedEpoch ==Int Epoch4, Epoch4Finalized ==K true  andBool Epoch3Finalized ==K false)
andBool implies(LastFinalizedEpoch ==Int Epoch3,                                   Epoch3Finalized ==K true)
andBool         LastFinalizedEpoch  <Int Epoch2
//
andBool implies(Epoch4JustifiedPrev, Epoch4Justified)
andBool implies(Epoch3JustifiedPrev, Epoch3Justified)
andBool implies(Epoch2JustifiedPrev, Epoch2Justified)
//
andBool implies(Epoch3Finalized, Epoch2LastJustifiedEpoch ==Int Epoch3) // TODO: make it general invariant
//
// ranges
//
andBool Epoch  >=Int 0
andBool Epoch1 >=Int 0
andBool Epoch2 >=Int 0
andBool Epoch3 >=Int 0
andBool Epoch4 >=Int 0
andBool Epoch1LastJustifiedEpoch >=Int 0
andBool Epoch2LastJustifiedEpoch >=Int 0
andBool LastFinalizedEpoch >=Int 0
ensures ?NewLastFinalizedEpoch >=Int 0
//
// ensures
//
// last finalized epoch
andBool implies(?NewLastFinalizedEpoch  <Int Epoch4, ?NewEpoch4Finalized ==K false andBool ?NewEpoch3Finalized ==K false andBool ?NewEpoch2Finalized ==K false)
andBool implies(?NewLastFinalizedEpoch ==Int Epoch4, ?NewEpoch4Finalized ==K true  andBool ?NewEpoch3Finalized ==K false andBool ?NewEpoch2Finalized ==K false)
andBool implies(?NewLastFinalizedEpoch ==Int Epoch3,                                       ?NewEpoch3Finalized ==K true  andBool ?NewEpoch2Finalized ==K false)
andBool implies(?NewLastFinalizedEpoch ==Int Epoch2,                                                                             ?NewEpoch2Finalized ==K true)
andBool         ?NewLastFinalizedEpoch  <Int Epoch1
// e-4 finalized or not
andBool implies(Epoch4Finalized ==K false,
            iff(?NewEpoch4Finalized, Epoch2LastJustifiedEpoch ==Int Epoch4 andBool Epoch2Justified andBool Epoch3Justified andBool Epoch4Justified)
        )
// e-3 finalized or not
andBool implies(Epoch3Finalized ==K false,
            iff(?NewEpoch3Finalized,
                    ( Epoch1LastJustifiedEpoch ==Int Epoch3 andBool Epoch1Justified andBool Epoch2Justified andBool Epoch3Justified )
                orBool
                    ( Epoch2LastJustifiedEpoch ==Int Epoch3 andBool                         Epoch2Justified andBool Epoch3Justified )
            )
        )
// e-2 finalized or not
andBool iff(?NewEpoch2Finalized, Epoch1LastJustifiedEpoch ==Int Epoch2 andBool Epoch1Justified andBool Epoch2Justified)
//
andBool implies(Epoch4Finalized, ?NewEpoch4Finalized)
andBool implies(Epoch3Finalized, ?NewEpoch3Finalized)
andBool LastFinalizedEpoch <=Int ?NewLastFinalizedEpoch

endmodule
