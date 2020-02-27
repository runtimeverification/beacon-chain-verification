require "../../verification.k"

module J-SPEC

imports VERIFICATION

rule
<T>
  <k> // source of e - 2
      case(xor5(
                Epoch2LastJustifiedEpoch <Int Epoch4
        andBool Epoch4Justified ==K false
      ,
                Epoch2LastJustifiedEpoch ==Int Epoch4
        andBool Epoch4Justified ==K true
        //
        andBool Epoch3Justified ==K true
        andBool Epoch2Justified ==K true
      ,
                Epoch2LastJustifiedEpoch ==Int Epoch4
        andBool Epoch4Justified ==K true
        //
        andBool (
                    Epoch3Justified ==K false
             orBool Epoch2Justified ==K false
        )
      ,
                Epoch2LastJustifiedEpoch ==Int Epoch3
        andBool Epoch3Justified ==K true
        //
        andBool Epoch2Justified ==K true
      ,
                Epoch2LastJustifiedEpoch ==Int Epoch3
        andBool Epoch3Justified ==K true
        //
        andBool Epoch2Justified ==K false
      ))
   // source of e - 1
   ~> case(xor5(
                Epoch1LastJustifiedEpoch <Int Epoch3
        andBool Epoch3Justified ==K false
      ,
                Epoch1LastJustifiedEpoch ==Int Epoch3
        andBool Epoch3Justified ==K true
        //
        andBool Epoch2Justified ==K true
        andBool Epoch1Justified ==K true
      ,
                Epoch1LastJustifiedEpoch ==Int Epoch3
        andBool Epoch3Justified ==K true
        //
        andBool (
                    Epoch2Justified ==K false
             orBool Epoch1Justified ==K false
        )
      ,
                Epoch1LastJustifiedEpoch ==Int Epoch2
        andBool Epoch2Justified ==K true
        //
        andBool Epoch1Justified ==K true
      ,
                Epoch1LastJustifiedEpoch ==Int Epoch2
        andBool Epoch2Justified ==K true
        //
        andBool Epoch1Justified ==K false
      ))
   // previous last finalized epoch
   ~> case(xor3(
                LastFinalizedEpoch <Int Epoch4
        andBool Epoch4Finalized ==K false
        andBool Epoch3Finalized ==K false
      ,
                LastFinalizedEpoch ==Int Epoch4
        andBool Epoch4Finalized ==K true
        andBool Epoch3Finalized ==K false
      ,
                LastFinalizedEpoch ==Int Epoch3
        andBool Epoch3Finalized ==K true
        andBool Epoch2LastJustifiedEpoch ==Int Epoch3 // TODO: make it invariant
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
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch2) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, Epoch2BoundaryBlock) </lastBlock>
      <lastJustified> Epoch2LastJustifiedEpoch </lastJustified>
      <justified>
        Epoch4 |-> Epoch4Justified:Bool
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
// invariant
andBool Epoch2LastJustifiedEpoch <Int Epoch2
andBool Epoch1LastJustifiedEpoch <Int Epoch1
// ranges
andBool Epoch >=Int 0
andBool Epoch1 >=Int 0
andBool Epoch2 >=Int 0
andBool Epoch3 >=Int 0
andBool Epoch4 >=Int 0
andBool Epoch1LastJustifiedEpoch >=Int 0
andBool Epoch2LastJustifiedEpoch >=Int 0
andBool LastFinalizedEpoch >=Int 0
ensures ?NewLastFinalizedEpoch >=Int 0
// invariant

andBool ( notBool Epoch4Finalized orBool ?NewEpoch4Finalized )
andBool ( notBool Epoch3Finalized orBool ?NewEpoch3Finalized )

// last finalized epoch
andBool bool(xor4(
                    ?NewLastFinalizedEpoch <Int Epoch4
            andBool ?NewEpoch4Finalized ==K false
            andBool ?NewEpoch3Finalized ==K false
            andBool ?NewEpoch2Finalized ==K false
          ,
                    ?NewLastFinalizedEpoch ==Int Epoch4
            andBool ?NewEpoch4Finalized ==K true
            andBool ?NewEpoch3Finalized ==K false
            andBool ?NewEpoch2Finalized ==K false
          ,
                    ?NewLastFinalizedEpoch ==Int Epoch3
            andBool ?NewEpoch3Finalized ==K true
            andBool ?NewEpoch2Finalized ==K false
          ,
                    ?NewLastFinalizedEpoch ==Int Epoch2
            andBool ?NewEpoch2Finalized ==K true
        ))

// e-2 finalized or not
andBool bool(xor2(
                    ?NewEpoch2Finalized ==K true
            andBool Epoch1LastJustifiedEpoch ==Int Epoch2
            andBool Epoch1Justified ==K true
        ,
                    ?NewEpoch2Finalized ==K false
            andBool (
                    Epoch1LastJustifiedEpoch <Int Epoch2
             orBool Epoch1Justified ==K false
            )
        ))

// e-3 finalized or not
andBool bool(xor6(
                    ?NewEpoch3Finalized ==K true andBool Epoch3Finalized ==K true
        ,
                    ?NewEpoch3Finalized ==K true andBool Epoch3Finalized ==K false
            andBool Epoch1LastJustifiedEpoch ==Int Epoch3
            andBool Epoch2Justified ==K true
            andBool Epoch1Justified ==K true
        ,
                    ?NewEpoch3Finalized ==K true andBool Epoch3Finalized ==K false
            andBool Epoch2LastJustifiedEpoch ==Int Epoch3
            andBool Epoch2Justified ==K true
        ,
                    ?NewEpoch3Finalized ==K false andBool Epoch3Finalized ==K false
            andBool Epoch1LastJustifiedEpoch =/=Int Epoch3
            andBool Epoch2LastJustifiedEpoch <Int Epoch3
        ,
                    ?NewEpoch3Finalized ==K false andBool Epoch3Finalized ==K false
            andBool Epoch1LastJustifiedEpoch ==Int Epoch3
            andBool (
                    Epoch2Justified ==K false
             orBool Epoch1Justified ==K false
            )
        ,
                    ?NewEpoch3Finalized ==K false andBool Epoch3Finalized ==K false
            andBool Epoch2LastJustifiedEpoch ==Int Epoch3
            andBool Epoch2Justified ==K false
        ))

// e-4 finalized or not
andBool bool(xor3(
                    ?NewEpoch4Finalized ==K true andBool Epoch4Finalized ==K true
        ,
                    ?NewEpoch4Finalized ==K true andBool Epoch4Finalized ==K false
            andBool Epoch2LastJustifiedEpoch ==Int Epoch4
            andBool Epoch3Justified ==K true
            andBool Epoch2Justified ==K true
        ,
                    ?NewEpoch4Finalized ==K false andBool Epoch4Finalized ==K false
            andBool (
                    Epoch2LastJustifiedEpoch =/=Int Epoch4
             orBool Epoch3Justified ==K false
             orBool Epoch2Justified ==K false
            )
        ))

endmodule
