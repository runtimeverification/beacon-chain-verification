require "../../verification.k"

module I-SPEC

imports VERIFICATION

rule
<T>
  <k> case(xor5(
                Epoch1LastJustifiedEpoch <Int Epoch3
      ,
                Epoch1LastJustifiedEpoch ==Int Epoch3
        andBool Epoch3Justified ==K true
        andBool Epoch2Justified ==K true
        andBool Epoch1Justified ==K true
      ,
                Epoch1LastJustifiedEpoch ==Int Epoch3
        andBool Epoch3Justified ==K true
        andBool (
                    Epoch2Justified ==K false
             orBool Epoch1Justified ==K false
        )
      ,
                Epoch1LastJustifiedEpoch ==Int Epoch2
        andBool Epoch2Justified ==K true
        andBool Epoch1Justified ==K true
      ,
                Epoch1LastJustifiedEpoch ==Int Epoch2
        andBool Epoch2Justified ==K true
        andBool Epoch1Justified ==K false
      ))
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
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch1) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, Epoch1BoundaryBlock) </lastBlock>
      <lastJustified> Epoch1LastJustifiedEpoch </lastJustified>
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
        Epoch4 |-> Epoch4Finalized:Bool
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
andBool Epoch1 ==Int Epoch -Int 1
andBool Epoch2 ==Int Epoch -Int 2
andBool Epoch3 ==Int Epoch -Int 3
andBool Epoch4 ==Int Epoch -Int 4
// invariant
andBool Epoch1LastJustifiedEpoch <Int Epoch1
andBool Epoch2LastJustifiedEpoch <Int Epoch2
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
andBool bool(xor5(
                    Epoch1LastJustifiedEpoch <Int Epoch3
            andBool ?NewEpoch3Finalized ==K Epoch3Finalized
            andBool ?NewEpoch2Finalized ==K false
            andBool ?NewLastFinalizedEpoch ==Int LastFinalizedEpoch
          ,
                    Epoch1LastJustifiedEpoch ==Int Epoch3
            andBool Epoch3Justified ==K true
            andBool Epoch2Justified ==K true
            andBool Epoch1Justified ==K true
            //
            andBool ?NewEpoch3Finalized ==K true
            andBool ?NewEpoch2Finalized ==K false
            andBool ?NewLastFinalizedEpoch ==Int Epoch3
          ,
                    Epoch1LastJustifiedEpoch ==Int Epoch3
            andBool Epoch3Justified ==K true
            andBool (
                        Epoch2Justified ==K false
                 orBool Epoch1Justified ==K false
            )
            //
            andBool ?NewEpoch3Finalized ==K Epoch3Finalized
            andBool ?NewEpoch2Finalized ==K false
            andBool ?NewLastFinalizedEpoch ==Int LastFinalizedEpoch
          ,
                    Epoch1LastJustifiedEpoch ==Int Epoch2
            andBool Epoch2Justified ==K true
            andBool Epoch1Justified ==K true
            //
            andBool ?NewEpoch3Finalized ==K Epoch3Finalized
            andBool ?NewEpoch2Finalized ==K true
            andBool ?NewLastFinalizedEpoch ==Int Epoch2
          ,
                    Epoch1LastJustifiedEpoch ==Int Epoch2
            andBool Epoch2Justified ==K true
            andBool Epoch1Justified ==K false
            //
            andBool ?NewEpoch3Finalized ==K Epoch3Finalized
            andBool ?NewEpoch2Finalized ==K false
            andBool ?NewLastFinalizedEpoch ==Int LastFinalizedEpoch
        ))

rule
<T>
  <k> case(xor5(
                Epoch2LastJustifiedEpoch <Int Epoch4
      ,
                Epoch2LastJustifiedEpoch ==Int Epoch4
        andBool Epoch4Justified ==K true
        andBool Epoch3Justified ==K true
        andBool Epoch2Justified ==K true
      ,
                Epoch2LastJustifiedEpoch ==Int Epoch4
        andBool Epoch4Justified ==K true
        andBool (
                    Epoch3Justified ==K false
             orBool Epoch2Justified ==K false
        )
      ,
                Epoch2LastJustifiedEpoch ==Int Epoch3
        andBool Epoch3Justified ==K true
        andBool Epoch2Justified ==K true
      ,
                Epoch2LastJustifiedEpoch ==Int Epoch3
        andBool Epoch3Justified ==K true
        andBool Epoch2Justified ==K false
      ))
   ~> processFinalization(Epoch2) => . </k>
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
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch1) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, Epoch1BoundaryBlock) </lastBlock>
      <lastJustified> Epoch1LastJustifiedEpoch </lastJustified>
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
        Epoch2 |-> false
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
andBool Epoch1 ==Int Epoch -Int 1
andBool Epoch2 ==Int Epoch -Int 2
andBool Epoch3 ==Int Epoch -Int 3
andBool Epoch4 ==Int Epoch -Int 4
// invariant
andBool Epoch1LastJustifiedEpoch <Int Epoch1
andBool Epoch2LastJustifiedEpoch <Int Epoch2
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
andBool bool(xor5(
                    Epoch2LastJustifiedEpoch <Int Epoch4
            andBool ?NewEpoch4Finalized ==K Epoch4Finalized
            andBool ?NewEpoch3Finalized ==K Epoch3Finalized
            andBool ?NewLastFinalizedEpoch ==Int LastFinalizedEpoch
          ,
                    Epoch2LastJustifiedEpoch ==Int Epoch4
            andBool Epoch4Justified ==K true
            andBool Epoch3Justified ==K true
            andBool Epoch2Justified ==K true
            //
            andBool ?NewEpoch4Finalized ==K true
            andBool ?NewEpoch3Finalized ==K Epoch3Finalized
            andBool ?NewLastFinalizedEpoch ==Int Epoch4
          ,
                    Epoch2LastJustifiedEpoch ==Int Epoch4
            andBool Epoch4Justified ==K true
            andBool (
                        Epoch3Justified ==K false
                 orBool Epoch2Justified ==K false
            )
            //
            andBool ?NewEpoch4Finalized ==K Epoch4Finalized
            andBool ?NewEpoch3Finalized ==K Epoch3Finalized
            andBool ?NewLastFinalizedEpoch ==Int LastFinalizedEpoch
          ,
                    Epoch2LastJustifiedEpoch ==Int Epoch3
            andBool Epoch3Justified ==K true
            andBool Epoch2Justified ==K true
            //
            andBool ?NewEpoch4Finalized ==K Epoch4Finalized
            andBool ?NewEpoch3Finalized ==K true
            andBool ?NewLastFinalizedEpoch ==Int Epoch3
          ,
                    Epoch2LastJustifiedEpoch ==Int Epoch3
            andBool Epoch3Justified ==K true
            andBool Epoch2Justified ==K false
            //
            andBool ?NewEpoch4Finalized ==K Epoch4Finalized
            andBool ?NewEpoch3Finalized ==K Epoch3Finalized
            andBool ?NewLastFinalizedEpoch ==Int LastFinalizedEpoch
        ))

endmodule
