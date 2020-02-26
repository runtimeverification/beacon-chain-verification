require "../../verification.k"

module PROCESS-FINALIZATION-SPEC

imports VERIFICATION

rule
<T>
  <k> case(xor2(
    //  Epoch2LastJustifiedEpoch <Int Epoch4
    //,
                Epoch1LastJustifiedEpoch ==Int Epoch2
        andBool Epoch1LastJustifiedBlock ==Int Epoch2BoundaryBlock
        andBool Epoch1JustifiedBlock ==K some Epoch1BoundaryBlock
        andBool Epoch2JustifiedBlock ==K some Epoch2BoundaryBlock
      ,
                Epoch1LastJustifiedEpoch ==Int Epoch3
        andBool Epoch1LastJustifiedBlock ==Int Epoch3BoundaryBlock
        andBool Epoch1JustifiedBlock ==K some Epoch1BoundaryBlock
        andBool Epoch2JustifiedBlock ==K some Epoch2BoundaryBlock
        andBool Epoch3JustifiedBlock ==K some Epoch3BoundaryBlock
        andBool Epoch3FinalizedBlock ==K none
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
      <lastJustified>
        (Epoch2LastJustifiedEpoch, Epoch2LastJustifiedBlock)
      </lastJustified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch1) </slot>
      <validators> Vs </validators>
      <lastBlock> (_, Epoch1BoundaryBlock) </lastBlock>
      <lastJustified>
        (Epoch1LastJustifiedEpoch, Epoch1LastJustifiedBlock)
      </lastJustified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch) </slot>
      <validators> Vs </validators>
      <justified>
        Epoch4 |-> Epoch4JustifiedBlock:Option
        Epoch3 |-> Epoch3JustifiedBlock:Option
        Epoch2 |-> Epoch2JustifiedBlock:Option
        Epoch1 |-> Epoch1JustifiedBlock:Option
        ...
      </justified>
      <finalized>
        Epoch4 |-> Epoch4FinalizedBlock:Option
        Epoch3 |-> (Epoch3FinalizedBlock:Option => ?NewEpoch3FinalizedBlock:Option)
        Epoch2 |-> (none                        => ?NewEpoch2FinalizedBlock:Option)
        Epoch1 |-> none
        ...
      </finalized>
      <lastFinalized>
        (LastFinalizedEpoch, LastFinalizedBlock)
      =>
        (?NewLastFinalizedEpoch, ?NewLastFinalizedBlock)
      </lastFinalized>
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

andBool Epoch >=Int 4


ensures ?NewLastFinalizedEpoch >=Int 0
// invariant

andBool bool(xor2(
                    Epoch1LastJustifiedEpoch ==Int Epoch2
            andBool Epoch1LastJustifiedBlock ==Int Epoch2BoundaryBlock
            andBool Epoch1JustifiedBlock ==K some Epoch1BoundaryBlock
            andBool Epoch2JustifiedBlock ==K some Epoch2BoundaryBlock
            //
            andBool ?NewEpoch3FinalizedBlock ==K Epoch3FinalizedBlock
            andBool ?NewEpoch2FinalizedBlock ==K some Epoch2BoundaryBlock
            andBool ?NewLastFinalizedEpoch ==Int Epoch2
            andBool ?NewLastFinalizedBlock ==Int Epoch2BoundaryBlock
          ,
                    Epoch1LastJustifiedEpoch ==Int Epoch3
            andBool Epoch1LastJustifiedBlock ==Int Epoch3BoundaryBlock
            andBool Epoch1JustifiedBlock ==K some Epoch1BoundaryBlock
            andBool Epoch2JustifiedBlock ==K some Epoch2BoundaryBlock
            andBool Epoch3JustifiedBlock ==K some Epoch3BoundaryBlock
            //
            andBool ?NewEpoch3FinalizedBlock ==K some Epoch3BoundaryBlock
            andBool ?NewEpoch2FinalizedBlock ==K none
            andBool ?NewLastFinalizedEpoch ==Int Epoch3
            andBool ?NewLastFinalizedBlock ==Int Epoch3BoundaryBlock
        ))

/*
andBool bool(xor5(
                    Epoch2LastJustifiedEpoch <Int Epoch4
            andBool ?NewEpoch4FinalizedBlock ==K Epoch4FinalizedBlock
            andBool ?NewEpoch3FinalizedBlock ==K Epoch3FinalizedBlock
            andBool ?NewEpoch2FinalizedBlock ==K Epoch2FinalizedBlock
            andBool ?NewLastFinalizedEpoch ==Int LastFinalizedEpoch
            andBool ?NewLastFinalizedBlock ==Int LastFinalizedBlock
        ,
                    Epoch2LastJustifiedEpoch ==Int Epoch4
            andBool Epoch2JustifiedBlock ==K some Epoch2BoundaryBlock
            andBool Epoch3JustifiedBlock ==K some Epoch3BoundaryBlock
         // andBool Epoch4JustifiedBlock ==K some Epoch4BoundaryBlock // TODO: needed?
            andBool ?NewEpoch4FinalizedBlock ==K some Epoch4BoundaryBlock
            andBool ?NewEpoch3FinalizedBlock ==K Epoch3FinalizedBlock
            andBool ?NewEpoch2FinalizedBlock ==K Epoch2FinalizedBlock
        ,
                    Epoch2LastJustifiedEpoch ==Int Epoch4
            andBool (
                        Epoch2JustifiedBlock ==K none
                 orBool Epoch3JustifiedBlock ==K none
            )
            andBool ?NewEpoch4FinalizedBlock ==K none
            andBool ?NewEpoch3FinalizedBlock ==K Epoch3FinalizedBlock
            andBool ?NewEpoch2FinalizedBlock ==K Epoch2FinalizedBlock
        ,
                    Epoch2LastJustifiedEpoch ==Int Epoch3
            andBool Epoch2JustifiedBlock ==K some Epoch2BoundaryBlock
            andBool ?NewEpoch4FinalizedBlock ==K Epoch4FinalizedBlock
            andBool ?NewEpoch3FinalizedBlock ==K some Epoch3BoundaryBlock
            andBool ?NewEpoch2FinalizedBlock ==K Epoch2FinalizedBlock
        ,
                    Epoch2LastJustifiedEpoch ==Int Epoch3
            andBool Epoch2JustifiedBlock ==K none
            andBool ?NewEpoch4FinalizedBlock ==K Epoch4FinalizedBlock
            andBool ?NewEpoch3FinalizedBlock ==K none
            andBool ?NewEpoch2FinalizedBlock ==K Epoch2FinalizedBlock
        ))
*/



/*

1. e-1 -> e-2
2. e-1 -> e-3
3. e-1 -> e-4+

a. e-2 -> e-3
b. e-2 -> e-4
c. e-2 -> e-5+


1a. (e-2 already justified, thus e-3 already finalized)
- e-1 j <=> e-2 f
- e-3 f
- e-4 stay

1b. (e-2 already justified)
- e-1 j <=> e-2 f
- e-3 j <=> e-4 f
- e-3 nf

1c. (e-2 already justified)
- e-1 j <=> e-2 f
- e-3 nf
- e-4 nf

2a. (e-1 doesn't affect)
- e-2 j <=> e-3 f
- e-2 nf
- e-4 stay

2b. (e-3 already justified)
- e-2 j <=> e-4 f
- e-1 j and e-2 j <=> e-3 f
- e-2 nf

2c.
- e-1 j and e-2 j <=> e-3 f
- e-2 nf
- e-4 nf

3a. impossible

3b. (e-3 cannot be justified)
- nothing finalized

3c.
- nothing finalized



e-1 -> e-2
- e-2 1-f: iff e-1 j
- e-3 2-f: false

e-1 -> e-3
- e-2 1-f: false
- e-3 2-f: iff e-1 j and e-2 j

e-1 -> e-4+
- e-2 1-f: false
- e-3 2-f: false


e-2 -> e-3
- e-3 1-f: iff e-2 j
- e-4 2-f: false

e-2 -> e-4
- e-3 1-f: false
- e-4 2-f: iff e-2 j and e-3 j

e-2 -> e-5+
- e-3 1-f: false
- e-4 2-f: false



e-2 f: iff e-2 1-f
e-3 f: iff e-3 1-f or e-3 2-f
e-4 f: iff e-4 2-f








andBool bool(xor(
                    Epoch1LastJustifiedEpoch ==Int Epoch2
            andBool ?NewEpoch2FinalizedBlock ==K some Epoch2BoundaryBlock
            andBool ?NewEpoch1JustifiedBlock ==K some Epoch1BoundaryBlock
        ,
                    Epoch1LastJustifiedEpoch ==Int Epoch2
            andBool ?NewEpoch2FinalizedBlock ==K none
            andBool ?NewEpoch1JustifiedBlock ==K none
        ))
andBool bool(xor(
                    Epoch1LastJustifiedEpoch ==Int Epoch3
            andBool ?NewEpoch3FinalizedBlock ==K some Epoch3BoundaryBlock
            andBool ?NewEpoch2JustifiedBlock ==K some Epoch2BoundaryBlock
            andBool ?NewEpoch1JustifiedBlock ==K some Epoch1BoundaryBlock
        ,
                    Epoch1LastJustifiedEpoch ==Int Epoch3
            andBool ?NewEpoch3FinalizedBlock ==K none
            andBool ?NewEpoch2JustifiedBlock ==K some Epoch2BoundaryBlock
            andBool ?NewEpoch1JustifiedBlock ==K none
        ,
                    Epoch1LastJustifiedEpoch ==Int Epoch3
            andBool ?NewEpoch3FinalizedBlock ==K none
            andBool ?NewEpoch2JustifiedBlock ==K none
            andBool ?NewEpoch1JustifiedBlock ==K some Epoch1BoundaryBlock
        ,
                    Epoch1LastJustifiedEpoch ==Int Epoch3
            andBool ?NewEpoch3FinalizedBlock ==K none
            andBool ?NewEpoch2JustifiedBlock ==K none
            andBool ?NewEpoch1JustifiedBlock ==K none
        ))

andBool bool(xor(
                    Epoch2LastJustifiedEpoch ==Int Epoch3
            andBool ?NewEpoch3FinalizedBlock ==K some Epoch3BoundaryBlock
            andBool ?NewEpoch2JustifiedBlock ==K some Epoch2BoundaryBlock
        ,
                    Epoch2LastJustifiedEpoch ==Int Epoch3
            andBool ?NewEpoch3FinalizedBlock ==K none
            andBool ?NewEpoch2JustifiedBlock ==K none
        ))
andBool bool(xor(
                    Epoch2LastJustifiedEpoch ==Int Epoch4
            andBool ?NewEpoch4FinalizedBlock ==K some Epoch4BoundaryBlock
            andBool     Epoch3JustifiedBlock ==K some Epoch3BoundaryBlock
            andBool ?NewEpoch2JustifiedBlock ==K some Epoch2BoundaryBlock
        ,
                    Epoch2LastJustifiedEpoch ==Int Epoch4
            andBool ?NewEpoch4FinalizedBlock ==K none
            andBool     Epoch3JustifiedBlock ==K some Epoch3BoundaryBlock
            andBool ?NewEpoch2JustifiedBlock ==K none
        ,
                    Epoch2LastJustifiedEpoch ==Int Epoch4
            andBool ?NewEpoch4FinalizedBlock ==K none
            andBool     Epoch3JustifiedBlock ==K none
            andBool ?NewEpoch2JustifiedBlock ==K some Epoch2BoundaryBlock
        ,
                    Epoch2LastJustifiedEpoch ==Int Epoch4
            andBool ?NewEpoch4FinalizedBlock ==K none
            andBool     Epoch3JustifiedBlock ==K none
            andBool ?NewEpoch2JustifiedBlock ==K none
        ))



andBool bool(xor(
                    ?NewEpoch2FinalizedBlock ==K some Epoch2BoundaryBlock
            andBool Epoch1LastJustifiedEpoch ==Int Epoch2
            andBool ?NewEpoch1JustifiedBlock == some Epoch1BoundaryBlock
        ,
                    ?NewEpoch2FinalizedBlock ==K none
            andBool Epoch1LastJustifiedEpoch ==Int Epoch2
            andBool ?NewEpoch1JustifiedBlock == none
        ,
                    ?NewEpoch2FinalizedBlock ==K none
            andBool Epoch1LastJustifiedEpoch <Int Epoch2
        ))
andBool bool(xor(
                    ?NewEpoch3FinalizedBlock ==K some Epoch3BoundaryBlock
            andBool Epoch2LastJustifiedEpoch ==Int Epoch3
            andBool ?NewEpoch2JustifiedBlock == some Epoch2BoundaryBlock
        ,
                    ?NewEpoch3FinalizedBlock ==K some Epoch3BoundaryBlock
            andBool Epoch1LastJustifiedEpoch ==Int Epoch3
            andBool ?NewEpoch2JustifiedBlock == some Epoch2BoundaryBlock
            andBool ?NewEpoch1JustifiedBlock == some Epoch1BoundaryBlock
        ,
                    ?NewEpoch4FinalizedBlock ==K none
            andBool notBool (
                andBool Epoch2LastJustifiedEpoch ==Int Epoch4
                andBool Epoch3JustifiedBlock == some Epoch3BoundaryBlock
                andBool ?NewEpoch2JustifiedBlock == some Epoch2BoundaryBlock
            )
        ))
andBool bool(xor(
                    ?NewEpoch4FinalizedBlock ==K some Epoch4BoundaryBlock
            andBool Epoch2LastJustifiedEpoch ==Int Epoch4
            andBool Epoch3JustifiedBlock == some Epoch3BoundaryBlock
            andBool ?NewEpoch2JustifiedBlock == some Epoch2BoundaryBlock
        ,
                    ?NewEpoch4FinalizedBlock ==K none
            andBool notBool (
                andBool Epoch2LastJustifiedEpoch ==Int Epoch4
                andBool Epoch3JustifiedBlock == some Epoch3BoundaryBlock
                andBool ?NewEpoch2JustifiedBlock == some Epoch2BoundaryBlock
            )
        ))


                    ?NewLastJustifiedEpoch ==Int Epoch3

            andBool isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs)
            andBool isJustifiable(Epoch1BoundaryBlock, Attestations1, Vs)
            andBool Epoch1LastJustifiedEpoch ==Int Epoch3

            andBool isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs)
            andBool Epoch2LastJustifiedEpoch ==Int Epoch3

        ,
                    ?NewLastJustifiedEpoch ==Int Epoch4
            andBool Epoch3JustifiedBlock == some Epoch3BoundaryBlock
            andBool isJustifiable(Epoch2BoundaryBlock, Attestations2, Vs)
            andBool Epoch2LastJustifiedEpoch ==Int Epoch4
        )
*/

endmodule
