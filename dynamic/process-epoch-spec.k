require "verification.k"
// require "process-justification-finalization-spec.k"
// require "process-rewards-penalties-spec.k"
// require "process-validator-updates-spec.k"

module PROCESS-EPOCH-SPEC

imports VERIFICATION

// module PROCESS-JUSTIFICATION-FINALIZATION-SPEC
// module PROCESS-REWARDS-PENALTIES-SPEC
// module PROCESS-VALIDATOR-UPDATES-SPEC

rule
<T>
  <k> processEpoch() => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> firstSlotOf(Epoch4) </slot>
      <validators> v(m(_, _, EBM4, _, _, _, _), VIDs4) </validators>
      <lastBlock> (_, Epoch4BoundaryBlock) </lastBlock>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch3) </slot>
      <validators> v(m(_, _, EBM3, _, _, _, _), VIDs3) </validators>
      <lastBlock> (_, Epoch3BoundaryBlock) </lastBlock>
      <justified>
        Epoch4 |-> Epoch3Epoch4Justified:Bool
        ...
      </justified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch2) </slot>
      <validators> v(m(_, _, EBM2, _, _, _, _), VIDs2) </validators>
      <lastBlock> (_, Epoch2BoundaryBlock) </lastBlock>
      <justified>
        Epoch4 |-> Epoch2Epoch4Justified:Bool
        Epoch3 |-> Epoch2Epoch3Justified:Bool
        ...
      </justified>
      <lastJustified> Epoch2LastJustifiedEpoch </lastJustified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch1) </slot>
      <validators> v(m(_, _, EBM1, _, _, _, _), VIDs1) </validators>
      <lastBlock> (_, Epoch1BoundaryBlock) </lastBlock>
      <attested>
        Epoch3 |-> Epoch1Attestations3:Attestations
        Epoch2 |-> Epoch1Attestations2:Attestations
        ...
      </attested>
      <justified>
        Epoch4 |-> Epoch1Epoch4Justified:Bool
        Epoch3 |-> Epoch1Epoch3Justified:Bool
        Epoch2 |-> Epoch1Epoch2Justified:Bool
        ...
      </justified>
      <finalized>
        Epoch4 |-> Epoch1Epoch4Finalized:Bool
        Epoch3 |-> Epoch1Epoch3Finalized:Bool
        Epoch2 |-> false
        ...
      </finalized>
      <lastJustified> Epoch1LastJustifiedEpoch </lastJustified>
      <lastFinalized> Epoch1LastFinalizedEpoch </lastFinalized>
      ...
    </state>
    <state>
      <slot> /* firstSlotOf(Epoch) */ Slot </slot>
      <validators> v(m(SM, BM1 => ?BM2, EBM, AEM1 => ?AEM2, AM1 => ?AM2, EM1 => ?EM2, WM1 => ?WM2), VIDs) </validators>
      <attested>
        Epoch2 |-> Attestations2:Attestations
        Epoch1 |-> Attestations1:Attestations
        Epoch  |-> (_ => .Attestations)
        ...
      </attested>
      <justified>
        Epoch4 |-> Epoch4Justified:Bool
        Epoch3 |-> Epoch3Justified:Bool
        Epoch2 |-> (PrevEpoch2Justified:Bool => ?NewEpoch2Justified:Bool)
        Epoch1 |-> (false                    => ?NewEpoch1Justified:Bool)
        Epoch  |-> (_ => false)
        ...
      </justified>
      <finalized>
        Epoch4 |-> (PrevEpoch4Finalized:Bool => ?NewEpoch4Finalized:Bool)
        Epoch3 |-> (PrevEpoch3Finalized:Bool => ?NewEpoch3Finalized:Bool)
        Epoch2 |-> (false                    => ?NewEpoch2Finalized:Bool)
        Epoch1 |-> false
        Epoch  |-> (_ => false)
        ...
      </finalized>
      <lastJustified> PrevLastJustifiedEpoch => ?NewLastJustifiedEpoch </lastJustified>
      <lastFinalized> PrevLastFinalizedEpoch => ?NewLastFinalizedEpoch </lastFinalized>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
andBool Epoch4 ==Int Epoch -Int 4
andBool Epoch3 ==Int Epoch -Int 3
andBool Epoch2 ==Int Epoch -Int 2
andBool Epoch1 ==Int Epoch -Int 1

andBool Epoch ==Int epochOf(Slot)
andBool Slot ==Int firstSlotOf(Epoch)

//
// invariant
//
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
andBool iff(Epoch1Epoch3Justified, isJustifiable(Epoch3, Epoch3BoundaryBlock, Epoch1Attestations3, EBM3, VIDs3))
andBool iff(Epoch1Epoch2Justified, isJustifiable(Epoch2, Epoch2BoundaryBlock, Epoch1Attestations2, EBM2, VIDs2))
andBool iff(Epoch1Epoch3Finalized, Epoch2LastJustifiedEpoch ==Int Epoch3 andBool Epoch1Epoch2Justified andBool Epoch1Epoch3Justified)
andBool isCorrectLastJustifiedEpoch(Epoch1LastJustifiedEpoch, Epoch1, Epoch1Epoch2Justified, Epoch1Epoch3Justified)
andBool isCorrectLastFinalizedEpoch(Epoch1LastFinalizedEpoch, Epoch1, Epoch1Epoch3Finalized, Epoch1Epoch4Finalized)
// state validness of e-2
andBool isCorrectLastJustifiedEpoch(Epoch2LastJustifiedEpoch, Epoch2, Epoch2Epoch3Justified, Epoch2Epoch4Justified)
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
andBool Epoch1LastFinalizedEpoch >=Int 0
andBool PrevLastJustifiedEpoch >=Int 0
andBool PrevLastFinalizedEpoch >=Int 0

// types
andBool Slot >=Int 0
// let-bindings
andBool ?SourceAttestations ==K filterNotSlashed(SM, Attestations2)
andBool ?TotalActiveBalance ==Int lift(totalBalance(EBM, activeValidators(VIDs, AM1, EM1, Epoch -Int 2)))
//
andBool ?ChurnLimitA ==Int churnLimit(size(activeValidators(VIDs, AM1, EM1, Epoch)))
andBool ?ChurnLimitB ==Int churnLimit(size(activeValidators(VIDs, AM1, EM1, Epoch -Int 1)))
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs, EM1), delayedActivationExitEpoch(Epoch))
andBool ?ActivationEpoch ==Int delayedActivationExitEpoch(Epoch -Int 1)
// pre-conditions
andBool Epoch >=Int 4
andBool Epoch <Int FAR_FUTURE_EPOCH
andBool forall(x, VIDs, EBM[x]i >=Int 0)
andBool distinct(VIDs)
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).inclusion_delay >=Int 1))
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).proposer in VIDs))
andBool isValidAttestations(Attestations2, VIDs, AM1, EM1, Epoch -Int 2)
//
andBool ?LastExitEpoch +Int size(VIDs) <Int FAR_FUTURE_EPOCH
andBool ?ActivationEpoch <Int FAR_FUTURE_EPOCH
andBool countValidatorsToActivate(VIDs, AM1, ?ActivationEpoch) ==Int 0




ensures true

andBool ?ValidatorsToBeActivated ==K activationQueueUptoChurnLimit(VIDs, AEM1, AM1, EM1, ?NewLastFinalizedEpoch, Epoch -Int 1)
andBool ?FinalityDelay ==Int Epoch -Int 2 -Int ?NewLastFinalizedEpoch

andBool ?FinalityDelay >=Int 0

andBool ?NewLastJustifiedEpoch >=Int 0
andBool ?NewLastFinalizedEpoch >=Int 0

// justification of e-1 and e-2
andBool iff(?NewEpoch2Justified, isJustifiable(Epoch2, Epoch2BoundaryBlock, Attestations2, EBM2, VIDs2))
andBool iff(?NewEpoch1Justified, isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, EBM1, VIDs1))
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


// post-conditions
andBool forall(x, VIDs, ?BM2[x]i <=Int BM1[x]i +Int (4 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)))
andBool forall(x, VIDs, ?BM2[x]i >=Int BM1[x]i -Int (7 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)) -Int getInactivityPenalty(EBM[x]i, ?FinalityDelay))
//
// processValidatorEjections 
andBool forall(x, VIDs, #if isActiveValidator(x, AM1, EM1, Epoch -Int 1) andBool EBM[x]i <=Int EJECTION_BALANCE andBool EM1[x]i ==Int FAR_FUTURE_EPOCH
                        #then ?EM2[x]i >=Int delayedActivationExitEpoch(Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH
                              andBool countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimitA
                        #else ?EM2[x]i ==Int EM1[x]i
                        #fi)
// updateActivationEligibilities
andBool forall(x, VIDs, ?AEM2[x]i ==Int #if isActivationEligible(x, AEM1, EBM) #then Epoch #else AEM1[x]i #fi)
// processValidatorActivation
andBool forall(x, ?ValidatorsToBeActivated, ?AM2[x]i ==Int ?ActivationEpoch)
andBool countValidatorsToActivate(VIDs, ?AM2, ?ActivationEpoch) <=Int ?ChurnLimitB




rule
<T>
  <k> processJustification(Epoch2)
   ~> processJustification(Epoch1)
   ~> processFinalization(Epoch2)
   ~> processFinalization(Epoch1) => .K ... </k>
  <currentSlot> Slot /* firstSlotOf(Epoch) */ </currentSlot>
  <states>
    <state>
      <slot> firstSlotOf(Epoch4) </slot>
      <validators> v(m(_, _, EBM4, _, _, _, _), VIDs4) </validators>
      <lastBlock> (_, Epoch4BoundaryBlock) </lastBlock>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch3) </slot>
      <validators> v(m(_, _, EBM3, _, _, _, _), VIDs3) </validators>
      <lastBlock> (_, Epoch3BoundaryBlock) </lastBlock>
      <justified>
        Epoch4 |-> Epoch3Epoch4Justified:Bool
        ...
      </justified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch2) </slot>
      <validators> v(m(_, _, EBM2, _, _, _, _), VIDs2) </validators>
      <lastBlock> (_, Epoch2BoundaryBlock) </lastBlock>
      <justified>
        Epoch4 |-> Epoch2Epoch4Justified:Bool
        Epoch3 |-> Epoch2Epoch3Justified:Bool
        ...
      </justified>
      <lastJustified> Epoch2LastJustifiedEpoch </lastJustified>
      ...
    </state>
    <state>
      <slot> firstSlotOf(Epoch1) </slot>
      <validators> v(m(_, _, EBM1, _, _, _, _), VIDs1) </validators>
      <lastBlock> (_, Epoch1BoundaryBlock) </lastBlock>
      <attested>
        Epoch3 |-> Epoch1Attestations3:Attestations
        Epoch2 |-> Epoch1Attestations2:Attestations
        ...
      </attested>
      <justified>
        Epoch4 |-> Epoch1Epoch4Justified:Bool
        Epoch3 |-> Epoch1Epoch3Justified:Bool
        Epoch2 |-> Epoch1Epoch2Justified:Bool
        ...
      </justified>
      <finalized>
        Epoch4 |-> Epoch1Epoch4Finalized:Bool
        Epoch3 |-> Epoch1Epoch3Finalized:Bool
        Epoch2 |-> false
        ...
      </finalized>
      <lastJustified> Epoch1LastJustifiedEpoch </lastJustified>
      <lastFinalized> Epoch1LastFinalizedEpoch </lastFinalized>
      ...
    </state>
    <state>
      <slot> Slot /* firstSlotOf(Epoch) */ </slot>
      <validators> v(m(_, _, EBM, _, _, _, _), VIDs) </validators>
      <attested>
        Epoch2 |-> Attestations2:Attestations
        Epoch1 |-> Attestations1:Attestations
        Epoch  |-> .Attestations
        ...
      </attested>
      <justified>
        Epoch4 |-> Epoch4Justified:Bool
        Epoch3 |-> Epoch3Justified:Bool
        Epoch2 |-> (PrevEpoch2Justified:Bool => ?NewEpoch2Justified:Bool)
        Epoch1 |-> (false                    => ?NewEpoch1Justified:Bool)
        Epoch  |-> false
        ...
      </justified>
      <finalized>
        Epoch4 |-> (PrevEpoch4Finalized:Bool => ?NewEpoch4Finalized:Bool)
        Epoch3 |-> (PrevEpoch3Finalized:Bool => ?NewEpoch3Finalized:Bool)
        Epoch2 |-> (false                    => ?NewEpoch2Finalized:Bool)
        Epoch1 |-> false
        Epoch  |-> false
        ...
      </finalized>
      <lastJustified> PrevLastJustifiedEpoch => ?NewLastJustifiedEpoch </lastJustified>
      <lastFinalized> PrevLastFinalizedEpoch => ?NewLastFinalizedEpoch </lastFinalized>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
andBool Epoch4 ==Int Epoch -Int 4
andBool Epoch3 ==Int Epoch -Int 3
andBool Epoch2 ==Int Epoch -Int 2
andBool Epoch1 ==Int Epoch -Int 1

andBool Epoch ==Int epochOf(Slot)
andBool Slot ==Int firstSlotOf(Epoch)

//
// invariant
//
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
andBool iff(Epoch1Epoch3Justified, isJustifiable(Epoch3, Epoch3BoundaryBlock, Epoch1Attestations3, EBM3, VIDs3))
andBool iff(Epoch1Epoch2Justified, isJustifiable(Epoch2, Epoch2BoundaryBlock, Epoch1Attestations2, EBM2, VIDs2))
andBool iff(Epoch1Epoch3Finalized, Epoch2LastJustifiedEpoch ==Int Epoch3 andBool Epoch1Epoch2Justified andBool Epoch1Epoch3Justified)
andBool isCorrectLastJustifiedEpoch(Epoch1LastJustifiedEpoch, Epoch1, Epoch1Epoch2Justified, Epoch1Epoch3Justified)
andBool isCorrectLastFinalizedEpoch(Epoch1LastFinalizedEpoch, Epoch1, Epoch1Epoch3Finalized, Epoch1Epoch4Finalized)
// state validness of e-2
andBool isCorrectLastJustifiedEpoch(Epoch2LastJustifiedEpoch, Epoch2, Epoch2Epoch3Justified, Epoch2Epoch4Justified)
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
andBool Epoch1LastFinalizedEpoch >=Int 0
andBool PrevLastJustifiedEpoch >=Int 0
andBool PrevLastFinalizedEpoch >=Int 0
ensures ?NewLastJustifiedEpoch >=Int 0
andBool ?NewLastFinalizedEpoch >=Int 0
//
// ensures
//
// justification of e-1 and e-2
andBool iff(?NewEpoch2Justified, isJustifiable(Epoch2, Epoch2BoundaryBlock, Attestations2, EBM2, VIDs2))
andBool iff(?NewEpoch1Justified, isJustifiable(Epoch1, Epoch1BoundaryBlock, Attestations1, EBM1, VIDs1))
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
[trusted]


rule
<T>
  <k> processRewardsPenalties(?Epoch -Int 2)
   ~> processValidatorUpdates() => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM1 => ?BM2, EBM, AEM1 => ?AEM2, AM1 => ?AM2, EM1 => ?EM2, WM1 => ?WM2), VIDs) </validators>
      <attested>
        ?Epoch -Int 2 |-> Attestations:Attestations
        ...
      </attested>
      <lastFinalized> LastFinalizedEpoch </lastFinalized>
      ...
    </state>
    <state>
      <slot> firstSlotOf(?Epoch -Int 2) </slot>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
andBool ?Epoch >=Int 0
andBool ?FinalityDelay >=Int 0
// let-bindings
andBool ?Epoch ==Int epochOf(Slot)
andBool ?FinalityDelay ==Int ?Epoch -Int 2 -Int LastFinalizedEpoch
andBool ?SourceAttestations ==K filterNotSlashed(SM, Attestations)
andBool ?TotalActiveBalance ==Int lift(totalBalance(EBM, activeValidators(VIDs, AM1, EM1, ?Epoch -Int 2)))
//
andBool ?ChurnLimitA ==Int churnLimit(size(activeValidators(VIDs, AM1, EM1, ?Epoch)))
andBool ?ChurnLimitB ==Int churnLimit(size(activeValidators(VIDs, AM1, EM1, ?Epoch -Int 1)))
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ActivationEpoch ==Int delayedActivationExitEpoch(?Epoch -Int 1)
andBool ?ValidatorsToBeActivated ==K activationQueueUptoChurnLimit(VIDs, AEM1, AM1, EM1, LastFinalizedEpoch, ?Epoch -Int 1)
// pre-conditions
andBool ?Epoch >=Int 4
andBool forall(x, VIDs, EBM[x]i >=Int 0)
andBool distinct(VIDs)
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).inclusion_delay >=Int 1))
andBool forall(x, VIDs, implies(x inA ?SourceAttestations, minByInclusionDelay(x, ?SourceAttestations).proposer in VIDs))
andBool isValidAttestations(Attestations, VIDs, AM1, EM1, ?Epoch -Int 2)
//
andBool LastFinalizedEpoch <Int FAR_FUTURE_EPOCH
andBool LastFinalizedEpoch <Int ?Epoch
andBool ?LastExitEpoch +Int size(VIDs) <Int FAR_FUTURE_EPOCH
andBool ?ActivationEpoch <Int FAR_FUTURE_EPOCH
andBool countValidatorsToActivate(VIDs, AM1, ?ActivationEpoch) ==Int 0
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, ?BM2[x]i <=Int BM1[x]i +Int (4 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)))
andBool forall(x, VIDs, ?BM2[x]i >=Int BM1[x]i -Int (7 *Int getBaseReward(EBM[x]i, ?TotalActiveBalance)) -Int getInactivityPenalty(EBM[x]i, ?FinalityDelay))
//
// processValidatorEjections 
andBool forall(x, VIDs, #if isActiveValidator(x, AM1, EM1, ?Epoch -Int 1) andBool EBM[x]i <=Int EJECTION_BALANCE andBool EM1[x]i ==Int FAR_FUTURE_EPOCH
                        #then ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH
                              andBool countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimitA
                        #else ?EM2[x]i ==Int EM1[x]i
                        #fi)
// updateActivationEligibilities
andBool forall(x, VIDs, ?AEM2[x]i ==Int #if isActivationEligible(x, AEM1, EBM) #then ?Epoch #else AEM1[x]i #fi)
// processValidatorActivation
andBool forall(x, ?ValidatorsToBeActivated, ?AM2[x]i ==Int ?ActivationEpoch)
andBool countValidatorsToActivate(VIDs, ?AM2, ?ActivationEpoch) <=Int ?ChurnLimitB
[trusted]

endmodule
