require "../../verification.k"

require "../../process-slashing-spec.k"
require "../../process-attestation-spec.k"
require "../../process-deposit-spec.k"
require "../../process-validator-exit-spec.k"

module Q4-SPEC

imports VERIFICATION

imports PROCESS-SLASHING-SPEC
imports PROCESS-ATTESTATION-SPEC
imports PROCESS-DEPOSIT-SPEC
imports PROCESS-VALIDATOR-EXIT-SPEC

rule
<T>
  <k> begin
   ~> processSlashings(Ss)
   ~> processAttestations(As)
   ~> processDeposits(Ds)
   ~> processVoluntaryExits(VEs) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM1 => ?SM2, BM1 => ?BM2, EBM1 => ?EBM2, AEM1 => ?AEM2, AM1 => ?AM2, EM1 => ?EM2, WM1 => ?WM2), VIDs1 => ?VIDs2) </validators>
      <attested>
        ?Epoch -Int 1 |-> (PrevAs1:Attestations => ?PrevAs2)
        ?Epoch        |-> (CurrAs1:Attestations => ?CurrAs2)
        ...
      </attested>
      <slashedBalance> _ => ?_ </slashedBalance>
      ...
    </state>
    ...
  </states>
  <lastJustified> LastJustifiedEpoch </lastJustified>
  <lastBlock> BlockMap </lastBlock>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
// let-bindings
//// processVoluntaryExits
andBool ?Epoch ==Int epochOf(Slot)
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs1, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(VIDs1, AM1, EM1, ?Epoch)))
// pre-conditions
andBool disjoint(getValidatorsA(As),  getValidatorsS(Ss)) // no attestation from validators that will be slashed in this block
andBool disjoint(getValidatorsE(VEs), getValidatorsS(Ss)) // no voluntary exits from validators that will be slashed in this block
//// processSlashings
andBool forallS(x, Ss, isSlashableAttestation(x.attestation_1, x.attestation_2) andBool x.attestation_1.attester ==Int x.attestation_2.attester)
andBool forall(x, getValidatorsS(Ss), SM1[x]b ==K false)
andBool distinct(getValidatorsS(Ss))
andBool forall(x, getValidatorsS(Ss), x in VIDs1)
andBool ?Epoch <Int FAR_FUTURE_EPOCH
//// processAttestations
andBool ?Epoch >=Int 1
andBool isValidAttestationListPartial(As, Slot, LastJustifiedEpoch, BlockMap)
andBool forall(x, getValidatorsA(As), SM1[x]b ==K false)
andBool forall(x, getValidatorsA(As), x in VIDs1)
//// processDeposits
andBool distinct(VIDs1)
andBool isValidDeposits(Ds)
//// processVoluntaryExits
andBool ?LastExitEpoch +Int sizeS(Ss) +Int sizeE(VEs) <Int FAR_FUTURE_EPOCH
andBool forallE(x, VEs, isValidVoluntaryExit(x, AM1, EM1, ?Epoch))
andBool distinct(getValidatorsE(VEs))
andBool forall(x, getValidatorsE(VEs), x in VIDs1)
// invariants
ensures true
// post-conditions
//// processSlashings
andBool forall(x, getValidatorsS(Ss), ?SM2[x]b ==K true)
/* TODO:
andBool forall(x, getValidatorsS(Ss), implies(EM1[x]i ==Int FAR_FUTURE_EPOCH, ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH andBool countValidatorsToExit(?VIDs2, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit))
*/
//// processAttestations
andBool ?PrevAs2 ==K revA(getAttestations(As, ?Epoch -Int 1)) ++A PrevAs1
andBool ?CurrAs2 ==K revA(getAttestations(As, ?Epoch       )) ++A CurrAs1
//// processDeposits
andBool distinct(?VIDs2)
andBool ?VIDs2 ==K unique(rev(getValidatorsD(Ds)) ++ VIDs1)
/*
andBool forall(x, ?VIDs2,  ?SM2[x]b ==K   #if x in VIDs1 #then  SM1[x]b #else false                 #fi)
andBool forall(x, ?VIDs2,  ?BM2[x]i >=Int #if x in VIDs1 #then  BM1[x]i #else 0                     #fi)
*/
andBool forall(x, ?VIDs2, ?EBM2[x]i >=Int #if x in VIDs1 #then EBM1[x]i #else 0                     #fi)
andBool forall(x, ?VIDs2, ?EBM2[x]i <=Int #if x in VIDs1 #then EBM1[x]i #else MAX_EFFECTIVE_BALANCE #fi)
andBool forall(x, ?VIDs2, ?AEM2[x]i ==Int #if x in VIDs1 #then AEM1[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, ?VIDs2,  ?AM2[x]i ==Int #if x in VIDs1 #then  AM1[x]i #else FAR_FUTURE_EPOCH      #fi)
/*
andBool forall(x, ?VIDs2,  ?EM2[x]i ==Int #if x in VIDs1 #then  EM1[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, ?VIDs2,  ?WM2[x]i ==Int #if x in VIDs1 #then  WM1[x]i #else FAR_FUTURE_EPOCH      #fi)
*/
//// processVoluntaryExits
andBool forall(x, getValidatorsE(VEs), ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch))
andBool forall(x, getValidatorsE(VEs), ?EM2[x]i  <Int FAR_FUTURE_EPOCH)
andBool forall(x, getValidatorsE(VEs), countValidatorsToExit(?VIDs2, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit)
// TODO: specify preserved other entries

/*
rule
<T>
  <k> processSlashings(Ss) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM1 => ?SM2, BM1 => ?BM2, EBM, AEM, AM, EM1 => ?EM2, WM1 => ?WM2), VIDs) </validators>
      <slashedBalance> _ => ?_ </slashedBalance>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
// let-bindings
andBool ?Epoch ==Int epochOf(Slot)
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(VIDs, AM, EM1, ?Epoch)))
// pre-conditions
andBool ?LastExitEpoch +Int sizeS(Ss) <Int FAR_FUTURE_EPOCH
andBool forallS(x, Ss, isSlashableAttestation(x.attestation_1, x.attestation_2) andBool x.attestation_1.attester ==Int x.attestation_2.attester)
andBool forall(x, getValidatorsS(Ss), SM1[x]b ==K false)
andBool distinct(getValidatorsS(Ss))
andBool forall(x, getValidatorsS(Ss), x in VIDs)
andBool ?Epoch <Int FAR_FUTURE_EPOCH
// invariants
ensures true
// post-conditions
andBool forall(x, VIDs, implies(notBool x in getValidatorsS(Ss), ?SM2[x]b ==K SM1[x]b))
andBool forall(x, VIDs, implies(notBool x in getValidatorsS(Ss), ?BM2[x]i ==K BM1[x]i))
andBool forall(x, VIDs, implies(notBool x in getValidatorsS(Ss), ?EM2[x]i ==K EM1[x]i))
andBool forall(x, VIDs, implies(notBool x in getValidatorsS(Ss), ?WM2[x]i ==K WM1[x]i))
andBool forall(x, getValidatorsS(Ss), ?SM2[x]b ==K true)
andBool forall(x, getValidatorsS(Ss), #if EM1[x]i ==Int FAR_FUTURE_EPOCH
                                      #then ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH
                                            andBool countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit
                                      #else ?EM2[x]i ==Int EM1[x]i
                                      #fi)
// rely-guarantee conditions
andBool maxInt(maxExitEpoch(VIDs, ?EM2), delayedActivationExitEpoch(?Epoch)) <=Int ?LastExitEpoch +Int sizeS(Ss)
andBool activeValidators(VIDs, AM, ?EM2, ?Epoch) ==K activeValidators(VIDs, AM, EM1, ?Epoch)
[trusted]

rule
<T>
  <k> processAttestations(As) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(VM, _) </validators>
      <attested>
        ?Epoch -Int 1 |-> (PrevAs1:Attestations => ?PrevAs2)
        ?Epoch        |-> (CurrAs1:Attestations => ?CurrAs2)
        ...
      </attested>
      ...
    </state>
    ...
  </states>
  <lastJustified> LastJustifiedEpoch </lastJustified>
  <lastBlock> BlockMap </lastBlock>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
// let-bindings
andBool ?Epoch ==Int epochOf(Slot)
// pre-conditions
andBool ?Epoch >=Int 1
andBool isValidAttestationListPartial(As, Slot, LastJustifiedEpoch, BlockMap)
andBool forall(x, getValidatorsA(As), VM.slashed[x]b ==K false)
// invariants
ensures true
// post-conditions
andBool ?PrevAs2 ==K revA(getAttestations(As, ?Epoch -Int 1)) ++A PrevAs1
andBool ?CurrAs2 ==K revA(getAttestations(As, ?Epoch       )) ++A CurrAs1
[trusted]

rule
<T>
  <k> processDeposits(Ds) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM1 => ?SM2, BM1 => ?BM2, EBM1 => ?EBM2, AEM1 => ?AEM2, AM1 => ?AM2, EM1 => ?EM2, WM1 => ?WM2), VIDs1 => ?VIDs2) </validators>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
// let-bindings
// pre-conditions
andBool distinct(VIDs1)
andBool isValidDeposits(Ds)
// invariants
ensures true
// post-conditions
andBool distinct(?VIDs2)
andBool ?VIDs2 ==K unique(rev(getValidatorsD(Ds)) ++ VIDs1)
andBool forall(x, ?VIDs2,  ?SM2[x]b ==K   #if x in VIDs1 #then  SM1[x]b #else false                 #fi)
andBool forall(x, ?VIDs2,  ?BM2[x]i >=Int #if x in VIDs1 #then  BM1[x]i #else 0                     #fi)
andBool forall(x, ?VIDs2, ?EBM2[x]i >=Int #if x in VIDs1 #then EBM1[x]i #else 0                     #fi)
andBool forall(x, ?VIDs2, ?EBM2[x]i <=Int #if x in VIDs1 #then EBM1[x]i #else MAX_EFFECTIVE_BALANCE #fi)
andBool forall(x, ?VIDs2, ?AEM2[x]i ==Int #if x in VIDs1 #then AEM1[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, ?VIDs2,  ?AM2[x]i ==Int #if x in VIDs1 #then  AM1[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, ?VIDs2,  ?EM2[x]i ==Int #if x in VIDs1 #then  EM1[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, ?VIDs2,  ?WM2[x]i ==Int #if x in VIDs1 #then  WM1[x]i #else FAR_FUTURE_EPOCH      #fi)
[trusted]

rule
<T>
  <k> processVoluntaryExits(VEs) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(m(SM, BM, EBM, AEM, AM, EM1 => ?EM2, WM1 => ?WM2), VIDs) </validators>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
// types
andBool Slot >=Int 0
// let-bindings
andBool ?Epoch ==Int epochOf(Slot)
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(VIDs, AM, EM1, ?Epoch)))
// pre-conditions
andBool ?LastExitEpoch +Int sizeE(VEs) <Int FAR_FUTURE_EPOCH
andBool forallE(x, VEs, isValidVoluntaryExit(x, AM, EM1, ?Epoch))
andBool distinct(getValidatorsE(VEs))
andBool forall(x, getValidatorsE(VEs), x in VIDs)
// invariants
ensures true
// post-conditions
andBool forall(x, getValidatorsE(VEs), ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch))
andBool forall(x, getValidatorsE(VEs), ?EM2[x]i  <Int FAR_FUTURE_EPOCH)
andBool forall(x, getValidatorsE(VEs), countValidatorsToExit(VIDs, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit)
[trusted]
*/

endmodule
