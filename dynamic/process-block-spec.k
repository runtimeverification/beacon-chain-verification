require "verification.k"

require "process-slashing-spec.k"
require "process-attestation-spec.k"
require "process-deposit-spec.k"
require "process-validator-exit-spec.k"

module PROCESS-BLOCK-SPEC

imports VERIFICATION

imports PROCESS-SLASHING-SPEC
imports PROCESS-ATTESTATION-SPEC
imports PROCESS-DEPOSIT-SPEC
imports PROCESS-VALIDATOR-EXIT-SPEC

rule
<T>
  <k> processBlock(#Block((Slot, ID), Parent, Ss, As, Ds, VEs)) => .K ... </k>
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
    <state>
      <slot> Slot -Int 1 </slot>
      <validators> v(m(SM1, BM1, EBM1, AEM1, AM1, EM1, WM1), VIDs1) </validators>
      ...
    </state>
    ...
  </states>
  <lastJustified> LastJustifiedEpoch </lastJustified>
  <lastBlock> BlockMap => BlockMap [ Slot <- ID ]i </lastBlock>
  <blocks> Bs => Bs [ ID <- #Block((Slot, ID), Parent, Ss, As, Ds, VEs) ]k </blocks>
  ...
</T>
requires true

// types
andBool Slot >=Int 1

// let-bindings
//// processVoluntaryExits
andBool ?Epoch ==Int epochOf(Slot)
andBool ?LastExitEpoch ==Int maxInt(maxExitEpoch(VIDs1, EM1), delayedActivationExitEpoch(?Epoch))
andBool ?ChurnLimit ==Int churnLimit(size(activeValidators(VIDs1, AM1, EM1, ?Epoch)))

////////////////////
// pre-conditions
////////////////////

andBool disjoint(getValidatorsA(As),  getValidatorsS(Ss)) // no attestation from validators that will be slashed in this block
andBool disjoint(getValidatorsE(VEs), getValidatorsS(Ss)) // no voluntary exits from validators that will be slashed in this block
andBool ?LastExitEpoch +Int sizeS(Ss) +Int sizeE(VEs) +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY <Int FAR_FUTURE_EPOCH
andBool ?Epoch +Int EPOCHS_PER_SLASHINGS_VECTOR <Int FAR_FUTURE_EPOCH
andBool forall(x, VIDs1,  BM1[x]i >=Int 0)
andBool forall(x, VIDs1, EBM1[x]i >=Int 0)
andBool forall(x, VIDs1, AEM1[x]i >=Int 0)
andBool forall(x, VIDs1,  AM1[x]i >=Int 0)
andBool forall(x, VIDs1,  EM1[x]i >=Int 0)
andBool forall(x, VIDs1,  WM1[x]i >=Int 0)

//// processSlashings

andBool forallS(x, Ss, isSlashableAttestation(x.attestation_1, x.attestation_2) andBool x.attestation_1.attester ==Int x.attestation_2.attester)
andBool forall(x, getValidatorsS(Ss), SM1[x]b ==K false)
andBool forall(x, getValidatorsS(Ss), AM1[x]i <=Int ?Epoch)
andBool forall(x, getValidatorsS(Ss), WM1[x]i  >Int ?Epoch)
andBool distinct(getValidatorsS(Ss))
andBool forall(x, getValidatorsS(Ss), x in VIDs1)

//// processAttestations

andBool ?Epoch >=Int 1
andBool isValidAttestationListPartial(As, Slot, LastJustifiedEpoch, BlockMap [ Slot <- ID ]i)
andBool forall(x, getValidatorsA(As), SM1[x]b ==K false)
andBool forall(x, getValidatorsA(As), x in VIDs1)

//// processDeposits

andBool distinct(VIDs1)
andBool isValidDeposits(Ds)

//// processVoluntaryExits

andBool forallE(x, VEs, isValidVoluntaryExit(x, AM1, EM1, ?Epoch))
andBool distinct(getValidatorsE(VEs))
andBool forall(x, getValidatorsE(VEs), x in VIDs1)

ensures true

////////////////////
// post-conditions
////////////////////

//// processSlashings

//// processAttestations

andBool ?PrevAs2 ==K revA(getAttestations(As, ?Epoch -Int 1)) ++A PrevAs1
andBool ?CurrAs2 ==K revA(getAttestations(As, ?Epoch       )) ++A CurrAs1

//// processDeposits

andBool distinct(?VIDs2)
andBool ?VIDs2 ==K unique(rev(getValidatorsD(Ds)) ++ VIDs1)

//// processVoluntaryExits

//// summary

// existing validators
andBool forall(x, VIDs1, #if x in getValidatorsS(Ss) #then ?SM2[x]b ==K true #else ?SM2[x]b ==K SM1[x]b #fi)
andBool forall(x, VIDs1, #if x in getValidatorsS(Ss) orBool x in getValidatorsD(Ds) #then ?BM2[x]i >=Int 0 #else ?BM2[x]i ==Int BM1[x]i #fi)
andBool forall(x, VIDs1, ?EBM2[x]i ==Int EBM1[x]i)
andBool forall(x, VIDs1, ?AEM2[x]i ==Int AEM1[x]i)
andBool forall(x, VIDs1,  ?AM2[x]i ==Int  AM1[x]i)
andBool forall(x, VIDs1, #if (x in getValidatorsS(Ss) andBool EM1[x]i ==Int FAR_FUTURE_EPOCH) orBool x in getValidatorsE(VEs)
                         #then ?EM2[x]i >=Int delayedActivationExitEpoch(?Epoch) andBool ?EM2[x]i <Int FAR_FUTURE_EPOCH // andBool countValidatorsToExit(?VIDs2, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit
                         #else ?EM2[x]i ==Int EM1[x]i #fi)
andBool forall(x, VIDs1, #if       x in getValidatorsS(Ss)  #then ?WM2[x]i >=Int ?Epoch +Int EPOCHS_PER_SLASHINGS_VECTOR                            // TODO: andBool ?WM2[x]i <Int FAR_FUTURE_EPOCH
                         #else #if x in getValidatorsE(VEs) #then ?WM2[x]i >=Int delayedActivationExitEpoch(?Epoch) +Int MIN_VALIDATOR_WITHDRAWABILITY_DELAY andBool ?WM2[x]i <Int FAR_FUTURE_EPOCH
                         #else ?WM2[x]i ==Int WM1[x]i #fi #fi)
/* TODO:
andBool forall(x, getValidatorsS(Ss), implies(EM1[x]i ==Int FAR_FUTURE_EPOCH, countValidatorsToExit(?VIDs2, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit))
*/
andBool forall(x, getValidatorsE(VEs), countValidatorsToExit(?VIDs2, ?EM2, ?EM2[x]i) <=Int ?ChurnLimit)

// new validators
andBool forall(x, ?VIDs2, implies(notBool x in VIDs1,  ?SM2[x]b ==K false))
andBool forall(x, ?VIDs2, implies(notBool x in VIDs1,  ?BM2[x]i >=Int 0))
andBool forall(x, ?VIDs2, implies(notBool x in VIDs1, ?EBM2[x]i >=Int 0 andBool ?EBM2[x]i <=Int MAX_EFFECTIVE_BALANCE))
andBool forall(x, ?VIDs2, implies(notBool x in VIDs1, ?AEM2[x]i ==Int FAR_FUTURE_EPOCH))
andBool forall(x, ?VIDs2, implies(notBool x in VIDs1,  ?AM2[x]i ==Int FAR_FUTURE_EPOCH))
andBool forall(x, ?VIDs2, implies(notBool x in VIDs1,  ?EM2[x]i ==Int FAR_FUTURE_EPOCH))
andBool forall(x, ?VIDs2, implies(notBool x in VIDs1,  ?WM2[x]i ==Int FAR_FUTURE_EPOCH))

// no negative values
andBool forall(x, ?VIDs2,  ?BM2[x]i >=Int 0)
andBool forall(x, ?VIDs2, ?EBM2[x]i >=Int 0)
andBool forall(x, ?VIDs2, ?AEM2[x]i >=Int 0)
andBool forall(x, ?VIDs2,  ?AM2[x]i >=Int 0)
andBool forall(x, ?VIDs2,  ?EM2[x]i >=Int 0)
andBool forall(x, ?VIDs2,  ?WM2[x]i >=Int 0)

/* TODO:
 - specify <slashedBalance> update
 - base case: when ?Epoch ==Int 0
 */

endmodule
