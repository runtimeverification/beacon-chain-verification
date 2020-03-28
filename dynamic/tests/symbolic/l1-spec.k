require "../../verification.k"

module L1-SPEC

imports VERIFICATION

rule
<T>
  <k> initiateValidatorExit(#Validator(VID, false, (B, EB), (AEE, AE), (FAR_FUTURE_EPOCH, WE))) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators>
        VID |-> #Validator(VID, false, (B, EB), (AEE, AE), (FAR_FUTURE_EPOCH => ?ExitEpoch, WE => ?_))
        Vs
      </validators>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
/*
andBool Vs1 ==K VID |-> #Validator(VID, false, (B, EB), (AEE, AE), (FAR_FUTURE_EPOCH, WE)) Vs
*/
// types
andBool Slot >=Int 0
ensures true
andBool ?ExitEpoch >=Int delayedActivationExitEpoch(epochOf(Slot))

/*
rule
<T>
  <k> initiateValidatorExit(V) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators>
        V.id |-> (V => ?V2:Validator)
        Vs
      </validators>
      ...
    </state>
    ...
  </states>
  ...
</T>
requires true
andBool V.exit_epoch ==Int FAR_FUTURE_EPOCH
andBool Vs1 ==K V.id |-> V Vs
// types
andBool Slot >=Int 0
ensures true
andBool ?V2.exit_epoch >=Int delayedActivationExitEpoch(epochOf(Slot))
*/

endmodule
