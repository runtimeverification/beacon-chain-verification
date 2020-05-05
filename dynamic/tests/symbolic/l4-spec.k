require "../../verification.k"

module L4-SPEC

imports VERIFICATION

rule
<T>
  <k> processVoluntaryExits(VEs) => . </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(VM, VIDs) => ?VS2 </validators>
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
// conditions
andBool isValidVoluntaryExits(VEs, VM, ?Epoch, VIDs)
ensures true
// ensures
andBool ?VS2 ==K storeValidatorExits(v(VM, VIDs), VEs, ?Epoch)

endmodule
