require "../../verification.k"

module M2-SPEC

imports VERIFICATION

rule
<T>
  <k> activateValidators(Vs) => .K ... </k>
  <currentSlot> Slot </currentSlot>
  <states>
    <state>
      <slot> Slot </slot>
      <validators> v(VM1 => ?VM2, _) </validators>
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
andBool ?Epoch ==Int epochOf(Slot) -Int 1
ensures true
// ensures
andBool ?VM2 ==K updateActivations(VM1, Vs, ?Epoch)

endmodule
