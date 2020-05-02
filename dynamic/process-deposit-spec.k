require "verification.k"

module PROCESS-DEPOSIT-SPEC

imports VERIFICATION

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
andBool forall(x, getValidatorsD(Ds),  ?SM2[x]b ==K   #if x in VIDs1 #then  SM1[x]b #else false                 #fi)
andBool forall(x, getValidatorsD(Ds),  ?BM2[x]i >=Int #if x in VIDs1 #then  BM1[x]i #else 0                     #fi)
andBool forall(x, getValidatorsD(Ds), ?EBM2[x]i >=Int #if x in VIDs1 #then EBM1[x]i #else 0                     #fi)
andBool forall(x, getValidatorsD(Ds), ?EBM2[x]i <=Int #if x in VIDs1 #then EBM1[x]i #else MAX_EFFECTIVE_BALANCE #fi)
andBool forall(x, getValidatorsD(Ds), ?AEM2[x]i ==Int #if x in VIDs1 #then AEM1[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, getValidatorsD(Ds),  ?AM2[x]i ==Int #if x in VIDs1 #then  AM1[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, getValidatorsD(Ds),  ?EM2[x]i ==Int #if x in VIDs1 #then  EM1[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, getValidatorsD(Ds),  ?WM2[x]i ==Int #if x in VIDs1 #then  WM1[x]i #else FAR_FUTURE_EPOCH      #fi)

rule
<T>
  <k> processDepositsAux(L_VIDs, Ds, v(m(SM0, BM0, EBM0, AEM0, AM0, EM0, WM0), VIDs0)) => .K ... </k>
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
andBool distinct(VIDs0)
andBool isValidDeposits(Ds)
// invariants
andBool VIDs1 ==K unique(L_VIDs ++ VIDs0)
andBool forall(x, VIDs1, implies(notBool x in L_VIDs, x in VIDs0))
andBool forall(x, VIDs1, implies(notBool x in L_VIDs,  SM1[x]b ==K  SM0[x]b))
andBool forall(x, VIDs1, implies(notBool x in L_VIDs,  BM1[x]i ==K  BM0[x]i))
andBool forall(x, VIDs1, implies(notBool x in L_VIDs, EBM1[x]i ==K EBM0[x]i))
andBool forall(x, VIDs1, implies(notBool x in L_VIDs, EBM1[x]i ==K EBM0[x]i))
andBool forall(x, VIDs1, implies(notBool x in L_VIDs, AEM1[x]i ==K AEM0[x]i))
andBool forall(x, VIDs1, implies(notBool x in L_VIDs,  AM1[x]i ==K  AM0[x]i))
andBool forall(x, VIDs1, implies(notBool x in L_VIDs,  EM1[x]i ==K  EM0[x]i))
andBool forall(x, VIDs1, implies(notBool x in L_VIDs,  WM1[x]i ==K  WM0[x]i))
andBool forall(x, rev(L_VIDs)                      ,  SM1[x]b ==K   #if x in VIDs0 #then  SM0[x]b #else false                 #fi)
andBool forall(x, rev(L_VIDs)                      ,  BM1[x]i >=Int #if x in VIDs0 #then  BM0[x]i #else 0                     #fi)
andBool forall(x, rev(L_VIDs)                      , EBM1[x]i >=Int #if x in VIDs0 #then EBM0[x]i #else 0                     #fi)
andBool forall(x, rev(L_VIDs)                      , EBM1[x]i <=Int #if x in VIDs0 #then EBM0[x]i #else MAX_EFFECTIVE_BALANCE #fi)
andBool forall(x, rev(L_VIDs)                      , AEM1[x]i ==Int #if x in VIDs0 #then AEM0[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, rev(L_VIDs)                      ,  AM1[x]i ==Int #if x in VIDs0 #then  AM0[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, rev(L_VIDs)                      ,  EM1[x]i ==Int #if x in VIDs0 #then  EM0[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, rev(L_VIDs)                      ,  WM1[x]i ==Int #if x in VIDs0 #then  WM0[x]i #else FAR_FUTURE_EPOCH      #fi)
ensures true
// post-conditions
andBool distinct(?VIDs2)
andBool ?VIDs2 ==K unique(rev(getValidatorsD(Ds)) ++ VIDs1)
andBool forall(x, rev(L_VIDs) ++ getValidatorsD(Ds),  ?SM2[x]b ==K   #if x in VIDs0 #then  SM0[x]b #else false                 #fi)
andBool forall(x, rev(L_VIDs) ++ getValidatorsD(Ds),  ?BM2[x]i >=Int #if x in VIDs0 #then  BM0[x]i #else 0                     #fi)
andBool forall(x, rev(L_VIDs) ++ getValidatorsD(Ds), ?EBM2[x]i >=Int #if x in VIDs0 #then EBM0[x]i #else 0                     #fi)
andBool forall(x, rev(L_VIDs) ++ getValidatorsD(Ds), ?EBM2[x]i <=Int #if x in VIDs0 #then EBM0[x]i #else MAX_EFFECTIVE_BALANCE #fi)
andBool forall(x, rev(L_VIDs) ++ getValidatorsD(Ds), ?AEM2[x]i ==Int #if x in VIDs0 #then AEM0[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, rev(L_VIDs) ++ getValidatorsD(Ds),  ?AM2[x]i ==Int #if x in VIDs0 #then  AM0[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, rev(L_VIDs) ++ getValidatorsD(Ds),  ?EM2[x]i ==Int #if x in VIDs0 #then  EM0[x]i #else FAR_FUTURE_EPOCH      #fi)
andBool forall(x, rev(L_VIDs) ++ getValidatorsD(Ds),  ?WM2[x]i ==Int #if x in VIDs0 #then  WM0[x]i #else FAR_FUTURE_EPOCH      #fi)

endmodule
