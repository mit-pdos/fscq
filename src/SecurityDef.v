Require Export SecurityHelper.

Set Implicit Arguments.

Definition prog_secure AT AEQ V T 
(wc: @mem addr addr_eq_dec valuset 
        -> @mem AT AEQ V -> Prop)
  (p : prog T) (pre post: pred):=
  forall m1 m2 m F1 F2 mp out1 vm hm,
  (F1 * diskIs m)%pred m1 ->
  (F2 * diskIs m)%pred m2 ->
  wc m mp ->
  pre mp ->
  exec m1 vm hm p out1 ->

  (exists r m1' m2' m' vm' hm' mr,
   out1 = Finished m1' vm' hm' r /\
   exec m2 vm hm p (Finished m2' vm' hm' r) /\
   (F1 * diskIs m')%pred m1' /\
   (F2 * diskIs m')%pred m2' /\
   wc m' mr /\
   post mr)
   
   \/

  (exists m1' m2' hm' mc,
   out1 = Crashed _ m1' hm' /\
   exec m2 vm hm p (Crashed _ m2' hm') /\
   (F1 * diskIs mc)%pred m1' /\
   (F2 * diskIs mc)%pred m2').


