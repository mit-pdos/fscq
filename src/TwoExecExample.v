(** this axioms may simplify tree equivalence after execution proofs *)
Axiom one_tag_per_user:
  forall pr t t',
    t <> Public ->
    t' <> Public ->
    can_access pr t ->
    can_access pr t' ->
    t = t'.

Axiom one_user_per_tag:
  forall pr pr' t,
    t <> Public ->
    can_access pr t ->
    can_access pr' t ->
    pr = pr'.


Definition sys_rep Fr Fm Ftop fsxp ds sm tree ilist frees mscs bm hm:=
  (Fr * [[ sync_invariant Fr ]] *
   LOG.rep (FSXPLog fsxp) (SB.rep fsxp) (LOG.NoTxn ds) (MSLL mscs) sm bm hm *
   [[[ ds!! ::: (Fm * rep fsxp Ftop tree ilist frees mscs sm)]]])%pred.















Lemma two_exec_return_indistinguishable:
  forall T (p: fprog T) pathname f pr off vs inum Fd tag
    Fr1 Fm1 Ftop1 ds1 sm1 tree1 mscs1 mscs1' fsxp1 ilist1 frees1 d1 bm1 hm1 d1' bm1' hm1' tr1 tr1'
    Fr2 Fm2 Ftop2 ds2 sm2 tree2 mscs2 mscs2' fsxp2 ilist2 frees2 d2 bm2 hm2 d2' bm2' hm2' tr2 tr2'
    (r1 r2: T),
    
  fexec pr tr1 d1 bm1 hm1 mscs1 p (RFinished d1' bm1' hm1' r1) mscs1' tr1' ->
  fexec pr tr2 d2 bm2 hm2 mscs2 p (RFinished d2' bm2' hm2' r2) mscs2' tr2' ->

  
  (sys_rep Fr1 Fm1 Ftop1 fsxp1 ds1 sm1 tree1 ilist1 frees1 mscs1 bm1 hm1)%pred d1 ->
  (sys_rep Fr2 Fm2 Ftop2 fsxp2 ds2 sm2 tree2 ilist2 frees2 mscs2 bm2 hm2)%pred d2 ->

  (** this represents the residual part of the precondition.
  e.g. a file existing and file having a block in the given offset etc. *)
  satisfies_precondition tree1 p ->
  satisfies precondition tree2 p ->
  
  can_access pr tag ->
  equivalent_for tag tree1 tree2 ->
  r1 = r2.









  

  


  

(** This is an alternative, stronger lemma which requires 
    proving an existence of a successful execution from equivalent tree. 
    I am not sure this version is provable in our framnework. **)
Lemma two_exec_return_indistinguishable_alternative:
  forall T (p: fprog T) pathname f pr off vs inum Fd tag
    Fr1 Fm1 Ftop1 ds1 sm1 tree1 mscs1 fsxp1 ilist1 frees1 d1 bm1 hm1 tr1 d1' bm1' hm1' mscs1' tr1'
    Fr2 Fm2 Ftop2 ds2 sm2 tree2 mscs2 fsxp2 ilist2 frees2 d2 bm2 hm2 tr2
    (r1 r2: T),
    
  fexec pr tr1 d1 bm1 hm1 mscs1 p (RFinished d1' bm1' hm1' r1) mscs1' tr1' ->
  
  (sys_rep Fr1 Fm1 Ftop1 fsxp1 ds1 sm1 tree1 ilist1 frees1 mscs1 bm1 hm1)%pred d1 ->
  (sys_rep Fr2 Fm2 Ftop2 fsxp2 ds2 sm2 tree2 ilist2 frees2 mscs2 bm2 hm2)%pred d2 ->

  (** this represents the residual part of the precondition.
  e.g. a file existing and file having a block in the given offset etc. *)
  satisfies_precondition tree1 p ->
  satisfies precondition tree2 p ->
  
  can_access pr tag ->
  equivalent_for tag tree1 tree2 ->
  
  exists d2' bm2' hm2' r2 mscs2' tr2',
    fexec pr tr2 d2 bm2 hm2 mscs2 p (RFinished d2' bm2' hm2' r2) mscs2' tr2' /\
    r1 = r2.

















  
(** This lemma proves that -combined with two_exec_return_indistinguishable- 
   interleaving syscalls from different users will preserve isolation.
   it inforamlly states the parts that user pr can't reach will stay equivalent 
   after series of syscalls from that user. **)
  Lemma two_exec_no_effect_on_others:
  forall T (p: fprog T) pathname f pr off vs inum Fd tag tag'
    Fr1 Fm1 Ftop1 ds1 sm1 tree1 mscs1 mscs1' fsxp1 ilist1 frees1 d1 bm1 hm1 d1' bm1' hm1' tr1 tr1'
    Fr2 Fm2 Ftop2 ds2 sm2 tree2 mscs2 mscs2' fsxp2 ilist2 frees2 d2 bm2 hm2 d2' bm2' hm2' tr2 tr2'
    (r1 r2: T),
    
  fexec pr tr1 d1 bm1 hm1 mscs1 p (RFinished d1' bm1' hm1' r1) mscs1' tr1' ->
  fexec pr tr2 d2 bm2 hm2 mscs2 p (RFinished d2' bm2' hm2' r2) mscs2' tr2' ->

  
  (sys_rep Fr1 Fm1 Ftop1 fsxp1 ds1 sm1 tree1 ilist1 frees1 mscs1 bm1 hm1)%pred d1 ->
  (sys_rep Fr2 Fm2 Ftop2 fsxp2 ds2 sm2 tree2 ilist2 frees2 mscs2 bm2 hm2)%pred d2 ->

  (** this represents the residual part of the precondition.
  e.g. a file existing and file having a block in the given offset etc. *)
  satisfies_precondition tree1 p ->
  satisfies precondition tree2 p ->
  
  can_access pr tag ->
  tag <> tag' ->
  equivalent_for tag' tree1 tree2 ->

  exists ds1' sm1' tree1' ilist1' frees1' ds2' sm2' tree2' ilist2' frees2',
      (sys_rep Fr1 Fm1 Ftop1 fsxp1 ds1' sm1' tree1' ilist1' frees1' mscs1' bm1' hm1')%pred d1' /\
      (sys_rep Fr2 Fm2 Ftop2 fsxp2 ds2' sm2' tree2' ilist2' frees2' mscs2' bm2' hm2')%pred d2' /\
      equivalent_for tag' tree1' tree2'.





























    
(** CRASHES **)


(** One shortcoming of the below lemma is that 
    it starts execution from a synced disc. 
    This requirement is imposed by the second part of the conclusion.
    if we would allow from some arbitrary disk, 
    then it could be recovered to a state 
    that is even before where p starts to execute.
    If that is the case, I don't know how to prove 
    the property second part wants to prove. **)
Lemma two_exec_recover_equivalent:
  forall T (p: fprog T) pathname f pr off vs inum Fd tag
    Fr1 Fm1 Ftop1 ds1 sm1 tree1 mscs1 mscs1' fsxp1 ilist1 frees1 d1 bm1 hm1 d1' bm1' hm1' tr1 tr1'
    Fr2 Fm2 Ftop2 ds2 sm2 tree2 mscs2 mscs2' fsxp2 ilist2 frees2 d2 bm2 hm2 d2' bm2' hm2' tr2 tr2'
    (r1 r2: T),
    
  fexec pr tr1 d1 bm1 hm1 mscs1 p (RRecovered d1' bm1' hm1' r1) mscs1' tr1' ->
  fexec pr tr2 d2 bm2 hm2 mscs2 p (RRecovered d2' bm2' hm2' r2) mscs2' tr2' ->
  
  
  (sys_rep Fr1 Fm1 Ftop1 fsxp1 (ds1, []) sm1 tree1 ilist1 frees1 mscs1 bm1 hm1)%pred d1 ->
  (sys_rep Fr2 Fm2 Ftop2 fsxp2 (ds2, []) sm2 tree2 ilist2 frees2 mscs2 bm2 hm2)%pred d2 ->

  (** this represents the residual part of the precondition.
  e.g. a file existing and file having a block in the given offset etc. *)
  satisfies_precondition tree1 p ->
  satisfies precondition tree2 p ->
  
  can_access pr tag ->
  equivalent_for tag tree1 tree2 ->

  exists Fr1' Fm1' Ftop1' fsxp1' ds1' sm1' tree1' ilist1' frees1'
     Fr2' Fm2' Ftop2' fsxp2' ds2' sm2' tree2' ilist2' frees2',

    (sys_rep Fr1 Fm1 Ftop1 fsxp1 (ds1', []) sm1'
             tree1' ilist1' frees1' mscs1' bm1' hm1')%pred d1' /\
    (sys_rep Fr2 Fm2 Ftop2 fsxp2 (ds2', []) sm2'
             tree2' ilist2' frees2' mscs2' bm2' hm2')%pred d2' /\
    equivalent_for tag tree1' tree2' /\

  (** this part says that the disks we recovered are reachable by 
      executing only a prefix of the program p. This has an implication that 
      we didn't recover a data to a wrong owner **)
  exists n,
  (exists d1'' bm1'' hm1'' r1' mscs1'' tr1'' ds1'' sm1'' ilist1'' frees1'',
     fexec pr tr1 d1 bm1 hm1 mscs1 (firstn_steps n p)
           (RFinished d1'' bm1'' hm1'' r1') mscs1'' tr1'' /\
     (sys_rep Fr1 Fm1 Ftop1 fsxp1 ds1'' sm1''
              tree1' ilist1'' frees1'' mscs1'' bm1'' hm1'')%pred d1'' /\
     ds1''!! = ds1') /\
  (exists d2'' bm2'' hm2'' r2' mscs2'' tr2'' ds2'' sm2'' ilist2'' frees2'',
     fexec pr tr2 d2 bm2 hm2 mscs2 (firstn_steps n p)
           (RFinished d2'' bm2'' hm2'' r2') mscs2'' tr2'' /\
     (sys_rep Fr2 Fm2 Ftop2 fsxp2 ds2'' sm2''
              tree2' ilist2'' frees2'' mscs2'' bm2'' hm2'')%pred d2'' /\
      ds2''!! = ds2!).
