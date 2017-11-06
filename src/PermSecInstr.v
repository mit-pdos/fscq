Require Export PermSec.



Lemma read_secure:
  forall s pr a tb,
    permission_secure pr s (Read a) (fun s => disk s a = Some tb) (fun s s' r => s' = blocks_upd s r tb).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; simpl in *; cleanup.
  simpl; intuition.
Qed.

Lemma write_secure:
  forall pr s a i tb,
    permission_secure pr s (Write a i) (fun s => blocks s i = Some tb)
                      (fun s s' _ => s' = disk_upd s a tb).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; simpl in *; cleanup.
  simpl; intuition.
Qed.


Lemma seal_secure:
  forall pr s t b,
    can_access pr t ->
    permission_secure pr s (Seal t b) (fun _ => True)
                      (fun s s' r => s' = blocks_upd s r (t, b)).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; simpl in *; cleanup.
  simpl; intuition.
Qed.

Lemma unseal_secure:
  forall pr s i t b,
    can_access pr t ->
    permission_secure pr s (Unseal i) (fun s => blocks s i = Some (t, b))
                      (fun s s' r => s' = s /\ r = b).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; simpl in *; cleanup.
  simpl; intuition.
Qed.

Lemma ret_secure:
  forall T pr s (v: T),
    permission_secure pr s (Ret v) (fun _ => True) (fun s s' r => s' = s /\ r = v).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; simpl in *; cleanup.
  simpl; intuition.
Qed.

Lemma run_secure:
  forall T s (p: prog T) pr pr' pre post,
    permission_secure pr' s p pre post ->
    permitted pr pr' ->
    permission_secure pr s (Run pr' p) pre post.
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; simpl in *.
  specialize (trace_app H11); intros; cleanup.
  specialize (H _ _ _ _ H1 H11); intuition.
  simpl; intuition.
  eapply trace_secure_permitted; eauto.
Qed.

Lemma bind_secure:
  forall T T' (p1: prog T) (p2: T -> prog T') t s pre post
    (post': state -> Prop) (post2: state -> state -> T' -> Prop),
    permission_secure t s p1 pre post ->
    (forall s' tr tr' r,
       pre s ->
       exec t s tr p1 s' (Finished r) tr' ->
       post s s' r ->
       post' s') ->
    (forall s' s'' tr tr' tr'' r r',
       pre s ->
       exec t s tr p1 s' (Finished r) tr' ->
       post s s' r ->
       post' s' ->
       exec t s' tr' (p2 r) s'' (Finished r') tr'' ->
       post2 s' s'' r' ->
       post2 s s'' r') ->
    (forall s' tr tr' r,
       pre s ->
       exec t s tr p1 s' (Finished r) tr' ->
       post s s' r ->
       permission_secure t s' (p2 r) post' post2 ) ->
    permission_secure t s (Bind p1 p2) pre post2.
Proof.
  unfold permission_secure; intros.
  inv_exec_perm.
  specialize (trace_app H4); intros; cleanup.
  specialize (H _ _ _ _ H3 H4); cleanup.
  specialize (trace_app H5); intros; cleanup.
  specialize (H0 _ _ _ _ H3 H4 H6); cleanup.
  specialize (H2 _ _ _ _ H3 H4 H6); cleanup.
  specialize (H2 _ _ _ _ H0 H5); cleanup.
  specialize (H1 _ _ _ _ _ _ _ H3 H4 H6 H0 H5 H7); intuition.
  apply trace_secure_app; auto.
Qed.


Lemma permission_drop_secure:
  forall s pr1 pr2 T (p: prog T) pre post,
    permission_secure pr1 s p pre post ->
    permitted pr2 pr1 ->
    (forall s' tr tr2 r, exec pr2 s tr p s' r (tr2++tr) ->
                      exists tr1, exec pr1 s tr p s' r (tr1++tr) /\ trace_match pr1 pr2 tr1 tr2) ->
    permission_secure pr2 s p pre post.
Proof.
  unfold permission_secure; intros.
  specialize (H1 _ _ _ _ H3); cleanup.
  specialize (H _ _ _ _ H2 H1); intuition.
  eapply trace_secure_match; eauto.
Qed.


Theorem pre_impl_secure:
  forall T s (p: prog T) pr (pre pre': PermProg.state -> Prop) post,
    permission_secure pr s p pre' post ->
    (pre s -> pre' s) ->
    permission_secure pr s p pre post.
Proof.
  unfold permission_secure; intros.
  specialize (H0 H1); eauto.
Qed.

Theorem post_impl_secure:
  forall T s (p: prog T) pr (pre: PermProg.state -> Prop)
    (post post': PermProg.state -> PermProg.state -> T -> Prop),
    permission_secure pr s p pre post ->
    (forall s' tr tr' r,
       pre s ->
       exec pr s tr p s' (Finished r) tr' ->
       post s s' r ->
       post' s s' r) ->
    permission_secure pr s p pre post'.
Proof.
  unfold permission_secure; intros.
  specialize (H _ _ _ _ H1 H2); cleanup; eauto.
Qed. 

Theorem impl_secure:
  forall T s (p: prog T) pr (pre pre': PermProg.state -> Prop)
    (post post': PermProg.state -> PermProg.state -> T -> Prop),
    permission_secure pr s p pre' post ->
    (forall s' tr tr' r,
       pre' s ->
       exec pr s tr p s' (Finished r) tr' ->
       post s s' r ->
       post' s s' r) ->
    (pre s -> pre' s) ->
    permission_secure pr s p pre post'.
Proof.
  intros;
  eapply pre_impl_secure; eauto.
  eapply post_impl_secure; eauto.
Qed. 