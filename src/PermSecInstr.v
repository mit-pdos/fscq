Require Export PermSec.



Lemma read_secure:
  forall s pr a tb,
    disk s a = Some tb ->
    permission_secure pr s (Read a) (fun s s' r => s' = blocks_upd s r tb).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; simpl in *; cleanup.
  simpl; intuition.
Qed.

Lemma write_secure:
  forall pr s a i tb,
    blocks s i = Some tb ->
    permission_secure pr s (Write a i) (fun s s' _ => s' = disk_upd s a tb).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; simpl in *; cleanup.
  simpl; intuition.
Qed.


Lemma seal_secure:
  forall pr s t b,
    can_access pr t ->
    permission_secure pr s (Seal t b) (fun s s' r => s' = blocks_upd s r (t, b)).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; simpl in *; cleanup.
  simpl; intuition.
Qed.

Lemma unseal_secure:
  forall pr s i t b,
    can_access pr t ->
    blocks s i = Some (t, b) ->
    permission_secure pr s (Unseal i) (fun s s' r => s' = s /\ r = b).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; simpl in *; cleanup.
  simpl; intuition.
Qed.

Lemma ret_secure:
  forall T pr s (v: T),
    permission_secure pr s (Ret v) (fun s s' r => s' = s /\ r = v).
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; simpl in *; cleanup.
  simpl; intuition.
Qed.

Lemma run_secure:
  forall T s (p: prog T) pr pr' post,
    permission_secure pr' s p post ->
    permitted pr pr' ->
    permission_secure pr s (Run pr' p) post.
Proof.
  unfold permission_secure; intros.
  inv_exec_perm; simpl in *.
  specialize (trace_app H10); intros; cleanup.
  specialize (H _ _ _ _ H10); intuition.
  simpl; intuition.
  eapply trace_secure_permitted; eauto.
Qed.

Lemma bind_secure:
  forall T T' (p1: prog T) (p2: T -> prog T') pr s post
    (post2: state -> state -> T' -> Prop),
    permission_secure pr s p1 post ->
    (forall s' s'' tr tr' tr'' r r',
       exec pr s tr p1 s' (Finished r) tr' ->
       post s s' r ->
       exec pr s' tr' (p2 r) s'' (Finished r') tr'' ->
       post2 s' s'' r' ->
       post2 s s'' r') ->
    (forall s' tr tr' r,
       exec pr s tr p1 s' (Finished r) tr' ->
       post s s' r ->
       permission_secure pr s' (p2 r) post2) ->
    permission_secure pr s (Bind p1 p2) post2.
Proof.
  unfold permission_secure; intros.
  inv_exec_perm.
  specialize (trace_app H2); intros; cleanup.
  specialize (H _ _ _ _ H2); cleanup.
  specialize (trace_app H3); intros; cleanup.
  specialize (H1 _ _ _ _ H2 H4); cleanup.
  specialize (H1 _ _ _ _ H3); cleanup.
  intuition.
  apply trace_secure_app; auto.
  eauto.
Qed.


Lemma permission_drop_secure:
  forall s pr1 pr2 T (p: prog T) post,
    permission_secure pr1 s p post ->
    permitted pr2 pr1 ->
    (forall s' tr tr2 r, exec pr2 s tr p s' r (tr2++tr) ->
                      exists tr1, exec pr1 s tr p s' r (tr1++tr) /\ trace_match pr1 pr2 tr1 tr2) ->
    permission_secure pr2 s p post.
Proof.
  unfold permission_secure; intros.
  specialize (H1 _ _ _ _ H2); cleanup.
  specialize (H _ _ _ _ H1); intuition.
  eapply trace_secure_match; eauto.
Qed.

Theorem impl_secure:
  forall T s (p: prog T) pr
    (post post': PermProg.state -> PermProg.state -> T -> Prop),
    permission_secure pr s p post ->
    (forall s' tr tr' r,
       exec pr s tr p s' (Finished r) tr' ->
       post s s' r ->
       post' s s' r) ->
    permission_secure pr s p post'.
Proof.
  unfold permission_secure; intros.
  specialize (H _ _ _ _ H1); cleanup; eauto.
Qed. 