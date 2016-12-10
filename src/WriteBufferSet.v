Require Import CoopConcur.
Require Export WriteBuffer.
Require Import DiskReaders.
Import List.
Import ListNotations.

(** TODO: this file mixes generic theorems about lists (using NoDup
and incl) with theorems that should be about a generic Map expressed
as a functor but are instead written as theorems about a WriteBuffer,
along with some truly WriteBuffer specific theorems (eg, wb_rep_empty,
the main result here) *)

Definition wb_writes wb : list (addr * valu) :=
  fold_right (fun e acc =>
                match e with
                | (a, Written v) => (a, v) :: acc
                | (_, WbMissing) => acc
                end) nil (wb_entries wb).

Definition upd_all A AEQ V (m: @mem A AEQ V) (entries: list (A * V)) :=
  fold_right (fun (e:A * V) acc =>
                let (a, v) := e in
                upd acc a v) m entries.

Definition add_empty_rdr (ae: addr * valu) : addr * wr_set :=
  let (a, v) := ae in
  (a, (v, None)).

(* TODO; replace with a more efficient direct recursive
  implementation and prove equivalent to this *)
Definition upd_buffered_writes (d: DISK) (entries: list (addr * valu)) :=
  upd_all d (map add_empty_rdr entries).

(* convenient expression of the computational behavior of [upd_buffered_writes] *)
Lemma upd_buffered_writes_cons : forall vd entries a v,
    upd_buffered_writes vd ((a, v) :: entries) =
    upd (upd_buffered_writes vd entries) a (v, None).
Proof.
  reflexivity.
Qed.

Hint Resolve in_eq in_cons.
Hint Resolve SetoidList.InA_cons_hd SetoidList.InA_cons_tl.

Lemma eq_key_elt_eq : forall elt a a',
    a = a' ->
    @Map.eq_key_elt elt a a'.
Proof.
  intros.
  subst.
  reflexivity.
Qed.

Hint Resolve eq_key_elt_eq.

Theorem wb_writes_complete : forall wb a v,
    wb_get wb a = Written v ->
    In (a, v) (wb_writes wb).
Proof.
  intros.
  unfold wb_writes, wb_get, wb_entries in *.
  pose proof (MapFacts.elements_mapsto_iff wb a (Written v)).
  let H := fresh in
  destruct (Map.find a wb) eqn:H; subst; try congruence.
  assert (Map.MapsTo a (Written v) wb).
  apply MapFacts.find_mapsto_iff; congruence.
  intuition.

  induction (Map.elements wb); intros.

  inversion H0.

  inversion H0; subst.
  inversion H4; destruct a0.
  simpl in *; subst.
  simpl; auto.

  intuition.
  destruct a0 as [ ? [] ]; simpl; auto.
Qed.

Lemma setoid_ina : forall a l,
    SetoidList.InA (Map.eq_key_elt (elt:=wb_entry)) a l <->
    In a l.
Proof.
  induction l.
  split; inversion 1.

  split; intuition.
  inversion H; subst; eauto.
  destruct a, a0.
  inversion H3; simpl in *; subst; eauto.

  inversion H; subst; eauto.
Qed.

Lemma in_wb_writes_elements : forall wb a v,
    In (a, v) (wb_writes wb) ->
    In (a, Written v) (Map.elements wb).
Proof.
  unfold wb_writes, wb_entries; intros.
  induction (Map.elements wb); simpl in *; auto.
  destruct a0 as [ ? [] ]; simpl in *.
  intuition.
  inversion H0; subst; auto.
  intuition.
Qed.

Theorem wb_writes_complete' : forall wb a v,
    In (a, v) (wb_writes wb) ->
    wb_get wb a = Written v.
Proof.
  intros.

  apply in_wb_writes_elements in H.
  assert (Map.MapsTo a (Written v) wb).
  apply MapFacts.elements_mapsto_iff.
  apply setoid_ina.
  auto.
  unfold wb_get.
  erewrite Map.find_1; eauto.
Qed.

Lemma wb_get_empty : forall a,
    wb_get emptyWriteBuffer a = WbMissing.
Proof.
  auto.
Qed.

Hint Constructors NoDup.

Lemma NoDup_entries : forall wb,
    NoDup (map fst (wb_entries wb)).
Proof.
  intros.
  pose proof (Map.elements_3w wb).
  unfold wb_entries.
  generalize dependent (Map.elements wb); intros.
  induction H; cbn; auto.
  constructor; auto.
  intro.
  apply H.

  destruct x; simpl in *.
  clear H H0.
  induction l; simpl in *; intuition.
  destruct a; simpl in *; subst.
  constructor.
  reflexivity.

  inversion IHNoDupA; subst; auto.
Qed.

Lemma wb_entries_writes_subset : forall wb,
    incl (map fst (wb_writes wb))
         (map fst (wb_entries wb)).
Proof.
  unfold incl, wb_writes; intros.
  generalize dependent (wb_entries wb); intros.
  induction l; simpl in *; eauto.
  destruct a0.
  destruct w; simpl in *; intuition.
Qed.


Lemma incl_nil : forall A (l: list A),
    incl l nil ->
    l = nil.
Proof.
  unfold incl; destruct l; intros; auto.
  assert (In a []) by eauto.
  inversion H0.
Qed.

Lemma incl_not_in : forall A (l l': list A) a,
    incl l l' ->
    ~In a l' ->
    ~In a l.
Proof.
  unfold incl; intros.
  intuition.
Qed.

Theorem incl_trans : forall A (l l' l'' : list A),
    incl l l' ->
    incl l' l'' ->
    incl l l''.
Proof.
  firstorder.
Qed.

Lemma incl_cons : forall A l l' (a:A),
    incl (a::l) l' ->
    incl l l'.
Proof.
  unfold incl; simpl; intuition eauto.
Qed.

Hint Resolve incl_cons.

Lemma incl_converse : forall A (l l': list A),
    incl l l' ->
    (forall a, ~In a l' -> ~In a l).
Proof.
  firstorder.
Qed.

Lemma incl_remove : forall A l l' (a:A),
    incl (a::l) (a::l') ->
    incl l l'.
Proof.
  induction l; intros; eauto.
  unfold incl; simpl; intuition.
Abort.

Fixpoint remove_first A (decA: EqDec A) (a:A) l :=
  match l with
  | nil => nil
  | a'::l' => if decA a a' then l' else a' :: remove_first decA a l'
  end.

Lemma in_split_first : forall A (decA: EqDec A) l (a:A),
    In a l ->
    exists l1 l2, l = l1 ++ a :: l2 /\
                  ~In a l1.
Proof.
  induction l.
  inversion 1.
  inversion 1; subst.
  exists nil, l.
  intuition eauto.

  pose proof (IHl _ H0).
  repeat deex.
  destruct (decA a a0); subst.
  exists nil, (l1 ++ a0 :: l2).
  intuition.
  exists (a :: l1), l2.
  rewrite <- app_comm_cons; intuition.
  inversion H1; subst; intuition eauto.
Qed.

Lemma remove_first_app : forall A (decA: EqDec A) l l' (a: A),
    ~In a l ->
    remove_first decA a (l ++ l') = l ++ remove_first decA a l'.
Proof.
  induction l; intros; eauto.
  rewrite <- app_comm_cons.
  simpl.
  destruct (decA a0 a); subst.
  exfalso; eauto.
  rewrite IHl; eauto.
Qed.

Lemma remove_first_eq : forall A (decA: EqDec A) l (a:A),
    remove_first decA a (a::l) = l.
Proof.
  intros; simpl.
  destruct (decA a a); congruence.
Qed.

Lemma incl_in_cons : forall A l l' (a:A),
    incl l l' ->
    In a l' ->
    incl (a::l) l'.
Proof.
  unfold incl; intros.
  destruct H1; subst; eauto.
Qed.

Hint Resolve incl_in_cons.

Lemma incl_app_comm_r : forall A (l l' l'': list A),
    incl l (l' ++ l'') ->
    incl l (l'' ++ l').
Proof.
  unfold incl; intros.
  apply H in H0.
  apply in_app_or in H0.
  intuition auto using in_or_app.
Qed.

Lemma incl_app_single : forall A (l l' l'': list A) a,
    incl l (l' ++ a :: l'') ->
    incl l (a :: l' ++ l'').
Proof.
  unfold incl; intros.
  apply H in H0.
  apply in_app_or in H0.
  intuition.
  rewrite app_comm_cons.
  destruct H1; subst;
    intuition auto using in_or_app.
Qed.

Lemma incl_remove' : forall A (decA: EqDec A) l l' (a:A),
    ~In a l ->
    incl (a::l) l' ->
    incl l (remove_first decA a l').
Proof.
  induction l; intros; eauto.
  unfold incl; inversion 1.
  assert (In a0 l') as Ina0 by eauto.
  pose proof (in_split_first decA _ _ Ina0); repeat deex.
  rewrite remove_first_app by eauto.
  rewrite remove_first_eq.
  clear Ina0.
  apply incl_app_single in H0.
  assert (incl (a0 :: l) (a0 :: l1 ++ l2)) as Hincl by eauto.
  apply IHl in Hincl.
  rewrite remove_first_eq in Hincl.
  apply incl_in_cons; eauto.
  destruct (decA a a0); subst.
  exfalso; eauto.

  assert (In a (a0 :: l1 ++ l2)) as Hin by eauto.
  destruct Hin; congruence.
  intuition eauto.
Qed.

Lemma count_occ_app : forall A (decA: EqDec A) l l' (a:A),
    count_occ decA (l ++ l') a =
    count_occ decA l a + count_occ decA l' a.
Proof.
  induction l; cbn; intros; eauto.
  destruct (decA a a0); subst; eauto.
  rewrite IHl; auto.
Qed.

Require Import Arith.

Lemma count_occ_remove_first : forall A (decA: EqDec A) (l: list A) a,
    In a l ->
    count_occ decA (remove_first decA a l) a < count_occ decA l a.
Proof.
  intros.
  apply in_split_first in H; auto.
  repeat deex.
  rewrite remove_first_app; auto.
  rewrite remove_first_eq.
  rewrite ?count_occ_app, ?count_occ_cons_eq by auto.
  apply plus_lt_compat_l.
  auto.
Qed.

Require Import Omega.

Lemma count_occ_in : forall A (decA : EqDec A) l (a:A),
    In a l ->
    1 <= count_occ decA l a.
Proof.
  intros.
  apply in_split_first in H; auto.
  repeat deex.
  rewrite count_occ_app.
  rewrite count_occ_cons_eq by auto.
  omega.
Qed.

Lemma count_occ_not_in : forall A (decA : EqDec A) l (a:A),
    ~In a l ->
    count_occ decA l a = 0.
Proof.
  intros.
  induction l; eauto.
  simpl; destruct (decA a0 a); subst; eauto.
  exfalso; eauto.
Qed.

Lemma incl_nodup_count_occ : forall A (decA: EqDec A) (l l': list A),
    NoDup l ->
    incl l l' ->
    (forall a, count_occ decA l a <= count_occ decA l' a).
Proof.
  induction l; intros; simpl.
  apply le_0_n.
  destruct (decA a a0); subst; eauto.
  assert (In a0 l') by eauto.
  inversion H; subst; eauto.
  pose proof (incl_remove' decA ltac:(eassumption) ltac:(eassumption)).
  apply IHl with (a := a0) in H2; auto.
  rewrite count_occ_not_in in * by eauto.
  pose proof (count_occ_in decA _ _ H1).
  omega.

  inversion H; subst; eauto.
Qed.

Lemma ina_key : forall a l v,
    (SetoidList.InA (Map.eq_key (elt:=wb_entry)) (a, v) l) <->
    (In a (map fst l)).
Proof.
  induction l; simpl.
  split; inversion 1.

  split; inversion 1; subst.
  destruct a0; simpl in *.
  inversion H1; subst; eauto.
  right; eapply IHl; eauto.

  constructor.
  reflexivity.
  constructor 2.
  apply IHl; auto.
Qed.

Lemma nodup_keys : forall l,
    SetoidList.NoDupA (Map.eq_key (elt:=wb_entry)) l ->
    NoDup (map fst l).
Proof.
  induction l; simpl; intros; eauto.
  destruct a; simpl.
  inversion H; subst.
  constructor; eauto.
  intro.
  eapply ina_key in H0; eauto.
Qed.

Lemma NoDup_writes : forall wb,
    NoDup (map fst (wb_writes wb)).
Proof.
  intros.
  pose proof (Map.elements_3w wb).
  apply nodup_keys in H.

  (* generalize inductive hypothesis *)
  assert (NoDup (map fst (wb_writes wb)) /\
          (forall a, In a (map fst (wb_writes wb)) ->
                     In a (map fst (wb_entries wb)))).

  unfold wb_writes, wb_entries.
  generalize dependent (Map.elements wb).

  induction l; simpl; auto; intros.
  inversion H; subst.
  destruct a as [ ? [] ]; simpl in *;
    intuition auto.

  intuition.
Qed.

Theorem in_nodup_split : forall A l (a:A),
    NoDup l ->
    In a l ->
    exists l1 l2,
      l = l1 ++ a :: l2 /\
      ~In a l1 /\
      ~In a l2.
Proof.
  intros.
  induction l.
  inversion H0.
  inversion H; subst; clear H.
  destruct H0; subst.
  - exists nil, l; intuition.
  - intuition; repeat deex.
    exists (a0 :: l1), l2; intuition.
    inversion H0; subst; eauto.
Qed.

Theorem in_nodup_map_split : forall A B (f: A -> B) l (a:A),
    NoDup (map f l) ->
    In a l ->
    exists l1 l2,
      l = l1 ++ a :: l2 /\
      ~In (f a) (map f l1) /\
      ~In (f a) (map f l2).
Proof.
  intros.
  induction l.
  inversion H0.
  destruct H0; subst.
  - exists nil, l; intuition.
    inversion H; subst; intuition.
  - inversion H; subst; intuition.
    repeat deex.
    exists (a0 :: l1), l2; intuition.
    destruct H2; subst; eauto.
    rewrite ?map_cons, ?map_app in *; simpl in *; intuition eauto.
    rewrite H2 in *.
    rewrite app_comm_cons in H at 1.
    apply NoDup_remove in H; intuition eauto.
    exfalso; eauto.
Qed.

Theorem upd_all_app_ignore : forall A AEQ V l1 l2
                                    (d: @mem A AEQ V) (a:A),
    ~In a (map fst l2) ->
    upd_all d (l1 ++ l2) a = upd_all d l1 a.
Proof.
  unfold upd_all.
  induction l1; cbn; intros.
  induction l2; cbn; auto.
  destruct a0.
  apply not_in_cons in H; intuition.
  autorewrite with upd; auto.
  destruct a.
  destruct (AEQ a a0); subst;
    autorewrite with upd;
    auto.
Qed.

Corollary upd_all_not_in : forall A AEQ V l
                                  (d: @mem A AEQ V) (a:A),
    ~In a (map fst l) ->
    upd_all d l a = d a.
Proof.
  intros.
  replace l with (nil ++ l) by reflexivity.
  rewrite upd_all_app_ignore; auto.
Qed.

Theorem upd_all_app_last : forall A AEQ V l
                                  (d: @mem A AEQ V)
                                  a v,
    ~In a (map fst l) ->
    upd_all d (l ++ [ (a, v) ]) a = Some v.
Proof.
  unfold upd_all.
  induction l; cbn; intros.
  autorewrite with upd; auto.

  destruct a.
  destruct (AEQ a a0); subst.

  autorewrite with upd; auto.
  apply not_in_cons in H; intuition.
  autorewrite with upd; auto.
Qed.

Lemma app_cons_to_app : forall A (l l': list A) a,
    l ++ a :: l' = l ++ [a] ++ l'.
Proof.
  auto.
Qed.

Hint Resolve in_map.

Lemma not_in_map : forall A B (f: A -> B)
                          (finj: forall a a', f a = f a' -> a = a')
                          l a,
    ~In a l ->
    ~In (f a) (map f l).
Proof.
  intros.
  contradict H.
  induction l.
  inversion H.
  inversion H.
  apply finj in H0; subst; auto.
  eauto.
Qed.

Lemma nodup_map : forall A B (f: A -> B) l,
    (forall a a', f a = f a' -> a = a') ->
    NoDup l ->
    NoDup (map f l).
Proof.
  intros.
  induction l; intros; cbn; auto.
  inversion H0; subst.
  constructor; auto.
  apply not_in_map; auto.
Qed.

Theorem upd_all_in : forall A AEQ V (d: @mem A AEQ V) l a v,
    NoDup (map fst l) ->
    In (a, v) l ->
    upd_all d l a = Some v.
Proof.
  intros.

  pose proof (in_nodup_map_split _ _ _ H H0); repeat deex.
  rewrite app_cons_to_app in *.
  rewrite app_assoc.
  rewrite upd_all_app_ignore; auto.
  rewrite upd_all_app_last; auto.
Qed.

Lemma In_add_empty_rdr : forall a v wb,
    In (a, v) (wb_writes wb) ->
    In (a, (v, None)) (map add_empty_rdr (wb_writes wb)).
Proof.
  intros.
  replace (a, (v, None)) with (add_empty_rdr (a, v)) by reflexivity.
  apply in_map; auto.
Qed.

Lemma addrs_add_empty_rdr : forall wb,
    map fst (map add_empty_rdr (wb_writes wb)) =
    map fst (wb_writes wb).
Proof.
  intros.
  rewrite map_map.
  unfold add_empty_rdr.
  induction (wb_writes wb); simpl; eauto.
  destruct a; simpl; congruence.
Qed.

Hint Resolve In_add_empty_rdr.

Lemma wb_get_missing' : forall wb a,
    wb_get wb a = WbMissing ->
    (forall v, ~In (a, v) (wb_writes wb)).
Proof.
  intros.
  intro.
  apply wb_writes_complete' in H0.
  congruence.
Qed.

Lemma in_map : forall A (l: list A) B (f: A -> B) b,
    In b (map f l) ->
    exists a, b = f a /\
              In a l.
Proof.
  induction l; simpl; intros.
  inversion H.
  intuition eauto.
  edestruct IHl; eauto.
  intuition eauto.
Qed.

Lemma wb_get_missing : forall wb a,
    wb_get wb a = WbMissing ->
    ~In a (map fst (wb_writes wb)).
Proof.
  intros; intro.
  apply in_map in H0; deex.
  destruct a0; simpl in *.
  pose proof (wb_get_missing' _ _ H).
  intuition eauto.
Qed.

Lemma hide_readers_upd_buffered_writes : forall entries d,
    hide_readers (upd_buffered_writes d entries) =
    upd_all (hide_readers d) entries.
Proof.
  unfold upd_buffered_writes.
  induction entries; intros.
  reflexivity.
  destruct a as [a v]; simpl.
  extensionality a'.
  destruct (nat_dec a a'); subst.
  unfold hide_readers; autorewrite with upd; auto.
  rewrite <- IHentries.
  unfold hide_readers; autorewrite with upd; auto.
Qed.

Theorem wb_rep_empty : forall d wb vd,
    wb_rep (hide_readers d) wb vd ->
    wb_rep (hide_readers (upd_buffered_writes d (wb_writes wb))) emptyWriteBuffer vd.
Proof.
  unfold wb_rep; intros.
  specialize (H a).
  rewrite wb_get_empty.
  rewrite hide_readers_upd_buffered_writes.
  let H := fresh in
  destruct (wb_get wb a) eqn:H; intuition.
  apply wb_writes_complete in H0.
  pose proof (NoDup_writes wb).
  erewrite upd_all_in; eauto.

  apply wb_get_missing in H0.
  rewrite upd_all_not_in; auto.
Qed.

Definition upd_all' A AEQ V (m: @mem A AEQ V) (entries: list (A*V)) :=
  fold_left (fun acc (e: A*V) => let (a, v) := e in upd acc a v) entries m.

Lemma upd_all'_not_in : forall A AEQ V entries (m: @mem A AEQ V) a,
    ~In a (map fst entries) ->
    upd_all' m entries a = m a.
Proof.
  induction entries; simpl in *; intuition auto; simpl in *.
  rewrite IHentries; auto.
  rewrite upd_ne by auto; auto.
Qed.

Hint Rewrite upd_all'_not_in using (solve [ auto ]) : upd.

Lemma upd_all'_in_mems : forall A AEQ V entries (m m': @mem A AEQ V) a,
    In a (map fst entries) ->
    NoDup (map fst entries) ->
    upd_all' m entries a  = upd_all' m' entries a.
Proof.
  induction entries; simpl; intros.
  destruct H.

  destruct a as [a v].
  inversion H0; subst.
  simpl in *.
  intuition auto; subst.
  autorewrite with upd; auto.
Qed.

Lemma upd_all_eq_upd_all' : forall A AEQ V (m: @mem A AEQ V) entries,
    NoDup (map fst entries) ->
    upd_all m entries = upd_all' m entries.
Proof.
  induction entries; simpl; intuition auto.
  destruct a as [a v]; simpl in *.
  inversion H; subst; intuition auto.
  extensionality a'.
  destruct (AEQ a a'); subst;
    autorewrite with upd; auto.
  rewrite H0.
  destruct (in_dec AEQ a' (map fst entries));
    autorewrite with upd; auto.
  apply upd_all'_in_mems; auto.
Qed.