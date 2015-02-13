Require Import Word.
Require Import Ascii.
Require Import String.
Require Import Dir.
Require Import Omega.

Definition ascii2byte (a : ascii) : word 8 :=
  match a with
  | Ascii a1 a2 a3 a4 a5 a6 a7 a8 =>
    WS a1 (WS a2 (WS a3 (WS a4 (WS a5 (WS a6 (WS a7 (WS a8 WO)))))))
  end.

Definition byte2ascii (b : word 8) : ascii :=
  match b with
  | WS a1 b1 => match b1 with
    | WS a2 b2 => match b2 with
      | WS a3 b3 => match b3 with
        | WS a4 b4 => match b4 with
          | WS a5 b5 => match b5 with
            | WS a6 b6 => match b6 with
              | WS a7 b7 => match b7 with
                | WS a8 _ => Ascii a1 a2 a3 a4 a5 a6 a7 a8
                | WO => Ascii.zero
                end
              | WO => Ascii.zero
              end
            | WO => Ascii.zero
            end
          | WO => Ascii.zero
          end
        | WO => Ascii.zero
        end
      | WO => Ascii.zero
      end
    | WO => Ascii.zero
    end
  | WO => Ascii.zero
  end.

Theorem ascii2byte2ascii : forall a, byte2ascii (ascii2byte a) = a.
Proof.
  destruct a; reflexivity.
Qed.

Theorem byte2ascii2byte : forall b, ascii2byte (byte2ascii b) = b.
Proof.
  intros.
  shatter_word b.
  reflexivity.
Qed.

Fixpoint name2padstring (nbytes : nat) (name : word (nbytes * 8)) : string.
  destruct nbytes.
  refine EmptyString.
  refine (String (byte2ascii (@split1 8 (nbytes * 8) name))
                 (name2padstring nbytes (@split2 8 (nbytes * 8) name))).
Defined.

Fixpoint padstring2name (nbytes : nat) (s : string) : word (nbytes * 8).
  destruct nbytes.
  refine ($0).
  destruct s.
  refine ($0).
  refine (combine (ascii2byte a) (padstring2name nbytes s)).
Defined.

Opaque ascii2byte byte2ascii split1 split2.

Theorem name2padstring2name : forall nbytes (name : word (nbytes * 8)),
  padstring2name nbytes (name2padstring nbytes name) = name.
Proof.
  induction nbytes; simpl; intros.
  rewrite word0. reflexivity.
  rewrite byte2ascii2byte. rewrite IHnbytes. rewrite combine_split. reflexivity.
Qed.

Theorem padstring2name2padstring : forall nbytes (s : string),
  length s = nbytes -> name2padstring nbytes (padstring2name nbytes s) = s.
Proof.
  induction nbytes; simpl; intros.
  destruct s; simpl in *; congruence.
  destruct s; simpl in *; try congruence.
  rewrite split1_combine.
  rewrite split2_combine.
  rewrite IHnbytes by congruence.
  rewrite ascii2byte2ascii.
  reflexivity.
Qed.

Theorem name2padstring_length : forall nbytes name,
  length (name2padstring nbytes name) = nbytes.
Proof.
  induction nbytes; simpl; eauto.
Qed.

Fixpoint string_pad nbytes (s : string) :=
  match nbytes with
  | O => EmptyString
  | S nbytes' =>
    match s with
    | EmptyString => String zero (string_pad nbytes' EmptyString)
    | String a s' => String a (string_pad nbytes' s')
    end
  end.

Fixpoint string_unpad (s : string) :=
  match s with
  | EmptyString => EmptyString
  | String a s' =>
    if ascii_dec a zero then EmptyString else String a (string_unpad s')
  end.

Theorem string_pad_length : forall nbytes s,
  length (string_pad nbytes s) = nbytes.
Proof.
  induction nbytes; simpl.
  reflexivity.
  destruct s; simpl; eauto.
Qed.

Inductive nozero : string -> Prop :=
  | NoZeroEmpty : nozero EmptyString
  | NoZeroCons : forall a s, a <> zero -> nozero s -> nozero (String a s).

Theorem string_pad_unpad : forall nbytes s,
  length s <= nbytes -> nozero s -> string_unpad (string_pad nbytes s) = s.
Proof.
  induction nbytes; simpl; intros.
  destruct s; simpl in *; try congruence; omega.
  destruct s; simpl in *; try congruence.
  inversion H0.
  destruct (ascii_dec a zero); try congruence.
  rewrite IHnbytes; eauto.
  omega.
Qed.

Inductive zerostring : string -> Prop :=
  | ZeroEmpty : zerostring EmptyString
  | ZeroCons : forall s, zerostring s -> zerostring (String zero s).

Inductive wellformedpadstring : string -> Prop :=
  | WFSzero : forall s, zerostring s -> wellformedpadstring s
  | WFScons : forall s c, wellformedpadstring s -> c <> zero -> wellformedpadstring (String c s).

Theorem pad_zero_string : forall s, wellformedpadstring (String zero s) ->
  s = string_pad (length s) EmptyString.
Proof.
  intros.
  inversion H; clear H; try congruence.
  clear H1 s0.
  inversion H0; clear H0; subst.
  induction s; simpl.
  reflexivity.
  inversion H1; subst.
  f_equal.
  apply IHs; auto.
Qed.

Theorem string_unpad_pad : forall s nbytes, length s = nbytes ->
  wellformedpadstring s -> string_pad nbytes (string_unpad s) = s.
Proof.
  induction s; intros; subst; simpl in *.
  reflexivity.
  destruct (ascii_dec a zero); subst.
  - f_equal.
    rewrite <- pad_zero_string; auto.
  - inversion H0.
    inversion H; congruence.
    rewrite IHs; auto.
Qed.

Definition string2name nbytes s := padstring2name nbytes (string_pad nbytes s).
Definition name2string nbytes name := string_unpad (name2padstring nbytes name).

Theorem string2name2string : forall nbytes s, length s <= nbytes -> nozero s ->
  name2string nbytes (string2name nbytes s) = s.
Proof.
  unfold string2name, name2string.
  intros.
  rewrite padstring2name2padstring by apply string_pad_length.
  rewrite string_pad_unpad; eauto.
Qed.

Theorem name2string2name : forall nbytes name, wellformedpadstring (name2padstring nbytes name)
  -> string2name nbytes (name2string nbytes name) = name.
Proof.
  unfold string2name, name2string.
  intros.
  rewrite string_unpad_pad; auto.
  rewrite name2padstring2name; auto.
  apply name2padstring_length.
Qed.
