Require Import List Relations.
Require Import Types Term Typing.
Require Import Autosubst.Autosubst.

Lemma typed_rename G t T :
  typed G t T ->
  forall G' r,
  (forall x T, nth_error G x = Some T -> nth_error G' (r x) = Some T) ->
  typed G' (rename r t) T.
Proof.
  induction 1; simpl; eauto.
  intros ? ? Hren. constructor. apply IHtyped.
  intros [ ]; eauto.
Qed.

Lemma typed_subst G t T :
  typed G t T ->
  forall s G',
  (forall x T, nth_error G x = Some T -> typed G' (s x) T) ->
  typed G' (t.[s]) T.
Proof.
  induction 1; simpl; eauto.
  intros ? ? Hs. constructor. apply IHtyped.
  unfold up. intros [ ]; simpl; inversion 1; eauto.
  apply typed_rename with (G := G'); eauto.
Qed.

Lemma subject_reduction t t' :
  cbv t t' ->
  forall G T, typed G t T ->
  typed G t' T.
Proof.
  induction 1; inversion 1; subst; eauto.
  inversion H4. subst.
  apply typed_subst with (G := T1 :: G); eauto.
  intros []; simpl; inversion 1; subst; eauto.
Qed.

Lemma normal_arrow v T1 T2 :
  value v ->
  typed nil v (typ_arrow T1 T2) ->
  exists t, v = trm_abs t.
Proof. inversion 1. eauto. Qed.

Lemma progress G t T :
  typed G t T ->
  G = nil ->
  value t \/ exists t', cbv t t'.
Proof.
  induction 1; intros; subst; eauto.
  - destruct x; inversion H.
  - destruct IHtyped1 as [ | [ ] ]; eauto.
    edestruct normal_arrow; eauto. subst.
    destruct IHtyped2 as [ | [ ] ]; eauto.
Qed.

Theorem type_safety t t' T :
  typed nil t T ->
  clos_refl_trans_1n _ cbv t t' ->
  value t' \/ exists t'', cbv t' t''.
Proof.
  induction 2.
  - eapply progress; eauto.
  - apply IHclos_refl_trans_1n.
    eapply subject_reduction; eauto.
Qed.