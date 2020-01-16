From mathcomp Require Import all_ssreflect.
Require Import Types Term Typing.
Require Import Autosubst.Autosubst.

Lemma typed_rename G t T :
  typed G t T ->
  forall G' r,
  (forall d x, nth d G x = nth d G' (r x)) ->
  typed G' (rename r t) T.
Proof.
  induction 1 => /= ? ? Hnth; eauto.
  - apply /typed_var => ?.
    by rewrite -Hnth H.
  - by apply /typed_abs /IHtyped => ? [ | ? ] /=.
  - apply /typed_let; eauto.
    by apply /IHtyped2 => ? [ | ? ] /=.
Qed.

Lemma typed_subst G t T :
  typed G t T ->
  forall s G',
  (forall x T, (forall d, nth d G x = T) -> typed G' (s x) T) ->
  typed G' t.[s] T.
Proof.
  induction 1 => /= ? ? Hnth; eauto.
  - apply /typed_abs /IHtyped => [ [ ? /(_ (typ_fvar 0)) /= -> | ? ? Hnth' ] /= ].
    + exact /typed_var.
    + exact /(typed_rename _ _ _ (Hnth _ _ Hnth')).
  - apply /typed_let; eauto.
    apply /IHtyped2 => [ [ ? /(_ (typ_fvar 0)) /= -> | ? ? Hnth' ] /= ].
    + exact /typed_var.
    + exact /(typed_rename _ _ _ (Hnth _ _ Hnth')).
Qed.

Lemma subject_reduction t t' :
  cbv t t' ->
  forall G T,
  typed G t T ->
  typed G t' T.
Proof.
  induction 1; inversion 1; subst; eauto.
  - inversion H4. subst.
    apply /typed_subst; eauto.
    move => [ ? /(_ (typ_fvar 0)) <- // | /= ? ? ? ]; eauto.
  - apply /typed_subst; eauto.
    move => [ ? /(_ (typ_fvar 0)) <- // | /= ? ? ? ]; eauto.
Qed.

Lemma canonical_arrow v T1 T2 :
  value v ->
  typed nil v (typ_arrow T1 T2) ->
  exists t, v = trm_abs t.
Proof. inversion 1; eauto. Qed.

Lemma progress t : forall T,
  typed [::] t T ->
  value t \/ exists t', cbv t t'.
Proof.
  induction t; inversion 1; subst; eauto.
  - move: (H2 (typ_fvar 0)).
    by rewrite -(H2 (typ_bvar 0)) !nth_default.
  - move: (IHt1 _ H3) => [ /((canonical_arrow _ _ _)^~H3) [ ? -> ] | [ ? ? ] ]; eauto.
    move: (IHt2 _ H5) => [ ? | [ ? ? ] ]; eauto.
  - move: (IHt _ H3) => [ ? | [ ? ? ] ]; eauto.
Qed.
