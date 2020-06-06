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
  - apply /typed_var => // ?.
    by rewrite -Hnth H.
  - apply /typed_abs; eauto.
    by apply /IHtyped => ? [ | ? ] /=.
  - apply /typed_let; eauto.
    by apply /IHtyped => ? [ | ? ] /=.
Qed.

Lemma typed_subst G t T :
  typed G t T ->
  forall s G',
  ( forall x T, (forall d, nth d G x = T) ->
    exists (L : seq _), forall s',
    (forall x, exists y, s' x = typ_fvar y /\ y \notin L) ->
    typed G' (s x) (typ_open s' T) ) ->
  typed G' t.[s] T.
Proof.
  induction 1 => /= s0 G' Hnth; eauto.
  - move: (Hnth _ _ H) => [ L Hs' ].
    rewrite -(env_subst_fvar G') -(typ_subst_fvar T)
    -(env_subst_ext (fun x => if x <= maximum (env_enum_fv G' (typ_enum_fv T L)) then typ_fvar x else s (x - maximum (env_enum_fv G' (typ_enum_fv T L))).-1)) => [ | ? Hin ].
    + rewrite -(typ_subst_ext (fun x => if x <= maximum (env_enum_fv G' (typ_enum_fv T L)) then typ_fvar x else s (x - maximum (env_enum_fv G' (typ_enum_fv T L))).-1)) => [ | ? Hin ].
      { rewrite -(typ_open_ext (typ_subst (fun x => if x <= maximum (env_enum_fv G' (typ_enum_fv T L)) then typ_fvar x else s (x - maximum (env_enum_fv G' (typ_enum_fv T L))).-1) \o (typ_fvar \o addn (maximum (env_enum_fv G' (typ_enum_fv T L))).+1))) => [ | ? /typ_bv_subst_elim [ ? | [ z ] ] /= ].
        - rewrite -typ_subst_open_distr => [ | z ? ? ].
          + apply /typed_subst_typ => [ | z ? ].
            * apply Hs' => y. repeat eexists. apply /negP => Hin.
              have : (maximum (env_enum_fv G' (typ_enum_fv T L))).+1 + y <= (maximum (env_enum_fv G' (typ_enum_fv T L))).
              { apply /maximum_sup.
                by rewrite env_enum_fv_inE_aux typ_enum_fv_inE_aux Hin !orbT. }
              by rewrite addSn ltnNge leq_addr.
            * case (z <= maximum (env_enum_fv G' (typ_enum_fv T L))) => //. exact /H0.
          + case (z <= maximum (env_enum_fv G' (typ_enum_fv T L))) => //. by rewrite H0.
        - by rewrite addSn ltnNge leq_addr /= subSKn addnC addnK.
        - case (z <= maximum (env_enum_fv G' (typ_enum_fv T L))) => //. by rewrite H0. }
      by rewrite maximum_sup // env_enum_fv_inE_aux typ_enum_fv_inE_aux Hin !orbT.
    + by rewrite maximum_sup // env_enum_fv_inE_aux typ_enum_fv_inE_aux Hin.
  - apply /typed_abs; eauto.
    apply /IHtyped => [ [ ? /(_ (typ_fvar 0)) /= -> | ? ? /= /Hnth [ L ? ] ] ].
    + exists [::] => ? Hs. apply /typed_var => //= x. by case (Hs x) => ? [ -> ].
    + exists L => ? ?. apply /typed_rename; eauto.
  - apply /typed_let; eauto.
    apply /IHtyped => [ [ ? /(_ (typ_fvar 0)) /= -> | ? ? /= /Hnth [ L' ? ] ] ].
    + exists L => ? Hs. apply /typed_var => //= x. by case (Hs x) => ? [ -> ].
    + exists L' => ? ?. apply /typed_rename; eauto.
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
    move => [ ? /(_ (typ_fvar 0)) <- /= | /= ? ? ? ]; exists [::] => ? Hs.
    + rewrite -(typ_open_ext typ_bvar) ?typ_open_bvar => // ?. by rewrite H7.
    + apply /typed_var => // x. by case (Hs x) => ? [ -> ].
  - apply /typed_subst; eauto.
    move => [ ? /(_ (typ_fvar 0)) <- /= | /= ? ? ? ]; eauto.
    exists [::] => ? Hs.
    apply /typed_var => // x. by case (Hs x) => ? [ -> ].
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
  - move: (H1 (typ_fvar 0)).
    by rewrite -(H1 (typ_bvar 0)) !nth_default.
  - move: (IHt1 _ H3) => [ /((canonical_arrow _ _ _)^~H3) [ ? -> ] | [ ? ? ] ]; eauto.
    move: (IHt2 _ H5) => [ ? | [ ? ? ] ]; eauto.
  - case (IHt (typ_open (typ_fvar \o addn (maximum L).+1) T1)) => [ | ? | [ ] ]; eauto.
    apply H3 => x. repeat eexists.
    apply /negP => /maximum_sup.
    by rewrite addSn ltnNge leq_addr.
Qed.
