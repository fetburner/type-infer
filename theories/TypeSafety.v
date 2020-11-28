From mathcomp Require Import all_ssreflect.
Require Import Util Types Term Typing.

Lemma typed_rename M G t T :
  typed M G t T ->
  forall G' r,
  (forall d x, nth d G x = nth d G' (r x)) ->
  typed M G' (rename r t) T.
Proof.
  induction 1 => /= ? ? Hnth; eauto.
  - apply /typed_var => // ?.
    by rewrite -Hnth H.
  - apply /typed_abs; eauto.
    by apply /IHtyped => ? [ | ? ] /=.
  - apply /typed_let; eauto.
    + by rewrite value_rename.
    + by apply /IHtyped => ? [ | ? ] /=.
Qed.

Lemma typed_subst M G t T :
  typed M G t T ->
  forall s G',
  ( forall x T, (forall d, nth d G x = T) ->
    exists (L : seq _), forall s',
    (forall x, exists2 y, s' x = typ_fvar y & y \notin L) ->
    typed M G' (s x) (typ_open s' T) ) ->
  typed M G' (subst s t) T.
Proof.
  induction 1 => /= s0 G' Hnth; eauto.
  - move: (Hnth _ _ H) => [ L Hs' ].
    rewrite -(env_subst_fvar M) -(env_subst_fvar G') -(typ_subst_fvar T)
    -!(env_subst_ext (fun x => if x <= maximum (env_enum_fv M (env_enum_fv G' (typ_enum_fv T L))) then typ_fvar x else s (x - maximum (env_enum_fv M (env_enum_fv G' (typ_enum_fv T L)))).-1) typ_fvar) => [ | ? Hin | ? Hin ].
    + rewrite -(typ_subst_ext (fun x => if x <= maximum (env_enum_fv M (env_enum_fv G' (typ_enum_fv T L))) then typ_fvar x else s (x - maximum (env_enum_fv M (env_enum_fv G' (typ_enum_fv T L)))).-1)) => [ | ? Hin ].
      { rewrite -(typ_open_ext (typ_subst (fun x => if x <= maximum (env_enum_fv M (env_enum_fv G' (typ_enum_fv T L))) then typ_fvar x else s (x - maximum (env_enum_fv M (env_enum_fv G' (typ_enum_fv T L)))).-1) \o (typ_fvar \o addn (maximum (env_enum_fv M (env_enum_fv G' (typ_enum_fv T L)))).+1))) => [ | ? /typ_bv_subst_elim [ ? | [ z ] ] /= ].
        - rewrite -typ_subst_open_distr => [ | z ? ? ].
          + apply /typed_subst_typ => [ | z ? ].
            * apply Hs' => y. repeat eexists. apply /negP => Hin.
              have : (maximum (env_enum_fv M (env_enum_fv G' (typ_enum_fv T L)))).+1 + y <= (maximum (env_enum_fv M (env_enum_fv G' (typ_enum_fv T L)))).
              { apply /maximum_sup.
                by rewrite !env_enum_fv_inE_aux typ_enum_fv_inE_aux Hin !orbT. }
              by rewrite addSn ltnNge leq_addr.
            * by rewrite 3!fun_if /= H0 if_same.
          + by rewrite 3!fun_if /= H0 if_same.
        - by rewrite addSn ltnNge leq_addr /= subSKn addnC addnK.
        - by rewrite 3!fun_if /= H0 if_same. }
      by rewrite maximum_sup // !env_enum_fv_inE_aux typ_enum_fv_inE_aux Hin !orbT.
    + by rewrite maximum_sup // !env_enum_fv_inE_aux typ_enum_fv_inE_aux Hin !orbT.
    + by rewrite maximum_sup // !env_enum_fv_inE_aux typ_enum_fv_inE_aux Hin.
  - apply /typed_abs; eauto.
    apply /IHtyped => [ [ ? /(_ (typ_fvar 0)) /= -> | ? ? /= /Hnth [ L ? ] ] ].
    + exists [::] => ? Hs. apply /typed_var => //= x. by case (Hs x) => ? ->.
    + exists L => ? ?. apply /typed_rename; eauto.
  - apply /typed_let; eauto.
    + exact /value_subst.
    + apply /IHtyped => [ [ ? /(_ (typ_fvar 0)) /= -> | ? ? /= /Hnth [ L' ? ] ] ].
      * exists L => ? Hs. apply /typed_var => //= x. by case (Hs x) => ? ->.
      * exists L' => ? ?. apply /typed_rename; eauto.
Qed.

Corollary typed_subst_single M G t t0 T T0 :
  typed M (T0 :: G) t T ->
  forall (L : seq _),
  (forall s',
    (forall x, exists2 y, s' x = typ_fvar y & y \notin L) ->
    typed M G t0 (typ_open s' T0)) ->
  typed M G (subst (scons t0 var) t) T.
Proof.
  move => /typed_subst Hsubst ? ?.
  apply /Hsubst => [ [ ? /(_ typ_unit) <- /= | /= ? ? ? ] ]; eauto.
  exists [::] => ? Hs.
  apply /typed_var => // x.
  by case (Hs x) => ? ->.
Qed.

Lemma preservation :
  forall H M G,
  size H = size M ->
  (forall i, typed M G (nth trm_unit H i) (nth typ_unit M i)) ->
  forall t H' t',
  cbv H t H' t' ->
  forall T,
  typed M G t T ->
  exists M', typed M' G t' T /\
  (forall x T, (forall d, nth d M x = T) -> forall d, nth d M' x = T) /\
  size H' = size M' /\
  (forall i, typed M' G (nth trm_unit H' i) (nth typ_unit M' i)).
Proof.
  induction 3; inversion 1; subst; eauto.
  - inversion H7. subst.
    exists M. repeat split; eauto.
    apply /(typed_subst_single _ _ _ _ _ _ H11 [::]) => ? Hs.
    rewrite typ_open_bvar_eq => // ?.
    by rewrite H10.
  - move: (IHcbv _ H7) => [ M' [ ? [ ? [ ? ? ] ] ] ].
    exists M'. repeat split; eauto.
    apply /typed_app; eauto.
    apply /(typed_weaken_store M); eauto.
  - move: (IHcbv _ H10) => [ M' [ ? [ ? [ ? ? ] ] ] ].
    exists M'. repeat split; eauto.
    apply /typed_app; eauto.
    apply /(typed_weaken_store M); eauto.
  - have ? : forall x T,
      (forall d, nth d M x = T) ->
      (forall d, nth d (rcons M T0) x = T).
    { move => x T Hnth d.
      by move: nth_rcons (leqP (size M) x)
        (Hnth (if x == size M then T0 else d)) => -> [ /(nth_default _) -> | ]. }
    exists (rcons M T0).
    (repeat split; eauto) => [ | | l ].
    + apply /typed_loc => /= [ | ? ].
      * apply /typed_closed. eauto.
      * by rewrite nth_rcons H0 ltnn eqxx.
    + by rewrite !size_rcons H0.
    + rewrite !nth_rcons -H0.
      case (ltngtP (size H) l) => ? //;
      apply /(typed_weaken_store M); eauto.
  - move: (IHcbv _ H6) => [ ? [ ? [ ? [ ? ? ] ] ] ]. eauto 6.
  - inversion H6. subst.
    rewrite -(H2 trm_unit) -(H9 typ_unit). eauto.
  - move: (IHcbv _ H6) => [ ? [ ? [ ? [ ? ? ] ] ] ]. eauto 6.
  - inversion H7. subst.
    exists M. (repeat split; eauto) => [ | l' ].
    + rewrite size_set_nth -H0.
      apply /maxn_idPr.
      case (leqP (size H) l) => // Hleq.
      move: (H10 typ_unit).
      by rewrite -(H10 (typ_fvar 0)) !nth_default -?H0.
    + rewrite nth_set_nth /=.
      case (@eqP _ l' l) => [ -> | ]; eauto.
      by rewrite H10.
  - move: (IHcbv _ H7) => [ M' [ ? [ ? [ ? ? ] ] ] ].
    exists M'. repeat split; eauto.
    apply /typed_update; eauto.
    apply /typed_weaken_store; eauto.
  - move: (IHcbv _ H10) => [ M' [ ? [ ? [ ? ? ] ] ] ].
    exists M'. repeat split; eauto.
    apply /typed_update; eauto.
    apply /typed_weaken_store; eauto.
  - exists M. repeat split; eauto.
    exact /(typed_subst_single _ _ _ _ _ _ H10 L).
  - by move: (cbv_value _ _ _ _ H2 H6).
Qed.

Lemma canonical_arrow : forall v M T1 T2,
  value v ->
  typed M [::] v (typ_arrow T1 T2) ->
  exists t, v = trm_abs t.
Proof. case => //; inversion 2. eauto. Qed.

Lemma canonical_ref : forall v M T,
  value v ->
  typed M [::] v (typ_ref T) ->
  exists l, v = trm_loc l.
Proof. case => //; inversion 2. eauto. Qed.

Lemma progress H M :
  size H = size M ->
  (forall i, typed M [::] (nth trm_unit H i) (nth typ_unit M i)) ->
  forall t T,
  typed M [::] t T ->
  value t \/ exists H' t', cbv H t H' t'.
Proof.
  move => Hsize Hstore t.
  induction t; inversion 1; subst; eauto.
  - move: (H2 typ_unit).
    by rewrite -(H2 (typ_bvar 0)) !nth_default.
  - move: (IHt1 _ H4) => [ /((canonical_arrow _ _ _ _)^~H4) [ ? -> ] | [ ? [ ? ? ] ] ]; eauto.
    move: (IHt2 _ H6) => [ ? | [ ? [ ? ? ] ] ]; eauto.
  - move: (IHt _ H3) => [ ? | [ ? [ ? ? ] ] ]; eauto.
  - move: (IHt _ H3) => [ /((canonical_ref _ _ _)^~H3) [ l ? ] | [ ? [ ? ? ] ] ]; subst; eauto.
    inversion H3. subst.
    right. repeat eexists. apply /(cbv_deref _ _ (nth trm_unit H l)) => ?.
    case (leqP (size H) l).
    + rewrite Hsize => ?.
      move: (H6 typ_unit).
      by rewrite -(H6 (typ_fvar 0)) !(@nth_default _ _ M).
    + exact /set_nth_default.
  - move: (IHt1 _ H4) => [ /((canonical_ref _ _ _)^~H4) [ l ? ] | [ ? [ ? ? ] ] ]; subst; eauto.
    inversion H4. subst.
    move: (IHt2 _ H6) => [ ? | [ ? [ ? ? ] ] ]; eauto.
Qed.
