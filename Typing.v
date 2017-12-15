Require Import Arith List Finite_sets_facts Omega Program.
Require Import Types Term.

Definition env := list typ.

Definition env_ftv (G : env) :=
  fold_right (fun T s => Union _ (typ_fv T) s) (Empty_set _) G.

Lemma env_ftv_bound G : { x | forall y, In _ (env_ftv G) y -> y <= x }.
Proof.
  Local Hint Resolve le_trans.
  induction G as [ | T ? [ y ] ]; simpl.
  - exists 0. inversion 1.
  - destruct (typ_fv_bound T) as [ x ].
    destruct (le_ge_dec x y); [ exists y | exists x ]; inversion 1; subst; eauto.
Defined.

Lemma env_ftv_intro G T x :
  In _ (typ_fv T) x ->
  List.In T G ->
  In _ (env_ftv G) x.
Proof. induction G; inversion 2; simpl; subst; eauto with sets. Qed.

Definition env_subst_typ s G := map (typ_subst s) G.

Lemma env_subst_typ_fvar G : env_subst_typ typ_fvar G = G.
Proof.
  eapply eq_trans.
  - apply map_ext. apply typ_subst_fvar.
  - apply map_id.
Qed.

Lemma env_subst_typ_ext s s' G :
  (forall x, In _ (env_ftv G) x -> s x = s' x) ->
  env_subst_typ s G = env_subst_typ s' G.
Proof.
  Local Hint Resolve typ_subst_ext.
  induction G; simpl; intros; f_equal; eauto with sets.
Qed.

Lemma env_subst_typ_comp s s' G : env_subst_typ s (env_subst_typ s' G) = env_subst_typ (fun x => typ_subst s (s' x)) G.
Proof.
  eapply eq_trans.
  - apply map_map.
  - apply map_ext. apply typ_subst_comp.
Qed.

Lemma env_ftv_subst G s x : In _ (env_ftv (env_subst_typ s G)) x -> exists y, In _ (typ_fv (s y)) x /\ In _ (env_ftv G) y.
Proof.
  induction G; simpl.
  - inversion 1.
  - inversion 1; [ edestruct typ_fv_subst as [ ? [ ] ] | destruct IHG as [ ? [ ] ] ]; eauto with sets.
Qed.

Inductive typed : env -> trm -> typ -> Prop :=
  | typed_var G x T :
      nth_error G x = Some T ->
      typed G (trm_var x) T
  | typed_abs G t T1 T2 :
      typed (T1 :: G) t T2 ->
      typed G (trm_abs t) (typ_arrow T1 T2)
  | typed_app G t1 t2 T1 T2 :
      typed G t1 (typ_arrow T1 T2) ->
      typed G t2 T1 ->
      typed G (trm_app t1 t2) T2.
Hint Constructors typed.

Lemma typed_subst_typ s G t T :
  typed G t T ->
  typed (env_subst_typ s G) t (typ_subst s T).
Proof.
  induction 1; simpl; eauto.
  constructor. apply map_nth_error. eauto.
Qed.
Hint Resolve typed_subst_typ.

Fixpoint typing n G t :=
  match t with
  | trm_var x => option_map (pair (n, typ_fvar)) (nth_error G x)
  | trm_abs t =>
      match typing (S n) (typ_fvar n :: G) t with
      | None => None
      | Some (n1, s1, T2) =>
          Some (n1, s1, typ_arrow (s1 n) T2)
      end
  | trm_app t1 t2 =>
      match typing n G t1 with
      | None => None
      | Some (n1, s1, T1) =>
          match typing n1 (env_subst_typ s1 G) t2 with
          | None => None
          | Some (n2, s2, T2) =>
              option_map
                (fun s3 => (S n2, fun x => typ_subst (fun x => typ_subst s3 (s2 x)) (s1 x), s3 n2))
                (unify [ (typ_subst s2 T1, typ_arrow T2 (typ_fvar n2)) ])
          end
      end
  end.

Theorem typing_sound t : forall G m n s T,
  typing m G t = Some (n, s, T) ->
  typed (env_subst_typ s G) t T.
Proof.
  induction t as [ x | t | t1 IHt1 t2 IHt2 ]; simpl; intros G m ? s T Htyping.
  - destruct (nth_error G x) eqn:?; inversion Htyping; subst.
    rewrite env_subst_typ_fvar. eauto.
  - destruct (typing (S m) (typ_fvar m :: G) t) as [ [ [ ] T2 ] | ] eqn:Heqo; inversion Htyping; subst.
    specialize (IHt _ _ _ _ _ Heqo). eauto.
  - destruct (typing m G t1) as [ [ [ n1 s1 ] T1 ] | ] eqn:Heqo1; inversion Htyping.
    specialize (IHt1 _ _ _ _ _ Heqo1).
    destruct (typing n1 (env_subst_typ s1 G) t2) as [ [ [ n2 s2 ] T2 ] | ] eqn:Heqo2; inversion Htyping.
    specialize (IHt2 _ _ _ _ _ Heqo2).
    destruct (unify [(typ_subst s2 T1, typ_arrow T2 (typ_fvar n2))]) as [ s3 | ] eqn:Heqo3; inversion Htyping.
    apply unify_sound in Heqo3. inversion Heqo3. subst. simpl in *.
    repeat rewrite <- env_subst_typ_comp in *.
    apply typed_subst_typ with (s := s2) in IHt1. apply typed_subst_typ with (s := s3) in IHt1. rewrite H6 in *. eauto.
Qed.

Theorem typing_complete t : forall G m s T,
  typed (env_subst_typ s G) t T ->
  (forall n, In _ (env_ftv G) n -> n < m) ->
  exists n s' s'' T', typing m G t = Some (n, s', T') /\ m <= n /\ T = typ_subst s'' T'
    /\ (forall x m, In _ (typ_fv (s' x)) m -> x = m \/ m < n)
    /\ (forall m, In _ (typ_fv T') m -> m < n)
    /\ forall n, n < m -> s n = typ_subst s'' (s' n).
Proof.
  Local Hint Resolve Nat.lt_le_trans le_trans le_S.
  induction t as [ x | t | t1 IHt1 t2 IHt2 ]; intros G m s T; inversion 1; intros Henv; subst; simpl in *.
  - unfold env_subst_typ in *.
    destruct (nth_error G x) as [ T' | ] eqn:Hnth.
    + exists m, typ_fvar, s, T'. repeat split; eauto.
      * apply map_nth_error with (f := typ_subst s) in Hnth. congruence.
      * inversion 1; eauto.
      * intros ? HIn. apply nth_error_In in Hnth.
        apply Henv. eapply env_ftv_intro; eauto.
    + apply nth_error_None in Hnth.
      assert (Hnth' : nth_error (map (typ_subst s) G) x <> None) by congruence.
      apply nth_error_Some in Hnth'. repeat rewrite map_length in *. omega.
  - destruct IHt with (G := typ_fvar m :: G) (m := S m) (s := fun x => if lt_dec x m then s x else T1) (T := T2) as [ n [ s' [ s'' [ T2' [ Htyping [ ? [ HT [ Hsfv [ ? Hs ] ] ] ] ] ] ] ] ].
    { simpl. destruct (lt_dec m m); [ omega | ].
      rewrite env_subst_typ_ext with (s' := s) by (intros x ?; destruct (lt_dec x m); [ eauto | exfalso; eauto ]).
      eauto. }
    { inversion 1; eauto. inversion H1; eauto. }
    rewrite Htyping. exists n, s', s'', (typ_arrow (s' m) T2'). simpl. repeat split; eauto.
    + rewrite HT. f_equal. rewrite <- Hs; eauto. destruct (lt_dec m m); eauto. omega.
    + inversion 1; subst; eauto.
      edestruct Hsfv; eauto; subst; eauto with sets.
    + intros l ?. rewrite <- Hs by eauto. destruct (lt_dec l m); [ eauto | exfalso; eauto ].
  - destruct (IHt1 _ m _ _ H3) as [ n1 [ s1 [ s1' [ T1' [ Htyping1 [ ? [ HT1 [ Hsfv1 [ ? Hs1 ] ] ] ] ] ] ] ] ]; eauto with sets. rewrite Htyping1.
    repeat rewrite env_subst_typ_ext with (s := s) (s' := fun x => typ_subst s1' (s1 x)) in * by eauto with sets.
    repeat rewrite <- env_subst_typ_comp in *.
    destruct (IHt2 _ n1 _ _ H5) as [ n2 [ s2 [ s2' [ T2' [ Htyping2 [ ? [ HT2 [ Hsfv2 [ ? Hs2 ] ] ] ] ] ] ] ] ]; eauto with sets.
    { intros ? HIn. destruct (env_ftv_subst _ _ _ HIn) as [ ? [ HIn' ] ]. destruct (Hsfv1 _ _ HIn'); subst; eauto with sets. }
    rewrite Htyping2. subst.
    rewrite typ_subst_ext with (s := s1') (s' := fun x => typ_subst s2' (s2 x)) in * by eauto with sets. repeat rewrite <- typ_subst_comp in *.
    destruct unify_complete with
      (C := [(typ_subst s2 T1', typ_arrow T2' (typ_fvar n2))])
      (s := fun x => if lt_dec x n2 then s2' x else T) as [ s3 [ Hunify [ s3' Hmg ] ] ].
    { constructor; eauto. simpl. destruct (lt_dec n2 n2); try omega.
      repeat rewrite typ_subst_ext with (s := fun x => if lt_dec x n2 then s2' x else T) (s' := s2'); eauto.
      - intros x HIn. destruct (lt_dec x n2); eauto. specialize (H4 _ HIn). omega.
      - intros x HIn. destruct (lt_dec x n2); eauto. destruct (typ_fv_subst _ _ _ HIn) as [ ? [ HIns2 HInT1 ] ].
        destruct (Hsfv2 _ _ HIns2); subst; try omega. specialize (H1 _ HInT1). omega. }
    rewrite Hunify. specialize (unifier_dom _ _ Hunify). intros Hsfv3. exists (S n2), (fun x => typ_subst (fun x => typ_subst s3 (s2 x)) (s1 x)), s3', (s3 n2). simpl in *. repeat split; eauto 3.
    + specialize (Hmg n2). destruct (lt_dec n2 n2); eauto; omega.
    + intros.
      repeat match goal with
      | H : In _ (typ_fv (typ_subst _ _)) _ |- _ => destruct (typ_fv_subst _ _ _ H) as [? [ ] ]; clear H
      end.
      edestruct Hsfv3; eauto.
      * subst. edestruct Hsfv2; eauto. subst. edestruct Hsfv1; eauto.
      * repeat match goal with
        | H : In _ (Union _ _ _) _ |- _ => inversion H; clear H
        | H : In _ (Singleton _ _) _ |- _ => inversion H; clear H
        | H : In _ (Empty_set _) _ |- _ => inversion H
        end; subst; eauto.
        destruct (typ_fv_subst _ _ _ H10) as [ ? [ ] ].
        edestruct Hsfv2; eauto. subst. eauto.
    + intros ? HIn. destruct (Hsfv3 _ _ HIn); subst; eauto.
      repeat match goal with
      | H : In _ (Union _ _ _) _ |- _ => inversion H; clear H
      | H : In _ (Singleton _ _) _ |- _ => inversion H; clear H
      | H : In _ (Empty_set _) _ |- _ => inversion H
      end; subst; eauto.
      destruct (typ_fv_subst _ _ _ H7) as [ ? [ ] ].
      edestruct Hsfv2; eauto. subst. eauto.
    + intros ? ?. rewrite Hs1 by eauto.
      rewrite typ_subst_ext with (s := s1') (s' := fun x => typ_subst s2' (s2 x))
        by (intros ? HIn; destruct (Hsfv1 _ _ HIn); subst; eauto with sets). rewrite <- typ_subst_comp.
      rewrite typ_subst_ext with (s := s2') (s' := fun x => typ_subst s3' (s3 x))
        by (intros x HIn; rewrite <- Hmg; destruct (lt_dec x n2); eauto; exfalso; destruct (typ_fv_subst _ _ _ HIn) as [ ? [ ] ];
            edestruct Hsfv2; eauto; subst; edestruct Hsfv1; eauto; subst; omega).
      repeat rewrite <- typ_subst_comp. eauto.
Qed.

Definition typing' G t :
  { s : _ & { T | typed (env_subst_typ s G) t T /\
    forall s' T', typed (env_subst_typ s' G) t T' ->
      exists s'', typ_subst s'' T = T' /\ forall x, In _ (env_ftv G) x -> s' x = typ_subst s'' (s x) } } +
  { forall s T, typed (env_subst_typ s G) t T -> False }.
Proof.
  assert (H : { x | forall y, In nat (env_ftv G) y -> y < x }).
  { destruct (env_ftv_bound G) as [ x ].
    exists (S x). intros ? ?. apply le_n_S. eauto. }
  destruct H as [ x ].
  destruct (typing x G t) as [ [ [ ? s ] T ] | ] eqn:Htyping.
  - left. exists s, T. split.
    + eapply typing_sound. eauto.
    + intros s' T' Htyped. destruct (typing_complete _ _ x _ _ Htyped) as [ ? [ ? [ s'' [ T'' [ Htyping' [ ? [ HT [ ? [ ? Hmg ] ] ] ] ] ] ] ] ]; eauto.
      rewrite Htyping in Htyping'. inversion Htyping'. subst. eauto.
  - right. intros ? ? Htyped. destruct (typing_complete _ _ x _ _ Htyped) as [ ? [ ? [ s'' [ T'' [ Htyping' [ ? [ HT [ ? [ ? Hmg ] ] ] ] ] ] ] ] ]; eauto.
    congruence.
Defined.
