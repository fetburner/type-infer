Require Import Arith List Recdef Finite_sets_facts Omega.
Require Import Misc.

Inductive typ : Set :=
  | typ_fvar (x : nat)
  | typ_arrow (T1 T2 : typ).

Definition typ_eq_dec T1 : forall T2 : typ, { T1 = T2 } + { T1 <> T2 }.
Proof.
  induction T1 as [ x | ? IHT11 ? IHT12 ]; intros [ y | T21 T22 ]; try solve [ right; inversion 1 ].
  - destruct (eq_nat_dec x y); [ left | right ]; congruence.
  - destruct (IHT11 T21); [ | right; congruence ].
    destruct (IHT12 T22); [ | right; congruence ].
    left. congruence.
Defined.

Fixpoint typ_fv T :=
  match T with
  | typ_fvar x => Singleton _ x
  | typ_arrow T1 T2 => Union _ (typ_fv T1) (typ_fv T2)
  end.

Definition typ_fv_dec x T :
  { In _ (typ_fv T) x } + { ~ In _ (typ_fv T) x }.
Proof.
  Local Hint Resolve In_Empty_dec In_Union_dec.
  induction T as [ y | ]; simpl; eauto.
  destruct (eq_nat_dec x y).
  - eauto with sets.
  - right. inversion 1. eauto with sets.
Defined.

Lemma typ_fv_finite T : Finite _ (typ_fv T).
Proof.
  Local Hint Resolve Empty_is_finite Singleton_is_finite Union_preserves_Finite.
  induction T; simpl; eauto.
Qed.

Lemma typ_fv_bound T : { x | forall y, In _ (typ_fv T) y -> y < x }.
Proof.
  Local Hint Resolve Singleton_bound Union_bound.
  induction T; simpl; eauto.
Defined.

Fixpoint typ_subst s T :=
  match T with
  | typ_fvar x => s x
  | typ_arrow T1 T2 => typ_arrow (typ_subst s T1) (typ_subst s T2)
  end.

Lemma typ_subst_fvar T : typ_subst typ_fvar T = T.
Proof. induction T; simpl; congruence. Qed.

Lemma typ_subst_ext s s' T :
  (forall x, In _ (typ_fv T) x -> s x = s' x) ->
  typ_subst s T = typ_subst s' T.
Proof. induction T; simpl; intros; solve [ eauto with sets | f_equal; eauto with sets ]. Qed.

Lemma typ_subst_comp s s' T : typ_subst s' (typ_subst s T) = typ_subst (fun x => typ_subst s' (s x)) T.
Proof. induction T; simpl; solve [ eauto with sets | f_equal; eauto with sets ]. Qed.

Lemma typ_fv_subst s T x : In _ (typ_fv (typ_subst s T)) x -> exists y, In _ (typ_fv (s y)) x /\ In _ (typ_fv T) y.
Proof.
  induction T; simpl; eauto with sets.
  - inversion 1; [ destruct IHT1 as [ ? [ ] ] | destruct IHT2 as [ ? [ ] ] ]; eauto with sets.
Qed.

Fixpoint typ_size T :=
  S match T with
    | typ_fvar _ => 0
    | typ_arrow T1 T2 => typ_size T1 + typ_size T2
    end.

Lemma typ_size_nonzero T : 0 < typ_size T.
Proof. destruct T; simpl; omega. Qed.

Definition constr := list (typ * typ).
Definition constr_fv (C : constr) :=
  fold_right (fun p s => Union _ (typ_fv (fst p)) (Union _ (typ_fv (snd p)) s)) (Empty_set _) C.

Lemma constr_fv_finite C : Finite _ (constr_fv C).
Proof.
  Local Hint Resolve typ_fv_finite Empty_is_finite Union_preserves_Finite.
  induction C; simpl; eauto.
Qed.

Definition constr_size (C : constr) :=
  fold_right (fun p s => typ_size (fst p) + s) 0 C.
Definition constr_subst s (C : constr) :=
  map (fun p => (typ_subst s (fst p), typ_subst s (snd p))) C.

Lemma constr_fv_subst C s x :
  In _ (constr_fv (constr_subst s C)) x ->
  exists y, In _ (typ_fv (s y)) x /\ In _ (constr_fv C) y.
Proof.
  unfold constr_fv, constr_subst.
  induction C as [ | [ T1 T2 ] ? IHC ]; simpl; intros;
    repeat match goal with
    | H : In _ (Empty_set _) _ |- _ => inversion H
    | H : In _ (Union _ _ _) _ |- _ => inversion H; clear H
    end;
    solve [ edestruct typ_fv_subst as [ ? [ ] ]; eauto with sets
          | destruct IHC as [ ? [ ? HIn ] ]; eauto with sets; inversion HIn; eauto with sets ].
Qed.

Definition typ_subst_single x T y :=
  if eq_nat_dec x y then T else typ_fvar y.

Lemma typ_subst_single_hit T x :
  typ_subst_single x T x = T.
Proof. unfold typ_subst_single. destruct (eq_nat_dec x x); congruence. Qed.

Lemma typ_subst_single_notin T1 T2 x :
  ~ In _ (typ_fv T1) x ->
  typ_subst (typ_subst_single x T2) T1 = T1.
Proof.
  intros. unfold typ_subst_single.
  rewrite typ_subst_ext with (s' := typ_fvar).
  - apply typ_subst_fvar.
  - intros y ?. destruct (eq_nat_dec x y); subst; congruence.
Qed.

Definition constr_lt (C1 C2 : constr) := forall m n,
  cardinal _ (constr_fv C1) m ->
  cardinal _ (constr_fv C2) n ->
  m <= n /\ (n <= m -> constr_size C1 < constr_size C2).

Lemma constr_lt_wf : well_founded constr_lt.
Proof.
  intros C.
  destruct (finite_cardinal _ _ (constr_fv_finite C)) as [ n ].
  generalize dependent C.
  induction n as [ n IHn ] using lt_wf_ind.
  intros C Hcard.
  induction C as [ C ] using (induction_ltof1 _ constr_size); unfold ltof in *.
  constructor.
  intros C' Hlt.
  destruct (finite_cardinal _ _ (constr_fv_finite C')) as [ m Hcard' ].
  destruct (Hlt _ _ Hcard' Hcard).
  destruct (eq_nat_dec m n); subst; eauto.
  eapply IHn; eauto; omega.
Qed.

Lemma Included_constr_same C T :
  Included _ (constr_fv C) (constr_fv ((T, T) :: C)).
Proof. intros ? ?. simpl. eauto with sets. Qed.

Lemma constr_lt_same C T :
  constr_lt C ((T, T) :: C).
Proof.
  intros ? ? ? ?. unfold constr_fv, constr_size in *. simpl in *. split.
  - eapply incl_card_le; eauto.
    apply Included_constr_same.
  - specialize (typ_size_nonzero T). omega.
Qed.

Lemma Included_constr_subst C T T1 T2 x :
  ~ In _ (typ_fv T) x ->
  T1 = T /\ T2 = typ_fvar x \/ T1 = typ_fvar x /\ T2 = T ->
  Included _ (constr_fv (constr_subst (typ_subst_single x T) C)) (constr_fv ((T1, T2) :: C)).
Proof.
  unfold typ_subst_single. simpl. intros ? Heq ? HIn.
  destruct (constr_fv_subst _ _ _ HIn) as [ z [ HIn' ] ].
  destruct (eq_nat_dec x z); [ | inversion HIn' ]; destruct Heq as [ [ ] | [ ] ]; subst; eauto with sets.
Qed.

Lemma constr_lt_subst C T T1 T2 x :
  ~ In _ (typ_fv T) x ->
  T1 = T /\ T2 = typ_fvar x \/ T1 = typ_fvar x /\ T2 = T ->
  constr_lt (constr_subst (typ_subst_single x T) C) ((T1, T2) :: C).
Proof.
  intros ? Heq m n ? ?.
  assert (~ In _ (constr_fv (constr_subst (typ_subst_single x T) C)) x); unfold typ_subst_single in *.
  { intros HIn. destruct (constr_fv_subst _ _ _ HIn) as [ y [ Hcontra ] ].
    destruct (eq_nat_dec x y); subst; simpl in *; eauto.
    inversion Hcontra. congruence. }
  unfold constr_size, constr_fv in *. simpl in *.
  assert (m < n).
  { eapply incl_st_card_lt; eauto. split.
    - apply Included_constr_subst; eauto.
    - intros Hcontra. rewrite Hcontra in *.
      destruct Heq as [ [ ] | [ ] ]; subst; simpl in *; eauto with sets. }
  omega.
Qed.

Lemma Included_constr_arrow C T11 T12 T21 T22 :
  Included _ (constr_fv ((T11, T21) :: (T12, T22) :: C)) (constr_fv ((typ_arrow T11 T12, typ_arrow T21 T22) :: C)).
Proof.
  unfold constr_fv in *. simpl. intros ? ?.
  repeat match goal with
  | H : In _ (Union _ _ _) _ |- _ => inversion H; clear H
  end; eauto with sets.
Qed.

 Lemma constr_lt_arrow C T11 T12 T21 T22 :
  constr_lt ((T11, T21) :: (T12, T22) :: C) ((typ_arrow T11 T12, typ_arrow T21 T22) :: C).
Proof.
  intros m n ? ?. split.
  - eapply incl_card_le; eauto.
    apply Included_constr_arrow.
  - unfold constr_size. simpl. omega.
Qed.

Local Hint Resolve constr_lt_same constr_lt_subst constr_lt_arrow.

Function unify C { wf constr_lt C } :=
  match C with
  | nil => Some typ_fvar
  | (T1, T2) :: C =>
      if typ_eq_dec T1 T2 then unify C
      else
        match T1, T2 with
        | typ_fvar x, _ =>
            if typ_fv_dec x T2 then None
            else option_map (fun s z => typ_subst s (typ_subst_single x T2 z)) (unify (constr_subst (typ_subst_single x T2) C))
        | _, typ_fvar y =>
            if typ_fv_dec y T1 then None
            else option_map (fun s z => typ_subst s (typ_subst_single y T1 z)) (unify (constr_subst (typ_subst_single y T1) C))
        | typ_arrow T11 T12, typ_arrow T21 T22 => unify ((T11, T21) :: (T12, T22) :: C)
        end
  end.
Proof.
  - intros. subst. eauto.
  - intros. eauto.
  - intros. eauto.
  - intros. eauto.
  - apply constr_lt_wf.
Defined.

Definition unifies s (C : constr) := Forall (fun p => typ_subst s (fst p) = typ_subst s (snd p)) C.

Lemma unify_sound_subst C s T T1 T2 x :
  (forall C', constr_lt C' ((T1, T2) :: C) -> forall s, unify C' = Some s -> unifies s C') ->
  (if typ_fv_dec x T then None
   else option_map (fun s z => typ_subst s (typ_subst_single x T z)) (unify (constr_subst (typ_subst_single x T) C))) = Some s ->
  T1 = T /\ T2 = typ_fvar x \/ T1 = typ_fvar x /\ T2 = T ->
  unifies s ((T1, T2) :: C).
Proof.
  intros IH Heq Hsel.
  destruct (typ_fv_dec x T) as [ | HnotIn ]; inversion Heq.
  destruct (unify (constr_subst (typ_subst_single x T) C)) eqn:Heqo; inversion Heq.
  constructor; simpl.
  - destruct Hsel as [ [ ] | [ ] ]; subst; simpl;
    rewrite <- typ_subst_comp;
    rewrite typ_subst_single_hit;
    rewrite typ_subst_single_notin; eauto.
  - specialize (IH _ (constr_lt_subst _ _ _ _ _ HnotIn Hsel) _ Heqo).
    specialize (Forall_map_inv _ _ _ _ _ IH).
    apply Forall_impl. intros [ ? ? ]; simpl in *.
    repeat rewrite <- typ_subst_comp. eauto.
Qed.

Theorem unify_sound : forall C s,
  unify C = Some s ->
  unifies s C.
Proof.
  unfold unifies.
  refine (@well_founded_induction _ _ constr_lt_wf _ _).
  intros [ | [ T1 T2 ] C ] IHC.
  - constructor.
  - intros ? Hunify. rewrite unify_equation in Hunify.
    destruct (typ_eq_dec T1 T2); subst; eauto.
    destruct T1;
      [ eapply unify_sound_subst; eauto | ];
      ( destruct T2; [ eapply unify_sound_subst; eauto | ] ).
    specialize (IHC _ (constr_lt_arrow _ _ _ _ _) _ Hunify).
    inversion IHC. inversion H2. subst. simpl in *.
    constructor; eauto. simpl. congruence.
Qed.

Lemma unifies_occur_aux s T x :
  typ_size (typ_subst s T) <= typ_size (s x) -> In _ (typ_fv T) x -> T = typ_fvar x.
Proof.
  induction T; simpl; inversion 2; subst; eauto.
  - rewrite IHT1 in H by (eauto || omega). simpl in *. omega.
  - rewrite IHT2 in H by (eauto || omega). simpl in *. omega.
Qed.

Corollary unifies_occur s T x :
  typ_subst s T = s x -> In _ (typ_fv T) x -> T = typ_fvar x.
Proof. intros Heq. eapply unifies_occur_aux. rewrite Heq. omega. Qed.

Lemma typ_subst_single_idempotent s T x :
  typ_subst s T = s x ->
  forall y, typ_subst s (typ_subst_single x T y) = s y.
Proof.
  intros ? ?. unfold typ_subst_single.
  destruct (eq_nat_dec x y); subst; simpl; eauto.
Qed.

Lemma unifies_extend s T C x :
  typ_subst s T = s x ->
  unifies s C ->
  unifies s (constr_subst (typ_subst_single x T) C).
Proof.
  intros ? H. apply Forall_map.
  eapply Forall_impl; [ | apply H ].
  intros [ T1 T2 ] ?. simpl in *.
  repeat rewrite typ_subst_comp.
  erewrite typ_subst_ext with (T := T1);
    [ erewrite typ_subst_ext with (T := T2); [ eassumption | ] | ];
    intros; apply typ_subst_single_idempotent; eauto.
Qed.

Definition moregen (s s' : nat -> typ) :=
  exists s0, forall x, s' x = typ_subst s0 (s x).

Lemma moregen_max s : moregen typ_fvar s.
Proof. exists s. eauto. Qed.

Lemma moregen_extend s s' T x :
  typ_subst s T = s x ->
  moregen s' s ->
  moregen (fun y => typ_subst s' (typ_subst_single x T y)) s.
Proof.
  intros ? [ s'' Heq ]. exists s''. intros ?.
  rewrite typ_subst_comp.
  rewrite typ_subst_ext with (s' := s) by (intros; symmetry; apply Heq).
  symmetry. apply typ_subst_single_idempotent. eauto.
Qed.

Local Hint Resolve unifies_extend moregen_max moregen_extend.

Lemma unify_complete_var C s T T1 T2 x :
  (forall C', constr_lt C' ((T1, T2) :: C) -> forall s, unifies s C' -> exists s', unify C' = Some s' /\ moregen s' s) ->
  T <> typ_fvar x ->
  typ_subst s T = s x ->
  unifies s C ->
  T1 = T /\ T2 = typ_fvar x \/ T1 = typ_fvar x /\ T2 = T ->
  exists s',
    (if typ_fv_dec x T then None
     else option_map (fun s0 z => typ_subst s0 (typ_subst_single x T z))
        (unify (constr_subst (typ_subst_single x T) C))) = Some s' /\ moregen s' s.
Proof.
  intros IHC Hneq Hunify Hunify' Hsel.
  destruct (typ_fv_dec x T).
  - destruct Hneq. eapply unifies_occur; eauto.
  - edestruct IHC as [ ? [ Heq ] ].
    + apply constr_lt_subst; eauto.
    + eauto.
    + rewrite Heq. simpl. eauto.
Qed.

Theorem unify_complete C : forall s,
  unifies s C ->
  exists s', unify C = Some s' /\ moregen s' s.
Proof.
  induction C as [ [ | [ T1 T2 ] C] IHC ] using (well_founded_induction constr_lt_wf);
    intros ? Hunifies;
    rewrite unify_equation in *;
    eauto.
  - inversion Hunifies; subst; simpl in *.
    destruct (typ_eq_dec T1 T2); subst; eauto.
    destruct T1; [ eapply unify_complete_var; eauto | ];
      (destruct T2; [ eapply unify_complete_var; eauto | ]);
      simpl in *; inversion H1; try congruence.
    edestruct IHC as [ ? [ Heq ] ].
    + apply constr_lt_arrow.
    + repeat constructor; eauto.
    + eauto.
Qed.

Lemma unifier_dom_var C s T T1 T2 x :
  (forall C', constr_lt C' ((T1, T2) :: C) ->
    forall s, unify C' = Some s ->
      forall y z, In _ (typ_fv (s y)) z ->
        y = z \/ In _ (constr_fv C') z) ->
  (if typ_fv_dec x T then None else
    option_map (fun s z => typ_subst s (typ_subst_single x T z))
      (unify (constr_subst (typ_subst_single x T) C))) = Some s ->
  T1 = T /\ T2 = typ_fvar x \/ T1 = typ_fvar x /\ T2 = T ->
  forall y z,
  In _ (typ_fv (s y)) z ->
  y = z \/ In _ (constr_fv ((T1, T2) :: C)) z.
Proof.
  intros IHC Hunify Hsel ? ? HIn.
  destruct (typ_fv_dec x T); inversion Hunify.
  destruct (unify (constr_subst (typ_subst_single x T) C)) eqn:Hunify'; inversion Hunify; subst.
  destruct (typ_fv_subst _ _ _ HIn) as [ ? [ ? HIn' ] ].
  edestruct IHC; eauto.
  - unfold typ_subst_single in HIn'. destruct (eq_nat_dec x y).
    + simpl. destruct Hsel as [ [ ] | [ ] ]; subst; eauto with sets.
    + inversion HIn'. subst. eauto.
  - right. eapply Included_constr_subst; eauto.
Qed.

Lemma unifier_dom : forall C s,
  unify C = Some s ->
  forall x y, In _ (typ_fv (s x)) y -> x = y \/ In _ (constr_fv C) y.
Proof.
  refine (@well_founded_induction _ _ constr_lt_wf _ _).
  intros [ | [ T1 T2 ] C ] IHC s Hunify ? ? HIn;
    rewrite unify_equation in Hunify; simpl in *.
  - inversion Hunify. subst. inversion HIn. eauto.
  - destruct (typ_eq_dec T1 T2).
    + subst. edestruct IHC; eauto with sets.
    + destruct T1; [ eapply unifier_dom_var; eauto | ];
        (destruct T2; [ eapply unifier_dom_var; eauto | ]);
        try inversion Hunify.
    simpl. edestruct IHC; eauto.
    right. apply Included_constr_arrow. eauto.
Qed.
