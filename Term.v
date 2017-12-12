Require Import Arith Finite_sets_facts.
Require Import Misc Types.

Inductive trm : Set :=
  | trm_var (n : nat)
  | trm_abs (T : typ) (t : trm)
  | trm_app (t1 t2 : trm).

Fixpoint trm_ftv t :=
  match t with
  | trm_var _ => Empty_set _
  | trm_abs T t => Union _ (typ_fv T) (trm_ftv t)
  | trm_app t1 t2 => Union _ (trm_ftv t1) (trm_ftv t2)
  end.

Lemma trm_ftv_bound t : { x | forall y, In _ (trm_ftv t) y -> y <= x }.
Proof.
  Local Hint Resolve le_trans.
  induction t as [ | T ? [ y ] | ? [ x ] ? [ y ] ]; simpl.
  - exists 0. inversion 1.
  - destruct (typ_fv_bound T) as [ x ].
    destruct (le_ge_dec x y); [ exists y | exists x ]; inversion 1; subst; eauto.
  - destruct (le_ge_dec x y); [ exists y | exists x ]; inversion 1; subst; eauto.
Defined.

Fixpoint trm_subst_typ s t :=
  match t with
  | trm_var x => trm_var x
  | trm_abs T t => trm_abs (typ_subst s T) (trm_subst_typ s t)
  | trm_app t1 t2 => trm_app (trm_subst_typ s t1) (trm_subst_typ s t2)
  end.

Lemma trm_subst_typ_fvar t : trm_subst_typ typ_fvar t = t.
Proof.
  Local Hint Resolve typ_subst_fvar.
  induction t; simpl; f_equal; eauto.
Qed.

Lemma trm_subst_typ_ext s s' t :
  (forall x, In _ (trm_ftv t) x -> s x = s' x) ->
  trm_subst_typ s t = trm_subst_typ s' t.
Proof.
  induction t; simpl; intros; f_equal; eauto with sets.
  apply typ_subst_ext. eauto with sets.
Qed.

Lemma trm_subst_typ_comp s s' t :
  trm_subst_typ s (trm_subst_typ s' t) = trm_subst_typ (fun x => typ_subst s (s' x)) t.
Proof.
  Local Hint Resolve typ_subst_comp.
  induction t; simpl; f_equal; eauto.
Qed.

Lemma trm_ftv_subst s t x : In _ (trm_ftv (trm_subst_typ s t)) x -> exists y, In _ (typ_fv (s y)) x /\ In _ (trm_ftv t) y.
Proof.
  induction t; simpl.
  - inversion 1.
  - inversion 1; [ edestruct typ_fv_subst as [ ? [ ] ] | destruct IHt as [ ? [ ] ] ]; eauto with sets.
  - inversion 1; [ destruct IHt1 as [ ? [ ] ] | destruct IHt2 as [ ? [ ] ] ]; eauto with sets.
Qed.

