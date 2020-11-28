From mathcomp Require Import all_ssreflect.
Require Import Program.
Require Import Util.

Inductive trm :=
  | trm_unit
  | trm_var (n : nat)
  | trm_loc (l : nat)
  | trm_abs (t : trm)
  | trm_app (t1 t2 : trm)
  | trm_ref (t : trm)
  | trm_deref (t : trm)
  | trm_update (t1 t2 : trm)
  | trm_let (t1 t2 : trm).

Fixpoint trm_rename r t :=
  match t with
  | trm_unit => trm_unit
  | trm_var n => trm_var (r n)
  | trm_loc l => trm_loc l
  | trm_abs t => trm_abs (trm_rename (upren r) t)
  | trm_app t1 t2 => trm_app (trm_rename r t1) (trm_rename r t2)
  | trm_ref t1 => trm_ref (trm_rename r t1)
  | trm_deref t1 => trm_deref (trm_rename r t1)
  | trm_update t1 t2 => trm_update (trm_rename r t1) (trm_rename r t2)
  | trm_let t1 t2 => trm_let (trm_rename r t1) (trm_rename (upren r) t2)
  end.

Program Instance TrmRename : Rename trm :=
  { var := trm_var; rename := trm_rename }.
Next Obligation.
  elim: t r r' H => /=;
  intros; f_equal; eauto using eq_upren, eq_upnren.
Qed.

Program Instance RenameLemmasTrm : RenameLemmas trm.
Next Obligation.
  induction t => /=; f_equal;
  eauto using rename_id_upren, rename_id_upnren.
Qed.
Next Obligation.
  elim: t r r' => /=; intros; f_equal; rewrite ?size_map;
  eauto using rename_rename_comp_upren, rename_rename_comp_upnren.
Qed.

Fixpoint trm_subst s t :=
  match t with
  | trm_unit => trm_unit
  | trm_var n => s n
  | trm_loc l => trm_loc l
  | trm_abs t => trm_abs (trm_subst (up s) t)
  | trm_app t1 t2 => trm_app (trm_subst s t1) (trm_subst s t2)
  | trm_ref t => trm_ref (trm_subst s t)
  | trm_deref t => trm_deref (trm_subst s t)
  | trm_update t1 t2 => trm_update (trm_subst s t1) (trm_subst s t2)
  | trm_let t1 t2 => trm_let (trm_subst s t1) (trm_subst (up s) t2)
  end.

Program Instance SubstTrm : Subst trm := { subst := trm_subst }.
Next Obligation.
  elim: t s s' H => /=; intros; f_equal;
  eauto using eq_up, eq_upn.
Qed.

Program Instance SubstLemmasTrm : SubstLemmas trm.
Next Obligation.
  elim: t => /=; intros; f_equal;
  eauto using subst_id_up, subst_id_upn.
Qed.
Next Obligation.
  elim: t r => /=; intros; f_equal;
  eauto using rename_subst_up, rename_subst_upn.
Qed.
Next Obligation.
  elim: t r s => /=; intros; f_equal; rewrite ?size_map;
  eauto using subst_rename_comp_up, subst_rename_comp_upn.
Qed.
Next Obligation.
  elim: t r s => /=; intros; f_equal; rewrite ?size_map;
  eauto using rename_subst_comp_up, rename_subst_comp_upn.
Qed.

Program Instance SubstLemmas'Trm : SubstLemmas' trm.
Next Obligation.
  elim: t s s' => /=; intros; f_equal; rewrite ?size_map;
  eauto using subst_subst_comp_up, subst_subst_comp_upn.
Qed.

Definition value v :=
  match v with
  | trm_unit => true
  | trm_abs _ => true
  | trm_loc _ => true
  | _ => false
  end.

Lemma value_rename : forall r v, value (rename r v) = value v.
Proof. by move => ? [ ]. Qed.

Lemma value_subst : forall s v, value v -> value (subst s v).
Proof. by move => ? [ ]. Qed.

Inductive cbv H : trm -> seq trm -> trm -> Prop :=
  | cbv_app t11 v2 :
      value v2 ->
      cbv H (trm_app (trm_abs t11) v2) H (subst (scons v2 var) t11)
  | cbv_app_1 H' t1 t1' t2 :
      cbv H t1 H' t1' ->
      cbv H (trm_app t1 t2) H' (trm_app t1' t2)
  | cbv_app_2 H' v1 t2 t2' :
      value v1 ->
      cbv H t2 H' t2' ->
      cbv H (trm_app v1 t2) H' (trm_app v1 t2')
  | cbv_ref v :
      value v ->
      cbv H (trm_ref v) (rcons H v) (trm_loc (size H))
  | cbv_ref_1 H' t t' :
      cbv H t H' t' ->
      cbv H (trm_ref t) H' (trm_ref t')
  | cbv_deref l v :
      (forall d, nth d H l = v) ->
      cbv H (trm_deref (trm_loc l)) H v
  | cbv_deref_1 H' t t' :
      cbv H t H' t' ->
      cbv H (trm_deref t) H' (trm_deref t')
  | cbv_update l v2 :
      value v2 ->
      cbv H (trm_update (trm_loc l) v2) (set_nth trm_unit H l v2) trm_unit
  | cbv_update_1 H' t1 t1' t2 :
      cbv H t1 H' t1' ->
      cbv H (trm_update t1 t2) H' (trm_update t1' t2)
  | cbv_update_2 H' v1 t2 t2' :
      value v1 ->
      cbv H t2 H' t2' ->
      cbv H (trm_update v1 t2) H' (trm_update v1 t2')
  | cbv_let v1 t2 :
      value v1 ->
      cbv H (trm_let v1 t2) H (subst (scons v1 var) t2)
  | cbv_let_1 H' t1 t1' t2 :
      cbv H t1 H' t1' ->
      cbv H (trm_let t1 t2) H' (trm_let t1' t2).

Hint Constructors cbv.

Lemma cbv_value H t H' t' :
  cbv H t H' t' ->
  value t ->
  false.
Proof. by inversion 1. Qed.

Lemma cbv_det H t H' t' :
  cbv H t H' t' ->
  forall H'' t'',
  cbv H t H'' t'' ->
  H' = H'' /\ t' = t''.
Proof.
  induction 1; inversion 1; subst;
    repeat match goal with
    | H : cbv _ (trm_abs _) _ _ |- _ => inversion H
    | H : cbv _ (trm_loc _) _ _ |- _ => inversion H
    | Hv : is_true (value ?v), Hr : cbv _ ?v _ _ |- _ => by move: (cbv_value _ _ _ _ Hr Hv)
    | Hr : cbv ?H ?t _ _,
      IH : forall H' t', cbv ?H ?t H' t' -> _ = H' /\ _ = t' |- _ => case (IH _ _ Hr) => ? ?; subst; clear Hr
     end; eauto.
  split; eauto.
  by rewrite -(H0 trm_unit) -(H3 trm_unit).
Qed.
