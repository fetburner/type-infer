Require Import Types.
Require Import Autosubst.Autosubst.

Inductive trm :=
  | trm_var (n : var)
  | trm_abs (t : { bind trm })
  | trm_app (t1 t2 : trm).

Instance Ids_trm : Ids trm. derive. Defined.
Instance Rename_trm : Rename trm. derive. Defined.
Instance Subst_trm : Subst trm. derive. Defined.
Instance SubstLemmas_trm : SubstLemmas trm. derive. Qed.

Inductive value : trm -> Prop := val_abs t : value (trm_abs t).

Inductive cbv : trm -> trm -> Prop :=
  | cbv_appabs t11 v2 :
      value v2 ->
      cbv (trm_app (trm_abs t11) v2) (t11.[v2/])
  | cbv_appl t1 t1' t2 :
      cbv t1 t1' ->
      cbv (trm_app t1 t2) (trm_app t1' t2)
  | cbv_appr v1 t2 t2' :
      value v1 ->
      cbv t2 t2' ->
      cbv (trm_app v1 t2) (trm_app v1 t2').

Hint Constructors value cbv.