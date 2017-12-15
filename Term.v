Require Import Arith Finite_sets_facts.
Require Import Misc Types.

Inductive trm : Set :=
  | trm_var (n : nat)
  | trm_abs (t : trm)
  | trm_app (t1 t2 : trm).
