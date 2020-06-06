From mathcomp Require Import all_ssreflect.

Inductive typ : Set :=
  | typ_fvar (x : nat)
  | typ_bvar (n : nat)
  | typ_arrow (T1 T2 : typ).

Definition typ_eq_dec (T1 T2 : typ) : { T1 = T2 } + { T1 <> T2 }.
Proof. decide equality; exact: PeanoNat.Nat.eq_dec. Defined.

Lemma typ_eqP : Equality.axiom typ_eq_dec.
Proof.
  move => T1 T2.
  by case (typ_eq_dec T1 T2) => ?; [ left | right ].
Qed.

Definition typ_eqMixin := EqMixin typ_eqP.
Canonical typ_eqType := Eval hnf in EqType typ typ_eqMixin.

Fixpoint typ_fv T : pred nat :=
  match T with
  | typ_fvar x => pred1 x
  | typ_bvar _ => pred0
  | typ_arrow T1 T2 => predU (typ_fv T1) (typ_fv T2)
  end.

Fixpoint typ_enum_fv T acc :=
  match T with
  | typ_fvar x => x :: acc
  | typ_bvar x => acc
  | typ_arrow T1 T2 => typ_enum_fv T1 (typ_enum_fv T2 acc) 
  end.

Fixpoint typ_bv T : pred nat :=
  match T with
  | typ_fvar _ => pred0
  | typ_bvar x => pred1 x
  | typ_arrow T1 T2 => predU (typ_bv T1) (typ_bv T2)
  end.

Fixpoint typ_enum_bv T acc :=
  match T with
  | typ_fvar x => acc
  | typ_bvar x => x :: acc
  | typ_arrow T1 T2 => typ_enum_bv T1 (typ_enum_bv T2 acc)
  end.

Lemma typ_enum_fv_inE_aux x : forall T acc,
  (x \in typ_enum_fv T acc) = (x \in typ_fv T) || (x \in acc).
Proof.
  elim => //= ? IHT1 ? IHT2 ?.
  by rewrite IHT1 IHT2 inE orbA.
Qed.

Corollary typ_enum_fv_inE x T :
  (x \in typ_enum_fv T [::]) = (x \in typ_fv T).
Proof. by rewrite typ_enum_fv_inE_aux orbF. Qed.

Lemma typ_enum_bv_inE_aux x : forall T acc,
  (x \in typ_enum_bv T acc) = (x \in typ_bv T) || (x \in acc).
Proof.
  elim => //= ? IHT1 ? IHT2 ?.
  by rewrite IHT1 IHT2 inE orbA.
Qed.

Corollary typ_enum_bv_inE x T :
  (x \in typ_enum_bv T [::]) = (x \in typ_bv T).
Proof. by rewrite typ_enum_bv_inE_aux orbF. Qed.

Fixpoint typ_subst s T :=
  match T with
  | typ_fvar x => s x
  | typ_bvar n => typ_bvar n
  | typ_arrow T1 T2 => typ_arrow (typ_subst s T1) (typ_subst s T2)
  end.

Fixpoint typ_open s T :=
  match T with
  | typ_fvar x => typ_fvar x
  | typ_bvar n => s n
  | typ_arrow T1 T2 => typ_arrow (typ_open s T1) (typ_open s T2)
  end.

Fixpoint typ_size T :=
  match T with
  | typ_fvar _ => 0
  | typ_bvar _ => 0
  | typ_arrow T1 T2 => typ_size T1 + typ_size T2
  end.+1.

Lemma typ_size_nonzero : forall T, 0 < typ_size T.
Proof. by case. Qed.

Lemma typ_subst_fvar T : typ_subst typ_fvar T = T.
Proof. induction T => /=; congruence. Qed.

Lemma typ_subst_ext s s' T :
  { in typ_fv T, s =1 s' } ->
  typ_subst s T = typ_subst s' T.
Proof.
  induction T => //= [ | Hext ].
  - apply. by rewrite inE eqxx.
  - f_equal; [ apply /IHT1 | apply /IHT2 ] => ?;
    rewrite -topredE => /= Hfv; apply /Hext;
    by rewrite inE Hfv ?orbT.
Qed.

Corollary typ_subst_fvar_eq s T :
  { in typ_fv T, s =1 typ_fvar } ->
  typ_subst s T = T.
Proof.
  move => /typ_subst_ext ->.
  by rewrite typ_subst_fvar.
Qed.

Lemma typ_subst_comp s s' T :
  typ_subst s (typ_subst s' T) = typ_subst (typ_subst s \o s') T.
Proof. by induction T => /=; congruence. Qed.

Lemma typ_fv_subst_aux s T x acc :
  has (fun y => x \in typ_fv (s y)) (typ_enum_fv T acc)
  = has (fun y => x \in typ_fv (s y)) acc || (x \in typ_fv (typ_subst s T)).
Proof.
  rewrite orbC.
  elim: T acc => //= ? IHT1 ? IHT2 ?.
  by rewrite IHT1 IHT2 inE orbA.
Qed.

Corollary typ_fv_subst s T x :
  (x \in typ_fv (typ_subst s T)) = has (fun y => x \in typ_fv (s y)) (typ_enum_fv T [::]).
Proof. exact /Logic.eq_sym /typ_fv_subst_aux. Qed.

Corollary typ_fv_subst_elim s T x :
  x \in typ_fv (typ_subst s T) ->
  exists2 y, x \in typ_fv (s y) & y \in typ_fv T.
Proof.
  rewrite typ_fv_subst => /hasP [ ? ].
  rewrite typ_enum_fv_inE => /=. eauto.
Qed.

Corollary typ_fv_subst_intro s T x y :
  y \in typ_fv T ->
  x \in typ_fv (s y) ->
  x \in typ_fv (typ_subst s T).
Proof.
  rewrite -typ_enum_fv_inE typ_fv_subst => ? ?.
  apply /hasP. eauto.
Qed.

Lemma typ_bv_subst_aux s x T acc :
  (x \in typ_bv (typ_subst s T)) || has (fun y => x \in typ_bv (s y)) acc
  = (x \in typ_bv T) || has (fun y => x \in typ_bv (s y)) (typ_enum_fv T acc).
Proof.
  rewrite -!topredE /=.
  elim: T acc => //= T1 IHT1 T2 IHT2 ?.
  by rewrite (orbC (typ_bv T1 x) (typ_bv T2 x)) -!orbA -IHT1 IHT2 !orbA (orbC (typ_bv T2 x)).
Qed.

Corollary typ_bv_subst s x T :
  (x \in typ_bv (typ_subst s T))
  = (x \in typ_bv T) || has (fun y => x \in typ_bv (s y)) (typ_enum_fv T [::]).
Proof. by rewrite -typ_bv_subst_aux orbF. Qed.

Corollary typ_bv_subst_elim s T x :
  x \in typ_bv (typ_subst s T) ->
  x \in typ_bv T \/ exists2 y, x \in typ_bv (s y) & y \in typ_fv T.
Proof.
  rewrite typ_bv_subst => /orP [ | /hasP [ ? ] ];
  [ | rewrite typ_enum_fv_inE ]; eauto.
Qed.

Corollary typ_bv_subst_intro_sub s T x y :
  y \in typ_fv T ->
  x \in typ_bv (s y) ->
  x \in typ_bv (typ_subst s T).
Proof.
  rewrite typ_bv_subst -typ_enum_fv_inE => ? ?.
  apply /orP /or_intror /hasP. eauto.
Qed.

Lemma typ_open_bvar T : typ_open typ_bvar T = T.
Proof. induction T => /=; congruence. Qed.

Lemma typ_open_ext s s' T :
  { in typ_bv T, s =1 s' } ->
  typ_open s T = typ_open s' T.
Proof.
  induction T => //= [ | Hext ].
  - apply. by rewrite inE eqxx.
  - congr (typ_arrow _ _); [ apply /IHT1 | apply /IHT2 ] => ?;
    rewrite -topredE => /= Hin; apply /Hext; by rewrite inE Hin ?orbT.
Qed.

Corollary typ_open_bvar_eq s T :
  { in typ_bv T, s =1 typ_bvar } ->
  typ_open s T = T.
Proof.
  move => /typ_open_ext ->.
  by rewrite typ_open_bvar.
Qed.

Lemma typ_open_comp s s' T : typ_open s (typ_open s' T) = typ_open (typ_open s \o s') T.
Proof. induction T => /=; congruence. Qed.

Lemma typ_bv_open_aux s x : forall T acc,
  has (fun y => x \in typ_bv (s y)) (typ_enum_bv T acc)
  = (x \in typ_bv (typ_open s T)) || has (fun y => x \in typ_bv (s y)) acc.
Proof.
  elim => //= ? IHT1 ? IHT2 ?.
  by rewrite IHT1 IHT2 -orbA.
Qed.

Corollary typ_bv_open s T x :
  (x \in typ_bv (typ_open s T))
  = has (fun y => x \in typ_bv (s y)) (typ_enum_bv T [::]).
Proof. by rewrite typ_bv_open_aux orbF. Qed.

Lemma typ_bv_open_elim s T x :
  x \in typ_bv (typ_open s T) ->
  exists2 y, x \in typ_bv (s y) & y \in typ_bv T.
Proof.
  rewrite typ_bv_open => /hasP [ ? ].
  rewrite typ_enum_bv_inE. eauto.
Qed.

Lemma typ_fv_open_aux s x T acc :
  (x \in typ_fv (typ_open s T)) || has (fun y => x \in typ_fv (s y)) acc
  = (x \in typ_fv T) || has (fun y => x \in typ_fv (s y)) (typ_enum_bv T acc).
Proof.
  rewrite -!topredE /=.
  elim: T acc => //= T1 IHT1 T2 IHT2 ?.
  by rewrite (orbC (typ_fv T1 x) (typ_fv T2 x)) -!orbA -IHT1 IHT2 !orbA (orbC (typ_fv T2 x)).
Qed.

Corollary typ_fv_open s x T :
  (x \in typ_fv (typ_open s T))
  = (x \in typ_fv T) || has (fun y => x \in typ_fv (s y)) (typ_enum_bv T [::]).
Proof. by rewrite -typ_fv_open_aux orbF. Qed.

Corollary typ_fv_open_elim s T x :
  x \in typ_fv (typ_open s T) ->
  x \in typ_fv T \/ exists2 y, x \in typ_fv (s y) & y \in typ_bv T.
Proof.
  rewrite typ_fv_open => /orP [ | /hasP [ ? ] ];
  [ | rewrite typ_enum_bv_inE ]; eauto.
Qed.

Lemma typ_subst_open_distr s s' T :
  (forall x, x \in typ_fv T -> forall y, y \in typ_bv (s x) -> s' y = typ_bvar y) ->
  typ_subst s (typ_open s' T) = typ_open (typ_subst s \o s') (typ_subst s T).
Proof.
  induction T => //= Hclose.
  - rewrite typ_open_bvar_eq => //= ? ?.
    by rewrite (Hclose x) // inE eqxx.
  - congr (typ_arrow _ _ ); [ rewrite IHT1 | rewrite IHT2 ] => // ?;
    rewrite -topredE => /= Hin ?;
    apply /Hclose; by rewrite inE Hin ?orbT.
Qed.

Lemma typ_open_subst_distr s s' T :
  (forall x, x \in typ_bv T -> forall y, y \in typ_fv (s x) -> s' y = typ_fvar y) ->
  typ_open s (typ_subst s' T) = typ_subst (typ_open s \o s') (typ_open s T).
Proof.
  induction T => //= Hfresh.
  - rewrite typ_subst_fvar_eq => //= ? ?.
    by rewrite (Hfresh n) //= inE eqxx.
  - congr (typ_arrow _ _ ); [ rewrite IHT1 | rewrite IHT2 ] => // ?;
    rewrite -topredE => /= Hin ?;
    apply /Hfresh; by rewrite inE Hin ?orbT.
Qed.


Lemma typ_subst_single_notin S T x (Hnotin : x \notin typ_fv T) :
  typ_subst [eta typ_fvar with x |-> S] T = T.
Proof.
  rewrite typ_subst_fvar_eq => // y /= Hin.
  by move: (@eqP _ y x) Hin Hnotin => [ -> -> | ].
Qed.

Lemma unifies_occur_aux s x : forall T,
  x \in typ_fv T -> typ_size (typ_subst s T) <= typ_size (s x) -> T = typ_fvar x.
Proof.
  elim => /= [ ? | ? | ? IHT1 ? IHT2 ].
  - by rewrite inE => /eqP <-.
  - by rewrite inE.
  - rewrite inE => /orP [ /IHT1 | /IHT2 ] IH Hsize;
    move: IH (Hsize) => -> /=.
    + by rewrite ltnNge leq_addr.
    + exact: (leq_trans (leq_addr _ _) (ltnW Hsize)).
    + by rewrite ltnNge leq_addl.
    + exact: (leq_trans (leq_addl _ _) (ltnW Hsize)).
Qed.

Corollary unifies_occur s T x :
  s x = typ_subst s T ->
  x \in typ_fv T ->
  T = typ_fvar x.
Proof.
  move => Hsize /(unifies_occur_aux s).
  rewrite Hsize leqnn. eauto.
Qed.

Definition typ_subst_seq := foldl (fun S '(x, T) => typ_subst [eta typ_fvar with x |-> T] S).

Lemma typ_subst_seq_arrow : forall s T1 T2,
  typ_subst_seq (typ_arrow T1 T2) s = typ_arrow (typ_subst_seq T1 s) (typ_subst_seq T2 s).
Proof. elim => //= [ [ ? ? ] ? IH ? ? ]. by rewrite IH. Qed.

Lemma typ_subst_seq_bvar x : forall s,
  typ_subst_seq (typ_bvar x) s = typ_bvar x.
Proof. by elim => [ | [ ] ]. Qed.

Corollary typ_subst_seq_cat : forall T s s',
  typ_subst_seq T (s ++ s') = typ_subst_seq (typ_subst_seq T s) s'.
Proof. exact: foldl_cat. Qed.

Lemma typ_subst_seq_typ_subst : forall s T,
  typ_subst_seq T s = typ_subst (typ_subst_seq^~s \o typ_fvar) T.
Proof.
  elim => [ | [ ? ? ] ? IH ] /= ?.
  - by rewrite typ_subst_fvar.
  - rewrite IH typ_subst_comp.
    apply /typ_subst_ext => ? ? /=.
    by rewrite -IH.
Qed.

Section UnifyInner.
  Variable unify : typ -> typ -> seq (nat * typ) -> option (seq (nat * typ)).

  Definition flex_flex x y s :=
    if x == y then Some s
    else
      match s with
      | [::] => Some [:: (x, typ_fvar y)]
      | (z, T) :: s =>
          omap (cons (z, T))
            (unify
              (typ_subst [eta typ_fvar with z |-> T] (typ_fvar x))
              (typ_subst [eta typ_fvar with z |-> T] (typ_fvar y)) s)
      end.

  Definition flex_rigid x T2 s :=
    match s with
    | [::] =>
        if x \in typ_fv T2 then None
        else Some [:: (x, T2)]
    | (z, T) :: s =>
        omap (cons (z, T))
          (unify
            (typ_subst [eta typ_fvar with z |-> T] (typ_fvar x))
            (typ_subst [eta typ_fvar with z |-> T] T2) s)
    end.

  Fixpoint typ_unify_inner T1 T2 s :=
    match T1, T2 with
    | typ_fvar x, typ_fvar y => flex_flex x y s
    | typ_fvar x, _ => flex_rigid x T2 s
    | _, typ_fvar y => flex_rigid y T1 s
    | typ_arrow T11 T12, typ_arrow T21 T22 =>
        oapp (typ_unify_inner T11 T21) None (typ_unify_inner T12 T22 s)
    | typ_bvar x, typ_bvar y =>
        if x == y then Some s else None
    | typ_bvar _, typ_arrow _ _ => None
    | typ_arrow _ _, typ_bvar _ => None
    end.

  Hypothesis typ_unify_sound :
    forall T1 T2 s s',
    unify T1 T2 s = Some s' ->
    exists s'', s' = s ++ s'' /\
    typ_subst_seq T1 s' = typ_subst_seq T2 s'.

  Lemma flex_rigid_sound x T2 s' : forall s,
    flex_rigid x T2 s = Some s' ->
    exists s'', s' = s ++ s'' /\
    typ_subst_seq (typ_fvar x) s' = typ_subst_seq T2 s'.
  Proof.
    move => [ | [ z T ] s ] /=.
    - destruct (x \in typ_fv T2) eqn:Hin; inversion 1 => /=.
      rewrite eqxx typ_subst_single_notin ?Hin; eauto.
    - destruct
        (unify (if x == z then T else typ_fvar x)
          (typ_subst [eta typ_fvar with z |-> T] T2) s) eqn:Heq;
      rewrite Heq; inversion 1 => /=.
      move: (typ_unify_sound _ _ _ _ Heq) => [ ? [ -> -> ] ]. eauto.
  Qed.

  Lemma flex_flex_sound x y s s' :
    flex_flex x y s = Some s' ->
    exists s'', s' = s ++ s'' /\
    typ_subst_seq (typ_fvar x) s' = typ_subst_seq (typ_fvar y) s'.
  Proof.
    move: (flex_rigid_sound x (typ_fvar y) s' s).
    rewrite /flex_flex /flex_rigid /= inE.
    case (@eqP _ x y); eauto.
    inversion 3. subst.
    exists [::]. by rewrite cats0.
  Qed.

  Lemma typ_unify_inner_sound :
    forall T1 T2 s s',
    typ_unify_inner T1 T2 s = Some s' ->
    exists s'', s' = s ++ s'' /\
    typ_subst_seq T1 s' = typ_subst_seq T2 s'.
  Proof.
    elim => /=
      [ x [ y ? ? /flex_flex_sound | ? ? ? /flex_rigid_sound | ? ? ? ? /flex_rigid_sound ]
      | x [ ? ? ? /flex_rigid_sound [ ? [ -> -> ] ] | y ? ? | ]
      | T11 IHT11 T12 IHT12 [ ? ? ? /flex_rigid_sound [ ? [ -> -> ] ] | | T21 T22 s ? ] ] //; eauto.
    - case (@eqP _ x y) => [ -> | ? ]; inversion 1.
      exists [::]. by rewrite cats0.
    - rewrite !typ_subst_seq_arrow.
      destruct (typ_unify_inner T12 T22 s) eqn:Heq => // /IHT11 [ ? [ -> -> ] ].
      rewrite !typ_subst_seq_cat.
      move: (IHT12 _ _ _ Heq) catA => [ ? [ -> -> ] ] <-. eauto.
  Qed.

  Fixpoint valid_subst_seq L s : Prop :=
    if s is (x, T) :: s
    then (x \in L) && (x \notin typ_fv T) /\ {subset typ_fv T <= L} /\ valid_subst_seq (rem x L) s
    else True.

  Variable L : seq nat.
  Variable typ_unify_complete :
    forall L',
    size L' < size L ->
    forall s s' T1 T2,
    uniq L' ->
    valid_subst_seq L' s ->
    {subset typ_fv T1 <= L'} ->
    {subset typ_fv T2 <= L'} ->
    typ_subst s' (typ_subst_seq T1 s)
    = typ_subst s' (typ_subst_seq T2 s) ->
    exists sd,
    valid_subst_seq L' (s ++ sd) /\
    unify T1 T2 s = Some (s ++ sd) /\
    exists s0, forall T,
    typ_subst s' T = typ_subst s0 (typ_subst_seq T sd).

  Lemma flex_rigid_complete x T2 : forall s s',
    uniq L ->
    valid_subst_seq L s ->
    x \in L ->
    {subset typ_fv T2 <= L} ->
    typ_subst s' (typ_subst_seq (typ_fvar x) s)
    = typ_subst s' (typ_subst_seq T2 s) ->
    T2 != typ_fvar x ->
    exists sd,
    valid_subst_seq L (s ++ sd) /\
    flex_rigid x T2 s = Some (s ++ sd) /\
    exists s0, forall T,
    typ_subst s' T = typ_subst s0 (typ_subst_seq T sd).
  Proof.
    move => [ | [ z T ] s ] /= s' Huniq =>
      [ ? | [ /andP [ Hz Hoccur ] [ HT Hvalid ] ] ] Hx HT2 Hunifies => [ | ? ].
    - destruct (x \in typ_fv T2) eqn:Hoccur.
      { by rewrite (unifies_occur _ _ _ Hunifies Hoccur) eqxx. }
      exists [:: (x, T2)] => /=. rewrite Hx Hoccur. repeat split; eauto.
      exists s' => ?.
      rewrite typ_subst_comp.
      apply /typ_subst_ext => z ? /=.
      by case (@eqP _ z x) => [ -> | ].
    - rewrite Hz Hoccur /=.
      have := typ_unify_complete _ _ _ _ _ _ (rem_uniq _ Huniq) Hvalid _ _ Hunifies.
      case => [ | y | y | sd [ ? [ -> /= ] ] ].
      { rewrite size_rem // prednK //.
        case (posnP (size L)) => [ /size0nil ? | // ]. subst.
        by move: in_nil Hz => ->. }
      { rewrite rem_filter // mem_filter /=.
        case (@eqP _ x z) => [ | /eqP ] ? /=; subst.
        - case (@eqP _ y z) => [ -> | ? /HT // ].
          by rewrite (negbTE Hoccur).
        - rewrite inE => /eqP ?. subst.
          by rewrite Hx andbT. }
      { rewrite rem_filter // mem_filter /= => /typ_fv_subst_elim /= [ w ].
        case (@eqP _ w z) => /= [ | /eqP ] ?; subst.
        - case (@eqP _ y z) => /= [ -> | ? /HT // ].
          by rewrite (negbTE Hoccur).
        - rewrite inE => /eqP -> /HT2 ->.
          by rewrite andbT. }
      eauto 6.
  Qed.

  Lemma flex_flex_complete x y s s' :
    uniq L ->
    valid_subst_seq L s ->
    x \in L ->
    y \in L ->
    typ_subst s' (typ_subst_seq (typ_fvar x) s)
    = typ_subst s' (typ_subst_seq (typ_fvar y) s) ->
    exists sd,
    valid_subst_seq L (s ++ sd) /\
    flex_flex x y s = Some (s ++ sd) /\
    exists s0, forall T,
    typ_subst s' T = typ_subst s0 (typ_subst_seq T sd).
  Proof.
    move => ? ? ? Hy ?.
    move: (flex_rigid_complete x (typ_fvar y) s s').
    rewrite /flex_rigid /flex_flex /= inE.
    case (@eqP _ x y) => ?; subst.
    - exists [::]. rewrite cats0. eauto.
    - apply => // [ ? | ].
      + rewrite inE => /eqP ?. by subst.
      + apply /eqP. congruence.
  Qed.

  Theorem typ_unify_inner_complete :
    forall T1 T2 s s',
    uniq L ->
    valid_subst_seq L s ->
    { subset typ_fv T1 <= L } ->
    { subset typ_fv T2 <= L } ->
    typ_subst s' (typ_subst_seq T1 s) = typ_subst s' (typ_subst_seq T2 s) ->
    exists sd,
    valid_subst_seq L (s ++ sd) /\
    typ_unify_inner T1 T2 s = Some (s ++ sd) /\
    exists s0, forall T,
    typ_subst s' T = typ_subst s0 (typ_subst_seq T sd).
  Proof.
    elim => [ x | x | T11 IHT11 T12 IHT12 ] [ y | y | T21 T22 ] /= s s' Huniq Hvalid HT1 HT2 Hunifies.
    - apply /flex_flex_complete => //=.
      + apply /HT1. by rewrite inE.
      + apply /HT2. by rewrite inE.
    - apply /flex_rigid_complete => //=.
      apply /HT1. by rewrite inE.
    - apply /flex_rigid_complete => //=.
      apply /HT1. by rewrite inE.
    - apply /flex_rigid_complete => //=.
      apply /HT2. by rewrite inE.
    - case (@eqP _ x y).
      + exists [::]. rewrite cats0. eauto.
      + move: Hunifies. rewrite !typ_subst_seq_bvar /=. congruence.
    - move: Hunifies. rewrite typ_subst_seq_arrow typ_subst_seq_bvar //.
    - apply /flex_rigid_complete => //=.
      apply /HT2. by rewrite inE.
    - move: Hunifies. rewrite typ_subst_seq_arrow typ_subst_seq_bvar //.
    - move: Hunifies. rewrite !typ_subst_seq_arrow. inversion 1.
      case (IHT12 T22 s s') => // [ ? | ? | sd [ ? [ -> /= [ s'' Hgen ] ] ] ].
      { rewrite -topredE => /= Hin. by rewrite HT1 // inE Hin orbT. }
      { rewrite -topredE => /= Hin. by rewrite HT2 // inE Hin orbT. }
      case (IHT11 T21 (s ++ sd) s'') => // [ ? | ? | | ? [ ] ].
      { rewrite -topredE => /= Hin. by rewrite HT1 // inE Hin. }
      { rewrite -topredE => /= Hin. by rewrite HT2 // inE Hin. }
      { by rewrite !typ_subst_seq_cat -!Hgen. }
      rewrite -!catA => ? [ -> [ sd' Hgen' ] ].
      (repeat eexists; eauto) => ?.
      by rewrite Hgen Hgen' typ_subst_seq_cat.
  Qed.

  Definition bound_subst_seq : seq (nat * typ) -> Prop :=
    foldr (fun '(_, T) => and {subset typ_bv T <= L}) True.

  Hypothesis typ_bv_unify :
    forall T1 T2 s s',
    bound_subst_seq s ->
    {subset typ_bv T1 <= L} ->
    {subset typ_bv T2 <= L} ->
    unify T1 T2 s = Some s' ->
    bound_subst_seq s'.

  Lemma flex_rigid_bound x T2 s' : forall s,
    bound_subst_seq s ->
    {subset typ_bv T2 <= L} ->
    flex_rigid x T2 s = Some s' ->
    bound_subst_seq s'.
  Proof.
    move => [ ? ? /= | [ z T ] s /= [ HT ? ] HT2 ].
    - by case (x \in typ_fv T2); inversion 1.
    - destruct (unify (if x == z then T else typ_fvar x) (typ_subst [eta typ_fvar with z |-> T] T2)) eqn:Hunify; inversion 1.
      split; eauto.
      refine (typ_bv_unify _ _ _ _ _ _ _ Hunify) => // ? => [ | /typ_bv_subst_elim [ /HT2 // | [ y /= ] ] ].
      + by case (x == z) => // /HT.
      + by case (y == z) => // /HT.
  Qed.

  Lemma flex_flex_bound x y s s' :
    bound_subst_seq s ->
    flex_flex x y s = Some s' ->
    bound_subst_seq s'.
  Proof.
    move: (flex_rigid_bound x (typ_fvar y) s' s).
    rewrite /flex_rigid /flex_flex /= inE.
    case (x == y) => [ | Hflex_rigid ? ].
    - inversion 3. subst. eauto.
    - exact /Hflex_rigid.
  Qed.

  Lemma typ_unify_inner_bound : forall T1 T2 s s',
    bound_subst_seq s ->
    {subset typ_bv T1 <= L} ->
    {subset typ_bv T2 <= L} ->
    typ_unify_inner T1 T2 s = Some s' ->
    bound_subst_seq s'.
  Proof.
    elim =>
      [ ? [ ? ? ? ? ? ? /flex_flex_bound | ? ? ? ? ? ? /flex_rigid_bound | ? ? ? ? ? ? ? /flex_rigid_bound ]
      | x [ ? ? ? ? ? ? /flex_rigid_bound | y ? ? ? ? ? | ]
      | T11 IHT11 T12 IHT12 [ ? ? ? ? ? ? /flex_rigid_bound | | T21 T22 s ? ? HT1 HT2 ] ] //=; eauto.
    - by case (x == y); inversion 1; subst.
    - destruct (typ_unify_inner T12 T22 s) eqn:Hunify => //=.
      apply /IHT11 => [ | ? | ? ].
      + refine (IHT12 _ _ _ _ _ _ Hunify) => // ?;
        rewrite -topredE => /= Hin;
        [ apply /HT1 | apply /HT2 ]; by rewrite /= inE Hin orbT.
      + rewrite -topredE => /= Hin. apply /HT1. by rewrite /= inE Hin.
      + rewrite -topredE => /= Hin. apply /HT2. by rewrite /= inE Hin.
  Qed.
End UnifyInner.

Fixpoint typ_unify_outer n T1 T2 s :=
  if n is n.+1
  then typ_unify_inner (typ_unify_outer n) T1 T2 s
  else if T1 == T2 then Some s else None.

Lemma typ_unify_outer_sound : forall n T1 T2 s s',
  typ_unify_outer n T1 T2 s = Some s' ->
  exists s'', s' = s ++ s'' /\
  typ_subst_seq T1 s' = typ_subst_seq T2 s'.
Proof.
  elim => /= [ T1 T2 ? ? | ? /typ_unify_inner_sound // ].
  case (@eqP _ T1 T2) => // ->. inversion 1. exists [::]. rewrite cats0. eauto.
Qed.

Lemma typ_unify_outer_complete :
  forall L n s s' T1 T2,
  size L <= n ->
  uniq L ->
  valid_subst_seq L s ->
  { subset typ_fv T1 <= L } ->
  { subset typ_fv T2 <= L } ->
  typ_subst s' (typ_subst_seq T1 s) = typ_subst s' (typ_subst_seq T2 s) ->
  exists sd,
  valid_subst_seq L (s ++ sd) /\
  typ_unify_outer n T1 T2 s = Some (s ++ sd) /\
  exists s0, forall T,
  typ_subst s' T = typ_subst s0 (typ_subst_seq T sd).
Proof.
  elim /(well_founded_induction (Wf_nat.well_founded_ltof _ (@size nat)))
    => L IH n s s' T1 T2 Hleq Huniq Hvalid HT1 HT2 Hunifies.
  case (posnP n) => [ ? | Hpos ]; subst => /=.
  - rewrite (_ : T1 == T2).
    { exists [::]. rewrite cats0 /=. eauto. }
    move: leqn0 Hleq Hunifies => -> /eqP /size0nil ?. subst.
    by rewrite !typ_subst_seq_typ_subst !typ_subst_comp !typ_subst_fvar_eq => [ -> | ? /HT2 | ? /HT1 ].
  - rewrite -(prednK Hpos) /=.
    apply /typ_unify_inner_complete => // ? Hlt ? ? ? ?.
    apply /IH.
    + exact /ltP.
    + rewrite -ltnS (prednK Hpos).
      exact: (leq_trans Hlt).
Qed.

Lemma typ_unify_outer_bound L :
  forall n T1 T2 s s',
  bound_subst_seq L s ->
  {subset typ_bv T1 <= L} ->
  {subset typ_bv T2 <= L} ->
  typ_unify_outer n T1 T2 s = Some s' ->
  bound_subst_seq L s'.
Proof.
  elim => /= [ T1 T2 ? ?  | ? IH ].
  - by case (T1 == T2); inversion 4; subst.
  - exact /typ_unify_inner_bound.
Qed.

Definition typ_unify T1 T2 :=
  omap (fun s => typ_subst_seq^~s \o typ_fvar) (typ_unify_outer (size (typ_enum_fv T1 (typ_enum_fv T2 [::]))) T1 T2 [::]).

Lemma valid_subst_seq_fv : forall s L,
  uniq L ->
  valid_subst_seq L s ->
  forall x T, x \in typ_fv (typ_subst_seq T s) -> (x \in typ_fv T) || (x \in L).
Proof.
  elim => /= [ ? ? ? ? ? -> // | [ y ? ] ? IH ? Huniq [ /andP [ ? ? ] [ HT0 Hvalid ] ] ? ? /(IH _ (rem_uniq _ Huniq) Hvalid) /orP [ /typ_fv_subst_elim /= [ x ] | ] ].
  - case (@eqP _ x y) => /= [ -> /HT0 -> | ? ].
    + by rewrite orbT.
    + by rewrite inE => /eqP -> ->.
  - rewrite (rem_filter _ Huniq) mem_filter => /= /andP [ ? -> ].
    by rewrite orbT.
Qed.

Theorem typ_unify_sound T1 T2 s :
  typ_unify T1 T2 = Some s ->
  typ_subst s T1 = typ_subst s T2.
Proof.
  rewrite /typ_unify.
  destruct (typ_unify_outer (size (typ_enum_fv T1 (typ_enum_fv T2 [::]))) T1 T2 [::]) eqn:Hunify; inversion 1. subst.
  move: (typ_unify_outer_sound _ _ _ _ _ Hunify) => /= [ ? [ ?  ] ].
  by rewrite !typ_subst_seq_typ_subst.
Qed.

Lemma typ_unify_complete_aux T1 T2 s :
  typ_subst s T1 = typ_subst s T2 ->
  exists s', typ_unify T1 T2 = Some s' /\
  (exists s0, forall T, typ_subst s T = typ_subst s0 (typ_subst s' T)) /\
  (forall x y, x \in typ_fv (s' y) -> x = y \/ x \in typ_fv T1 \/ x \in typ_fv T2).
Proof.
  move => Hunifies.
  rewrite /typ_unify.
  case (typ_unify_outer_complete (undup (typ_enum_fv T1 (typ_enum_fv T2 [::]))) (size (typ_enum_fv T1 (typ_enum_fv T2 [::]))) [::] s T1 T2)
    => //= [ | | ? | ? | ? [ Hvalid [ -> [ ? Hgen ] ] ] ].
  - by rewrite size_undup.
  - exact: undup_uniq.
  - by rewrite mem_undup typ_enum_fv_inE_aux => ->.
  - rewrite mem_undup !typ_enum_fv_inE_aux => ->. exact: orbT.
  - (repeat eexists) => [ ? | ? ? /(valid_subst_seq_fv _ _ (undup_uniq _) Hvalid) /= /orP [ ] ].
    + by rewrite Hgen typ_subst_seq_typ_subst.
    + rewrite inE => /eqP; eauto.
    + rewrite mem_undup !typ_enum_fv_inE_aux in_nil => /orP [ -> | /orP [ -> | // ] ]; eauto.
Qed.

Theorem typ_unify_complete T1 T2 s :
  typ_subst s T1 = typ_subst s T2 ->
  exists s', typ_unify T1 T2 = Some s' /\
  exists s0, forall T, typ_subst s T = typ_subst s0 (typ_subst s' T).
Proof.
  move => /typ_unify_complete_aux [ ? [ -> [ ] ] ].
  repeat (eexists; eauto).
Qed.

Theorem typ_fv_unify T1 T2 s (Hunify : typ_unify T1 T2 = Some s) :
  forall x y, x \in typ_fv (s y) -> x = y \/ x \in typ_fv T1 \/ x \in typ_fv T2.
Proof.
  move: (typ_unify_sound _ _ _ Hunify) (Hunify) => /typ_unify_complete_aux [ ? [ -> [ ] ] ].
  inversion 3. by subst.
Qed.

Theorem typ_bv_unify T1 T2 s :
  typ_unify T1 T2 = Some s ->
  forall x y, y \in typ_bv (s x) -> y \in typ_bv T1 \/ y \in typ_bv T2.
Proof.
  rewrite /typ_unify.
  have H : forall s L, bound_subst_seq L s -> forall x T, { subset typ_bv T <= L } -> x \in typ_bv (typ_subst_seq T s) -> x \in L.
  { elim => [ ? ? ? ? | [ y ? ] ? IH ? /= [ HT0 ? ] ? ? HT  ].
    - apply.
    - apply /IH => // ? /typ_bv_subst_elim [ /HT | [ x ] ] //=.
      by case (x == y) => // /HT0. }
  destruct (typ_unify_outer (size (typ_enum_fv T1 (typ_enum_fv T2 [::]))) T1 T2 [::]) eqn:Hunify; inversion 1 => ? x Hbv.
  have : x \in typ_enum_bv T1 (typ_enum_bv T2 [::]).
  { apply: H Hbv => //.
    apply: typ_unify_outer_bound Hunify => // ?; rewrite !typ_enum_bv_inE_aux => -> //.
    by rewrite orbT. }
  rewrite !typ_enum_bv_inE_aux in_nil => /orP [ -> | /orP [ -> | // ] ]; eauto.
Qed.
