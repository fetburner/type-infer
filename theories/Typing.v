From mathcomp Require Import all_ssreflect.
Require Import Types Term.

Definition env := list typ.
Definition store := env.

Definition env_fv G : pred nat := fun x => has (typ_fv^~x) G.
Definition env_bv G : pred nat := fun x => has (typ_bv^~x) G.

Definition env_enum_fv G := (foldr typ_enum_fv)^~G.
Definition env_enum_bv G := (foldr typ_enum_bv)^~G.

Lemma env_enum_fv_inE_aux x : forall G acc,
  (x \in env_enum_fv G acc) = (x \in env_fv G) || (x \in acc).
Proof.
  elim => //= ? ? IH ?.
  by rewrite typ_enum_fv_inE_aux IH orbA.
Qed.

Corollary env_enum_fv_inE G x :
  (x \in env_enum_fv G [::]) = (x \in env_fv G).
Proof. by rewrite env_enum_fv_inE_aux orbF. Qed.

Lemma env_enum_bv_inE_aux x : forall G acc,
  (x \in env_enum_bv G acc) = (x \in env_bv G) || (x \in acc).
Proof.
  elim => //= ? ? IH ?.
  by rewrite typ_enum_bv_inE_aux IH orbA.
Qed.

Corollary env_enum_bv_inE G x :
  (x \in env_enum_bv G [::]) = (x \in env_bv G).
Proof. by rewrite env_enum_bv_inE_aux orbF. Qed.

Lemma env_fv_intro T x :
  x \in typ_fv T ->
  forall G, T \in G -> x \in env_fv G.
Proof.
  rewrite -topredE => /= ? ? ?.
  apply /hasP. eauto.
Qed.

Lemma env_bv_intro T x :
  x \in typ_bv T ->
  forall G, T \in G -> x \in env_bv G.
Proof.
  rewrite -topredE => /= ? ? ?.
  apply /hasP. eauto.
Qed.

Definition env_subst s := map (typ_subst s).
Definition env_open s := map (typ_open s).

Lemma env_subst_fvar G : env_subst typ_fvar G = G.
Proof.
  rewrite /env_subst map_id_in // => ? ?.
  by rewrite typ_subst_fvar.
Qed.

Lemma env_open_bvar G : env_open typ_bvar G = G.
Proof.
  rewrite /env_open map_id_in // => ? ?.
  by rewrite typ_open_bvar.
Qed.

Lemma env_subst_ext s s' G
  (Hext : { in env_fv G, s =1 s' }) :
  env_subst s G = env_subst s' G.
Proof.
  apply /eq_in_map => ? ?.
  apply /typ_subst_ext => ? ?.
  apply /Hext /env_fv_intro; eauto.
Qed.

Lemma env_open_ext s s' G
  (Hext : { in env_bv G, s =1 s' }) :
  env_open s G = env_open s' G.
Proof.
  apply /eq_in_map => ? ?.
  apply /typ_open_ext => ? ?.
  apply /Hext /env_bv_intro; eauto.
Qed.

Corollary env_subst_fvar_eq s G :
  { in env_fv G, s =1 typ_fvar } ->
  env_subst s G = G.
Proof.
  move => /env_subst_ext ->.
  exact /env_subst_fvar.
Qed.

Corollary env_open_bvar_eq s G :
  { in env_bv G, s =1 typ_bvar } ->
  env_open s G = G.
Proof.
  move => /env_open_ext ->.
  exact /env_open_bvar.
Qed.

Lemma env_subst_comp s s' G :
  env_subst s (env_subst s' G) = env_subst (typ_subst s \o s') G.
Proof.
  rewrite /env_subst -map_comp.
  exact /eq_map /typ_subst_comp.
Qed.

Lemma env_open_comp s s' G :
  env_open s (env_open s' G) = env_open (typ_open s \o s') G.
Proof.
  rewrite /env_open -map_comp.
  exact /eq_map /typ_open_comp.
Qed.

Lemma env_fv_subst_elim s x : forall G,
  x \in env_fv (env_subst s G) ->
  exists2 y, x \in typ_fv (s y) & y \in env_fv G.
Proof.
  elim => //= ? ? IH /orP [ /typ_fv_subst_elim | /IH ] [ y ? ];
  rewrite -topredE => /= Hin; exists y; by rewrite // -topredE /= Hin ?orbT.
Qed.

Lemma env_fv_subst_intro s x y : forall G,
  y \in env_fv G ->
  x \in typ_fv (s y) ->
  x \in env_fv (env_subst s G).
Proof.
  elim => //= ? ? IH /orP [ ] Hin => [ /(typ_fv_subst_intro _ _ _ _ Hin) | /(IH Hin) ];
  rewrite -!topredE => /= -> //.
  by rewrite orbT.
Qed.

Lemma env_bv_open s x : forall G,
  x \in env_bv (env_open s G) ->
  exists2 y, x \in typ_bv (s y) & y \in env_bv G.
Proof.
  elim => //= ? ? IH /orP [ /typ_bv_open_elim | /IH ] [ y ? ];
  rewrite -topredE => /= Hin; exists y; by rewrite // -topredE /= Hin ?orbT.
Qed.


Inductive typed M : env -> trm -> typ -> Prop :=
  | typed_unit G :
      typed M G trm_unit typ_unit
  | typed_var G x s T :
      (forall d, nth d G x = T) ->
      (forall x, typ_bv (s x) =i pred0) ->
      typed M G (trm_var x) (typ_open s T)
  | typed_loc G l T :
      typ_bv T =i pred0 ->
      (forall d, nth d M l = T) ->
      typed M G (trm_loc l) (typ_ref T)
  | typed_abs G t T1 T2 :
      typ_bv T1 =i pred0 ->
      typed M (T1 :: G) t T2 ->
      typed M G (trm_abs t) (typ_arrow T1 T2)
  | typed_app G t1 t2 T1 T2 :
      typed M G t1 (typ_arrow T1 T2) ->
      typed M G t2 T1 ->
      typed M G (trm_app t1 t2) T2
  | typed_ref G t T :
      typed M G t T ->
      typed M G (trm_ref t) (typ_ref T)
  | typed_deref G t T :
      typed M G t (typ_ref T) ->
      typed M G (trm_deref t) T
  | typed_update G t1 t2 T :
      typed M G t1 (typ_ref T) ->
      typed M G t2 T ->
      typed M G (trm_update t1 t2) typ_unit
  | typed_let (L : seq nat) G t1 t2 T1 T2 :
      value t1 ->
      (forall s,
        (forall x, exists2 y, s x = typ_fvar y & y \notin L) ->
        typed M G t1 (typ_open s T1)) ->
      typed M (T1 :: G) t2 T2 ->
      typed M G (trm_let t1 t2) T2.
Hint Constructors typed.

Lemma typed_closed M G t T :
  typed M G t T ->
  typ_bv T =i pred0.
Proof.
  induction 1 => //= n.
  - rewrite typ_bv_open.
    apply /negbTE /negP => /hasP [ ? ].
    by rewrite H0 inE.
  - move: (H n) (IHtyped n).
    by rewrite -!topredE => /= -> ->.
  - move: (IHtyped1 n).
    rewrite -!topredE => /= /negbT.
    by rewrite negb_or => /andP [ ? ] /negbTE.
Qed.

Lemma typed_weaken M G t T :
  typed M G t T ->
  forall M' G',
  (forall x T, (forall d, nth d M x = T) -> (forall d, nth d M' x = T)) ->
  (forall x T, (forall d, nth d G x = T) -> exists2 '(s, T'), (forall d, nth d G' x = T') & T = typ_open s T') ->
  typed M' G' t T.
Proof.
  induction 1 => /= M' G' HM' HG'; eauto.
  - case (HG' _ _ H) => [ [ ? ? ] ? -> ].
    rewrite typ_open_comp.
    apply /typed_var => // ? n.
    rewrite typ_bv_open.
    apply /negbTE /negP => /hasP [ ? ].
    by rewrite H0 inE.
  - apply /typed_abs => //.
    apply /IHtyped => [ | [ ? | ] /= ]; eauto.
    eexists (_, _); eauto.
    exact /Logic.eq_sym /typ_open_bvar.
  - apply /typed_let; eauto.
    apply /IHtyped => [ | [ ? | ] /= ]; eauto.
    eexists (_, _); eauto.
    exact /Logic.eq_sym /typ_open_bvar.
Qed.

Corollary typed_weaken_env M G t T :
  typed M G t T ->
  forall G',
  (forall x T, (forall d, nth d G x = T) -> exists2 '(s, T'), (forall d, nth d G' x = T') & T = typ_open s T') ->
  typed M G' t T.
Proof.
  move => Htyped ?.
  exact /(typed_weaken _ _ _ _ Htyped).
Qed.

Corollary typed_weaken_store M G t T :
  typed M G t T ->
  forall M',
  (forall x T, (forall d, nth d M x = T) -> (forall d, nth d M' x = T)) ->
  typed M' G t T.
Proof.
  move => Htyped ? Hstore.
  apply /(typed_weaken _ _ _ _ Htyped _ _ Hstore) => ? ? ?.
  eexists (typ_bvar, _); eauto.
  by rewrite typ_open_bvar.
Qed.

Lemma typed_subst_typ M G t T :
  typed M G t T ->
  forall s,
  (forall x, typ_bv (s x) =i pred0) ->
  typed (env_subst s M) (env_subst s G) t (typ_subst s T).
Proof.
  induction 1 => s0 Hclosed /=; eauto.
  - rewrite typ_subst_open_distr => [ | ? ? ? ].
    + apply /typed_var => [ ? | ? ? ].
      * case (leqP (size G) x) => ?.
         { move: (H (typ_fvar 0)).
           by rewrite -(H (typ_bvar 0)) !nth_default // size_map. }
        by rewrite /env_subst (nth_map (typ_fvar 0)) // H.
      * rewrite typ_bv_subst H0.
        apply /negbTE /negP => /hasP [ ? ].
        by rewrite Hclosed.
    + by rewrite Hclosed.
  - apply /typed_loc => [ ? | ? ].
    + rewrite typ_bv_subst H.
      apply /negbTE /negP => /hasP [ ? ].
      by rewrite Hclosed.
    + case (leqP (size M) l) => ?.
      * move: (H0 (typ_fvar 0)).
        by rewrite -(H0 (typ_bvar 0)) !nth_default // size_map.
      * by rewrite /env_subst (nth_map (typ_fvar 0)) // H0.
  - apply /typed_abs => [ ? | ].
    + rewrite typ_bv_subst H.
      apply /negbTE /negP => /hasP [ ? ].
      by rewrite Hclosed.
    + exact /IHtyped.
  - apply /(typed_let _ (env_enum_fv M (env_enum_fv G (typ_enum_fv T1 L)))) => [ // | s' Hs' | ]; [ | exact /IHtyped ].
    rewrite -(typ_subst_ext (fun x => if (x \notin env_fv M) && (x \notin env_fv G) && (x \notin typ_fv T1) then typ_fvar x else s0 x)) => [ | ? -> /= ].
    + rewrite typ_open_subst_distr => [ | x ? ? ].
      { rewrite -(typ_subst_ext (fun x => if (x \notin env_fv M) && (x \notin env_fv G) && (x \notin typ_fv T1) then typ_fvar x else s0 x)) => [ | /= ? /typ_fv_open_elim [ -> /= | [ x [ ] ] ] ].
        - rewrite -!(env_subst_ext (fun x => if (x \notin env_fv M) && (x \notin env_fv G) && (x \notin typ_fv T1) then typ_fvar x else s0 x) s0) => [ | ? -> | ? -> // ].
          + apply /H1 => [ x | ? ? ].
            * case (Hs' x) => ? ->.
              rewrite !env_enum_fv_inE_aux typ_enum_fv_inE_aux !negb_or => /andP [ ? /andP [ ? /andP [ ] ] ]. eauto.
            * by rewrite 3!fun_if Hclosed /= if_same.
          + by rewrite andbF.
        - rewrite andbF typ_open_bvar_eq => // ?.
          by rewrite Hclosed.
        - case (Hs' x) => ? -> /=.
          rewrite !env_enum_fv_inE_aux typ_enum_fv_inE_aux !negb_or inE => /andP [ HM /andP [ HG /andP [ HT1 ? ] ] ] /eqP ?.
          subst. by rewrite HM HG HT1. }
      case (Hs' x) => ? [ -> /= ].
      rewrite !env_enum_fv_inE_aux typ_enum_fv_inE_aux !negb_or inE => /andP [ HM /andP [ HG /andP [ HT1 ? ] ] ] /eqP ?.
      subst. by rewrite HM HG HT1.
    + by rewrite andbF.
Qed.
Hint Resolve typed_subst_typ.

Definition maximum := foldr maxn 0.

Lemma maximum_sup : forall xs x, x \in xs -> x <= maximum xs.
Proof.
  elim => //= ? ? IH ?.
  rewrite in_cons => /orP [ /eqP <- | /IH ];
  rewrite leq_max ?leqnn // => ->.
  by rewrite orbT.
Qed.

Definition typ_gen {pT : predType nat} (L : pT) :=
  typ_subst (fun x => if x \in L then typ_fvar x else typ_bvar x).

Fixpoint typing n G t :=
  match t with
  | trm_unit => Some (n, typ_fvar, typ_unit)
  | trm_var x =>
      omap
        (fun T => ((n + maximum (typ_enum_bv T [::])).+1, typ_fvar, typ_open (typ_fvar \o addn n) T))
        (nth None (map Some G) x)
  | trm_loc _ => None
  | trm_abs t =>
      omap
        (fun '(m, s, T2) => (m, s, typ_arrow (s n) T2))
        (typing n.+1 (typ_fvar n :: G) t)
  | trm_app t1 t2 =>
      match typing n G t1 with
      | None => None
      | Some (n1, s1, T1) =>
          match typing n1 (env_subst s1 G) t2 with
          | None => None
          | Some (n2, s2, T2) =>
              omap
                (fun s3 => (n2.+1, typ_subst (typ_subst s3 \o s2) \o s1, s3 n2))
                (typ_unify (typ_subst s2 T1) (typ_arrow T2 (typ_fvar n2)))
          end
      end
  | trm_ref t =>
      omap (fun '(m, s, T) => (m, s, typ_ref T)) (typing n G t)
  | trm_deref t =>
      match typing n G t with
      | None => None
      | Some (n1, s1, T) =>
          omap
            (fun 's2 => (n1.+1, typ_subst s2 \o s1, s2 n1))
            (typ_unify T (typ_ref (typ_fvar n1)))
      end
  | trm_update t1 t2 =>
      match typing n G t1 with
      | None => None
      | Some (n1, s1, T1) =>
          match typing n1 (env_subst s1 G) t2 with
          | None => None
          | Some (n2, s2, T2) =>
              omap
                (fun s3 => (n2, typ_subst (typ_subst s3 \o s2) \o s1, typ_unit))
                (typ_unify (typ_subst s2 T1) (typ_ref T2))
          end
      end
  | trm_let t1 t2 =>
      if value t1 then
        match typing n G t1 with
        | None => None
        | Some (n1, s1, T1) =>
            match typing n1 (typ_gen (env_fv (env_subst s1 G)) T1 :: env_subst s1 G) t2 with
            | None => None
            | Some (n2, s2, T2) => Some (n2, typ_subst s2 \o s1, T2)
            end
        end
      else None
  end.

(* let f = fun x -> x in f f *)
Eval compute in (typing 0 [::] (trm_let (trm_abs (trm_var 0)) (trm_app (trm_var 0) (trm_var 0)))).
(* (fun f -> f f) (fun x -> x) *)
Eval compute in (typing 0 [::] (trm_app (trm_abs (trm_app (trm_var 0) (trm_var 0))) (trm_abs (trm_var 0)))).

Theorem typing_sound : forall t n m G s T,
  typing n G t = Some (m, s, T) ->
  typed [::] (env_subst s G) t T /\ forall x, typ_bv (s x) =i pred0.
Proof.
  elim => /=
    [ 
    | x ? ? G ? ?
    | //
    | t IHt n ? G ? ?
    | t1 IHt1 t2 IHt2 n ? G ? ?
    | t IHt n ? G ? ?
    | t IHt n ? G ? ?
    | t1 IHt1 t2 IHt2 n ? G ? ?
    | t1 IHt1 t2 IHt2 n ? G ? ? ].
  - by inversion 1 => /=.
  - case (leqP (size G) x) => ?.
    + by rewrite nth_default // size_map.
    + rewrite (nth_map (typ_fvar 0)) //. inversion 1.
      rewrite env_subst_fvar.
      split => [ | ? // ].
      apply /typed_var => // ?.
      exact /set_nth_default.
  - destruct (typing n.+1 (typ_fvar n :: G) t) as [ [ [ ? ? ] ] | ] eqn:Htyping; inversion 1. subst.
    move: (IHt _ _ _ _ _ Htyping) => [ ? ? ]. eauto.
  - destruct (typing n G t1) as [ [ [ n1 s1 ] T1 ] | ] eqn:Htyping1 => //.
    destruct (typing n1 (env_subst s1 G) t2) as [ [ [ n2 s2 ] T2 ] | ] eqn:Htyping2 => //.
    destruct (typ_unify (typ_subst s2 T1) (typ_arrow T2 (typ_fvar n2))) as [ s3 | ] eqn:Hunify; inversion 1. subst.
    case (IHt1 _ _ _ _ _ Htyping1) => ? Hs1bv.
    case (IHt2 _ _ _ _ _ Htyping2) => Htyped2 Hs2bv.
    have Htyped1' : typed [::] (env_subst s2 (env_subst s1 G)) t1 (typ_subst s2 T1).
    { exact /(typed_subst_typ [::]). }
    have : forall x, typ_bv (s3 x) =i pred0 => [ ? x | Hs3bv ].
    { apply /negbTE /negP => /(typ_bv_unify _ _ _ Hunify) [ | /= ].
      - by rewrite (typed_closed _ _ _ _ Htyped1').
      - move: (typed_closed _ _ _ _ Htyped2 x).
        by rewrite -!topredE => /= ->. }
    split => [ | ? ? ].
    + rewrite -!env_subst_comp.
      apply /(typed_app _ _ _ _ (typ_subst s3 T2)).
      * move: (typ_unify_sound _ _ _ Hunify) => /= <-.
        apply /(typed_subst_typ [::]); eauto.
      * apply /(typed_subst_typ [::]); eauto.
    + rewrite typ_bv_subst Hs1bv.
      apply /negbTE /negP => /hasP [ ? ? ].
      rewrite /= typ_bv_subst Hs2bv => /hasP [ ? ? ].
    by rewrite Hs3bv.
  - destruct (typing n G t) as [ [ [ m s ] T ] | ] eqn:Htyping; inversion 1. subst.
    case (IHt _ _ _ _ _ Htyping). eauto.
  - destruct (typing n G t) as [ [ [ n1 s1 ] T ] | ] eqn:Htyping => //.
    destruct (typ_unify T (typ_ref (typ_fvar n1))) as [ s2 | ] eqn:Hunify; inversion 1. subst.
    case (IHt _ _ _ _ _ Htyping) => Htyped Hs1bv.
    have : forall x, typ_bv (s2 x) =i pred0 => [ ? x | Hs2bv ].
    { apply /negbTE /negP => /(typ_bv_unify _ _ _ Hunify) [ | // ].
      by rewrite (typed_closed _ _ _ _ Htyped). }
    split => [ | ? ? ].
    + rewrite -!env_subst_comp.
      apply /typed_deref.
      move: (typ_unify_sound _ _ _ Hunify) => /= <-.
      exact /(typed_subst_typ [::]).
    + rewrite typ_bv_subst Hs1bv.
      apply /negbTE /negP => /hasP [ ? ? ].
      by rewrite Hs2bv.
  - destruct (typing n G t1) as [ [ [ n1 s1 ] T1 ] | ] eqn:Htyping1 => //.
    destruct (typing n1 (env_subst s1 G) t2) as [ [ [ n2 s2 ] T2 ] | ] eqn:Htyping2 => //.
    destruct (typ_unify (typ_subst s2 T1) (typ_ref T2)) as [ s3 | ] eqn:Hunify; inversion 1. subst.
    case (IHt1 _ _ _ _ _ Htyping1) => ? Hs1bv.
    case (IHt2 _ _ _ _ _ Htyping2) => Htyped2 Hs2bv.
    have Htyped1' : typed [::] (env_subst s2 (env_subst s1 G)) t1 (typ_subst s2 T1).
    { exact /(typed_subst_typ [::]). }
    have : forall x, typ_bv (s3 x) =i pred0 => [ ? x | Hs3bv ].
    { apply /negbTE /negP => /(typ_bv_unify _ _ _ Hunify) [ | /= ].
      - by rewrite (typed_closed _ _ _ _ Htyped1').
      - by rewrite (typed_closed _ _ _ _ Htyped2). }
    split => [ | ? ? ].
    + rewrite -!env_subst_comp.
      apply /(typed_update _ _ _ _ (typ_subst s3 T2));
      [ move: (typ_unify_sound _ _ _ Hunify) => /= <- | ];
      exact /(typed_subst_typ [::]).
    + rewrite typ_bv_subst Hs1bv.
      apply /negbTE /negP => /hasP [ ? ? ] /=.
      rewrite typ_bv_subst Hs2bv => /hasP [ ? ? ].
      by rewrite Hs3bv.
  - destruct (value t1) eqn:Hvalue => //.
    destruct (typing n G t1) as [ [ [ n1 s1 ] T1 ] | ] eqn:Htyping1 => //.
    destruct (typing n1 (typ_gen (env_fv (env_subst s1 G)) T1 :: env_subst s1 G) t2) as [ [ [ n2 s2 ] T2 ] | ] eqn:Htyping2; inversion 1. subst.
    case (IHt1 _ _ _ _ _ Htyping1) => Htyped1 Hclosed1.
    case (IHt2 _ _ _ _ _ Htyping2) => ? Hclosed2.
    split => [ | ? ? ].
    + rewrite -env_subst_comp.
      (apply /(typed_let _ (env_enum_fv (env_subst s1 G) [::])); eauto) => s Hs.
      rewrite typ_subst_comp typ_open_subst_distr => [ | ? ].
      { rewrite typ_open_bvar_eq => [ | ? ].
        - rewrite (env_subst_ext s2 (typ_open s \o (typ_subst s2 \o (fun x => if x \in env_fv (env_subst s1 G) then typ_fvar x else typ_bvar x)))) => [ | ? /= -> /= ].
          + apply /(typed_subst_typ [::]) => //= x ?.
            rewrite typ_bv_open.
            apply /negbTE /negP => /hasP [ y ].
            case (Hs y) => ? -> //.
          + rewrite typ_open_bvar_eq => // ?.
            by rewrite Hclosed2.
        - by rewrite (typed_closed _ _ _ _ Htyped1). }
      by rewrite (typed_closed _ _ _ _ Htyped1).
    + rewrite typ_bv_subst Hclosed1.
      apply /negbTE /negP => /hasP [ ? ].
      by rewrite Hclosed2.
Qed.

Theorem typing_complete : forall t n G s T,
  {in env_fv G, forall x, typ_bv (s x) =i pred0} ->
  (forall x, x \in env_fv G -> x < n) ->
  typed [::] (env_subst s G) t T ->
  exists m s' s'' T', typing n G t = Some (m, s', T')
    /\ n <= m
    /\ T = typ_subst s'' T'
    /\ typ_bv T' =i pred0
    /\ (forall x, typ_bv (s' x) =i pred0)
    /\ (forall x y, x \in typ_fv (s' y) -> x = y \/ x < m)
    /\ (forall x, x \in typ_fv T' -> x < m)
    /\ (forall x, x < n -> s x = typ_subst s'' (s' x)).
Proof.
  elim => /=
    [
    | x
    | l 
    | t IHt
    | t1 IHt1 t2 IHt2
    | t IHt
    | t IHt
    | t1 IHt1 t2 IHt2
    | t1 IHt1 t2 IHt2 ] n G s T Hclos HG; inversion 1; subst.
  - (repeat eexists; eauto) => /= ? ?.
    rewrite inE => /eqP. eauto.
  - case (leqP (size G) x) => ?.
    { move: (H1 (typ_fvar 0)).
      by rewrite -(H1 (typ_bvar 0)) !nth_default // size_map. }
    exists ((n + maximum (typ_enum_bv (nth (typ_fvar 0) G x) [::])).+1), typ_fvar, (fun x => if x < n then s x else s0 (x - n)), (typ_open (typ_fvar \o addn n) (nth (typ_fvar 0) G x)).
    (repeat split) => [ | | | ? | ? ? /= | ? /typ_fv_open_elim [ ? | [ ? /= ] ] | ? /= -> // ].
    + by rewrite (nth_map (typ_fvar 0)).
    + apply /leqW /leq_addr.
    + rewrite -(H1 (typ_fvar 0)) /env_subst (nth_map (typ_fvar 0)) // typ_subst_open_distr => [ | /= x0 ? ? ].
      { rewrite (typ_subst_ext (fun x => if x < n then s x else s0 (x - n)) s) => [ | ? ? ].
        - apply /typ_open_ext => ? ? /=.
          by rewrite ltnNge leq_addr /= addKn.
        - by rewrite HG // (env_fv_intro (nth (typ_fvar 0) G x)) // mem_nth. }
      by rewrite HG ?Hclos // (env_fv_intro (nth (typ_fvar 0) G x)) // mem_nth.
    + rewrite typ_bv_open.
      by apply /negbTE /negP => /hasP [ ? ].
    + rewrite inE => /eqP. eauto.
    + apply /leqW /ltn_addr /HG /(env_fv_intro (nth (typ_fvar 0) G x)) => //.
      exact /mem_nth.
    + rewrite inE => /eqP -> ?.
        by rewrite ltnS leq_add2l maximum_sup // typ_enum_bv_inE_aux in_nil orbF.
  - move: (H3 typ_unit).
    by rewrite -(H3 (typ_fvar 0)) !nth_default.
  - move: (IHt n.+1 (typ_fvar n :: G) (fun x => if x < n then s x else T1) T2) => /= [ ? /orP [ /eqP -> | Hin ] | ? /orP [ /eqP -> | /HG /leqW // ] | | n1 [ s1 [ s' [ T' [ -> [ Hn1 [ -> [ HT'bv [ Hs1bv [ Hs1fv [ HT'fv Hs1 ] ] ] ] ] ] ] ] ] ] ].
    { by rewrite ltnn. }
    { rewrite HG //. exact /Hclos /Hin. }
    { exact /leqnn. }
    { by rewrite ltnn -(env_subst_ext s) => // ? /HG ->. }
    exists n1, s1, s', (typ_arrow (s1 n) T').
    (repeat split) => //= [ | | x | ? | ? Hlt ].
    + exact /ltnW.
    + by rewrite -Hs1 // ltnn.
    + move: (HT'bv x) (Hs1bv n x).
      by rewrite -!topredE => /= -> ->.
    + by rewrite inE => /orP [ /Hs1fv [ -> | ] | /HT'fv ].
    + rewrite -Hs1 ?Hlt => //. exact /leqW.
  - move: (IHt1 n G s (typ_arrow T1 T)) => [ ] // n1 [ s1 [ s' [ T2' [ -> [ Hn1 [ HT [ HT2'bv [ Hs1bv [ Hs1fv [ HTfv Hs ] ] ] ] ] ] ] ] ] ].
    move: (IHt2 n1 (env_subst s1 G) s' T1) => [ ? /env_fv_subst_elim [ x ? ? ] z | ? /env_fv_subst_elim [ ? /Hs1fv [ -> /HG /((@leq_trans _ _ _)^~Hn1) | ] // ] | | n2 [ s2 [ s'' [ T1' [ -> [ Hn2 [ HT1 [ HT1'bv [ Hs2bv [ Hs2fv [ HT1fv Hs' ] ] ] ] ] ] ] ] ] ] ].
    { apply /negbTE /negP => ?.
      have : z \in typ_bv (typ_subst s' (s1 x)).
      { apply /typ_bv_subst_intro_sub; eauto. }
      by rewrite -Hs ?Hclos ?HG. }
    { by rewrite env_subst_comp -(env_subst_ext s) => // ? /= /HG /Hs. }
    move: (typ_unify_complete (typ_subst s2 T2') (typ_arrow T1' (typ_fvar n2)) (fun x => if x < n2 then s'' x else T)) => [ | s3 [ Hunify [ s''' Hgen ] ] ] /=.
    { rewrite ltnn !(typ_subst_ext (fun x => if x < n2 then s'' x else T) s'') => [ | ? /HT1fv -> | ? /typ_fv_subst_elim [ ? /Hs2fv [ ] -> // /HTfv /((@leq_trans _ _ _)^~Hn2) -> ] ] //.
      rewrite typ_subst_comp (typ_subst_ext (typ_subst s'' \o s2) s') => [ | ? /HTfv /Hs' -> // ].
      congruence. }
    rewrite Hunify.
    have : forall x, typ_bv (s3 x) =i pred0 => [ ? x | Hs3bv ].
    { apply /negbTE /negP => /(typ_bv_unify _ _ _ Hunify) [ /typ_bv_subst_elim [ | [ ? ] ] | /= ].
      - by rewrite HT2'bv.
      - by rewrite Hs2bv.
      - rewrite !inE orbF.
        exact /negP /negbT /HT1'bv. }
    exists n2.+1, (typ_subst (typ_subst s3 \o s2) \o s1), s''', (s3 n2).
    (repeat split) => [ | | // | x ? | ? ? /typ_fv_subst_elim [ ? /typ_fv_subst_elim [ ? /(typ_fv_unify _ _ _ Hunify) [ -> /Hs2fv [ -> /Hs1fv [ | /((@leq_trans _ _ _)^~Hn2) ] | ] | [ /typ_fv_subst_elim [ ? /Hs2fv [ -> /HTfv /((@leq_trans _ _ _)^~Hn2) | ] ] | /= ] ] ] ] | ? /(typ_fv_unify _ _ _ Hunify) [ -> | [ /typ_fv_subst_elim [ ? /Hs2fv [ -> /HTfv /((@leq_trans _ _ _)^~Hn2) | ] ] | /= ] ] | ? ? /= ]; eauto.
    + apply /leqW /leq_trans; eauto.
    + by rewrite -(Hgen (typ_fvar n2)) /= ltnn.
    + rewrite typ_bv_subst Hs1bv.
      apply /negbTE /negP => /hasP [ ? ? ].
      rewrite /= typ_bv_subst Hs2bv => /hasP [ ? ? ].
      by rewrite Hs3bv.
    + rewrite !inE => /orP [ /HT1fv | /eqP -> ]; eauto.
    + rewrite !inE => /orP [ /HT1fv | /eqP -> ]; eauto.
    + rewrite Hs // (typ_subst_ext s' (typ_subst s'' \o s2)) => [ | ? /Hs1fv /= [ -> | /Hs' -> // ] ].
      * rewrite -!typ_subst_comp -Hgen.
        apply /typ_subst_ext => ? /typ_fv_subst_elim [ ? /Hs2fv [ <- /Hs1fv [ -> | /((@leq_trans _ _ _)^~Hn2) -> ] | -> ] // ].
        by rewrite ((@leq_trans _ _ _)^~Hn2) // ((@leq_trans _ _ _)^~Hn1).
      * exact /Hs' /((@leq_trans _ _ _)^~Hn1).
  - move: (IHt n G s T0) => [ ] // ? [ ? [ ? [ ? [ -> [ ? [ HT0 [ ? [ ? [ ? [ ? ? ] ] ] ] ] ] ] ] ] ].
    (repeat eexists) => /=; eauto.
    by rewrite HT0.
  - move: (IHt n G s (typ_ref T)) => [ ] // n1' [ s1 [ s' [ T' [ -> [ Hn1 [ HT [ HT'bv [ Hs1bv [ Hs1fv [ HTfv Hs ] ] ] ] ] ] ] ] ] ].
    move: (typ_unify_complete T' (typ_ref (typ_fvar n1')) (fun x => if x < n1' then s' x else T)) => [ /= | s2 [ Hunify [ s'' Hgen ] ] ].
    { by rewrite ltnn -(typ_subst_ext s') => // ? /HTfv ->. }
    rewrite Hunify.
    have : forall x, typ_bv (s2 x) =i pred0 => [ ? x | Hs2bv ].
    { apply /negbTE /negP => /(typ_bv_unify _ _ _ Hunify) => /= /orP.
      by rewrite HT'bv. }
    exists (n1'.+1), (typ_subst s2 \o s1), s'', (s2 n1').
    (repeat split) => [ | | | ? ? | ? ? /typ_fv_subst_elim [ ? /(typ_fv_unify _ _ _ Hunify) /= [ -> /Hs1fv [ -> | ] | [ /HTfv | /eqP -> ] ] ] | ? /(typ_fv_unify _ _ _ Hunify) [ -> | [ /HTfv | /eqP -> ] ] | ? Hlt ]; eauto.
    + by rewrite -(Hgen (typ_fvar n1')) /= ltnn.
    + rewrite typ_bv_subst Hs1bv.
      apply /negbTE /negP => /hasP [ ? ? ].
      by rewrite Hs2bv.
    + rewrite Hs // -Hgen.
      apply /typ_subst_ext => ? /Hs1fv [ ] -> //.
      by rewrite (leq_trans Hlt).
  - move: (IHt1 n G s (typ_ref T0)) => [ ] // n1 [ s1 [ s' [ T0' [ -> [ Hn1 [ HT0 [ HT0'bv [ Hs1bv [ Hs1fv [ HT0'fv Hs ] ] ] ] ] ] ] ] ] ].
    move: (IHt2 n1 (env_subst s1 G) s' T0) => [ | | | ] => [ ? /env_fv_subst_elim [ x ? ? ] z | ? /env_fv_subst_elim [ ? /Hs1fv [ -> /HG /((@leq_trans _ _ _)^~Hn1) | ] // ] | | n2 [ s2 [ s'' [ T1' [ -> [ Hn2 [ HT1 [ HT1'bv [ Hs2bv [ Hs2fv [ HT1fv Hs' ] ] ] ] ] ] ] ] ] ] ].
    { apply /negbTE /negP => ?.
      have : z \in typ_bv (typ_subst s' (s1 x)).
      { apply /typ_bv_subst_intro_sub; eauto. }
      by rewrite -Hs ?Hclos ?HG. }
    { by rewrite env_subst_comp -(env_subst_ext s) => // ? /= /HG /Hs. }
    move: (typ_unify_complete (typ_subst s2 T0') (typ_ref T1') s'') => [ /= | s3 [ Hunify [ s''' Hgen ] ] ].
    { by rewrite -HT1 typ_subst_comp -(typ_subst_ext s') -?HT0 => // ? /HT0'fv /Hs'. }
    rewrite Hunify.
    exists n2, (typ_subst (typ_subst s3 \o s2) \o s1), s''', typ_unit.
    (repeat split) => [ | ? ? | ? ? /typ_fv_subst_elim [ ? /typ_fv_subst_elim [ ? /(typ_fv_unify _ _ _ Hunify) [ -> /Hs2fv [ -> /Hs1fv [ -> | /((@leq_trans _ _ _)^~Hn2) ] | ] | /= [ /typ_fv_subst_elim [ ? /Hs2fv [ -> /HT0'fv /((@leq_trans _ _ _)^~Hn2) | ] ] | /HT1fv ] ] ] ] | | ? ? ]; eauto.
    + apply /leq_trans; eauto.
    + rewrite typ_bv_subst Hs1bv.
      apply /negbTE /negP => /hasP [ ? ? ].
      rewrite typ_bv_subst Hs2bv => /hasP [ ? ? /(typ_bv_unify _ _ _ Hunify) /= /orP ].
      rewrite HT1'bv orbF typ_bv_subst HT0'bv => /hasP [ ? ? ].
      by rewrite Hs2bv.
    + rewrite Hs // (typ_subst_ext s' (typ_subst s'' \o s2)) => [ /= | ? /Hs1fv /= [ -> | /Hs' -> // ] ].
      * by rewrite -!typ_subst_comp Hgen.
      * apply /Hs' /leq_trans; eauto.
  - rewrite H2.
    move: (IHt1 n G s (typ_open (typ_fvar \o addn (maximum (env_enum_fv (env_subst s G) (typ_enum_fv T1 L))).+1) T1)) => [ | | | n1' [ s1 [ s' [ T1' [ -> [ Hn1 [ HT [ HT1'bv [ Hs1bv [ Hs1fv [ HTfv Hs ] ] ] ] ] ] ] ] ] ] ] //.
    { apply /H4 => x. repeat eexists.
      apply /negP => HinL.
      have : (maximum (env_enum_fv (env_subst s G) (typ_enum_fv T1 L))).+1 + x \in env_enum_fv (env_subst s G) (typ_enum_fv T1 L) => [ | /maximum_sup ].
      { by rewrite env_enum_fv_inE_aux typ_enum_fv_inE_aux HinL !orbT. }
      by rewrite addSn ltnNge leq_addr. }
    move: (IHt2 n1' (typ_subst (fun x => if x \in env_fv (env_subst s1 G) then typ_fvar x else typ_bvar x) T1' :: env_subst s1 G) s' T) =>
      /= [ ? /orP [ /typ_fv_subst_elim [ x ] | /env_fv_subst_elim [ x ? ? ] z ] | ? /orP [ /typ_fv_subst_elim [ y ] | /env_fv_subst_elim [ ? /Hs1fv [ -> /HG /((@leq_trans _ _ _)^~Hn1) | ] ] ] // | | n2' [ s2 [ s'' [ T2' [ -> [ Hn2 [ HT2' [ HT2'bv [ Hs2bv [ Hs2fv [ HT2fv Hs' ] ] ] ] ] ] ] ] ] ] ] //.
    { destruct (x \in env_fv (env_subst s1 G)) eqn:Hfv => //=; rewrite inE => /eqP <- ? z.
      apply /negbTE /negP => ?.
      have : z \in typ_bv (typ_subst s' T1').
      { apply /typ_bv_subst_intro_sub; eauto. }
      by rewrite -HT => /typ_bv_open_elim [ ? ]. }
    { apply /negbTE /negP => ?.
      have : z \in typ_bv (typ_subst s' (s1 x)).
      { apply/ typ_bv_subst_intro_sub; eauto. }
      by rewrite -Hs ?Hclos ?HG. }
    { move: (y \in env_fv (env_subst s1 G)) => [ /= | // ].
      by rewrite inE => /eqP -> /HTfv. }
    { apply /(typed_weaken_env _ _ _ _ H6) => [ [ ? /(_ (typ_fvar 0)) <- | i ? Hnth ] /= ].
      - move: (f_equal (typ_subst (fun x => if x <= maximum (env_enum_fv (env_subst s G) (typ_enum_fv T1 L)) then typ_fvar x else typ_bvar (x - (maximum (env_enum_fv (env_subst s G) (typ_enum_fv T1 L))).+1))) HT).
        rewrite typ_subst_open_distr => [ | x Hin ? ].
        + rewrite typ_subst_fvar_eq => [ | x Hin ].
          { rewrite typ_open_bvar_eq => [ -> | ? ? /= ].
            - eexists (typ_subst (fun x => if x <= maximum (env_enum_fv (env_subst s G) (typ_enum_fv T1 L)) then typ_fvar x else typ_bvar (x - (maximum (env_enum_fv (env_subst s G) (typ_enum_fv T1 L))).+1)) \o s', _); eauto.
              rewrite !typ_subst_comp typ_open_subst_distr => [ | ? ].
              + rewrite typ_open_bvar_eq => [ | ? ].
                { apply /typ_subst_ext => x ? /=.
                  rewrite fun_if /= fun_if /=.
                  destruct (x \in env_fv (env_subst s1 G)) eqn:Henv => //.
                  rewrite typ_open_bvar_eq => [ | y ? ].
                  - rewrite typ_subst_fvar_eq => [ // | y Hin ].
                    rewrite maximum_sup // env_enum_fv_inE_aux typ_enum_fv_inE_aux -(env_subst_ext (typ_subst s' \o s1)) => [ | ? /HG /Hs // ].
                    by rewrite -env_subst_comp (env_fv_subst_intro _ _ x) // orbT.
                  - have : y \in typ_bv (typ_subst s' T1').
                    { apply /typ_bv_subst_intro_sub; eauto. }
                    by rewrite -HT => /typ_bv_open_elim [ ? ]. }
                by rewrite HT1'bv.
              + by rewrite HT1'bv.
            - by rewrite addSn ltnNge leq_addr /= subSS addKn. }
          by rewrite maximum_sup // env_enum_fv_inE_aux typ_enum_fv_inE_aux Hin orbT.
        + by rewrite maximum_sup // env_enum_fv_inE_aux typ_enum_fv_inE_aux Hin orbT.
      - rewrite env_subst_comp (env_subst_ext (typ_subst s' \o s1) s) => [ | ? /HG /Hs // ].
        eexists (_, _).
        + exact /Hnth.
        + exact /Logic.eq_sym /typ_open_bvar. }
    exists n2', (typ_subst s2 \o s1), s'', T2'.
    (repeat split) => //= [ | ? ? | ? ? /typ_fv_subst_elim [ ? /Hs2fv [ -> /Hs1fv [ | /((@leq_trans _ _ _)^~Hn2) ] | ] ] | ? ? ]; eauto.
    + exact /(leq_trans Hn1).
    + rewrite typ_bv_subst Hs1bv.
      apply /negbTE /negP => /hasP [ ? ].
      by rewrite Hs2bv.
    + rewrite Hs // (typ_subst_ext s' (typ_subst s'' \o s2)) ?typ_subst_comp => /= [ // | ? /Hs1fv [ -> | ] ];
      apply /Hs'; exact /((@leq_trans _ _ _)^~Hn1).
Qed.
