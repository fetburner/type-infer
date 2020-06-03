From mathcomp Require Import all_ssreflect.
Require Import Types Term.

Definition env := list typ.

Definition env_fv := foldr (predU \o typ_fv) pred0.
Definition env_bv := foldr (predU \o typ_bv) pred0.

Lemma env_fv_intro T x :
  x \in typ_fv T ->
  forall G, T \in G -> x \in env_fv G.
Proof.
  rewrite -topredE => /= H.
  elim => //= ? ? IH.
  rewrite inE => /orP [ /eqP <- | /IH ].
  - by rewrite inE H.
  - rewrite -!topredE => /= ->. by rewrite orbT.
Qed.

Lemma env_bv_intro T x :
  x \in typ_bv T ->
  forall G, T \in G -> x \in env_bv G.
Proof.
  rewrite -topredE => /= H.
  elim => //= ? ? IH.
  rewrite inE => /orP [ /eqP <- | /IH ].
  - by rewrite inE H.
  - rewrite -!topredE => /= ->. by rewrite orbT.
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

Lemma env_fv_subst s x : forall G,
  x \in env_fv (env_subst s G) ->
  exists y, x \in typ_fv (s y) /\ y \in env_fv G.
Proof.
  elim => //= ? ? IH.
  rewrite inE => /orP [ /typ_fv_subst | /IH ] [ y [ ? ] ];
  rewrite -topredE => /= Hin; exists y; rewrite inE Hin ?orbT; eauto.
Qed.

Lemma env_fv_subst_intro s x y : forall G,
  y \in env_fv G ->
  x \in typ_fv (s y) ->
  x \in env_fv (env_subst s G).
Proof.
  elim => //= ? ? IH.
  rewrite !inE => /orP [ ] Hin => [ /(typ_fv_subst_intro _ _ _ _ Hin) | /(IH Hin) ];
  rewrite -topredE => /= -> //.
  by rewrite orbT.
Qed.

Lemma env_bv_open s x : forall G,
  x \in env_bv (env_open s G) ->
  exists y, x \in typ_bv (s y) /\ y \in env_bv G.
Proof.
  elim => //= ? ? IH.
  rewrite inE => /orP [ /typ_bv_open | /IH ] [ y [ ? ] ];
  rewrite -topredE => /= Hin; exists y; rewrite inE Hin ?orbT; eauto.
Qed.

Definition env_enum_fv := foldr (fun T => typ_enum_fv^~T).

Lemma env_enum_fv_inE x : forall G acc,
  (x \in env_enum_fv acc G) = (x \in env_fv G) || (x \in acc).
Proof.
  elim => //= ? ? IH ?.
  by rewrite typ_enum_fv_inE IH inE orbA.
Qed.

Inductive typed : env -> trm -> typ -> Prop :=
  | typed_var G x s T :
      (forall d, nth d G x = T) ->
      (forall x, typ_bv (s x) =i pred0) ->
      typed G (trm_var x) (typ_open s T)
  | typed_abs G t T1 T2 :
      typ_bv T1 =i pred0 ->
      typed (T1 :: G) t T2 ->
      typed G (trm_abs t) (typ_arrow T1 T2)
  | typed_app G t1 t2 T1 T2 :
      typed G t1 (typ_arrow T1 T2) ->
      typed G t2 T1 ->
      typed G (trm_app t1 t2) T2
  | typed_let (L : seq nat) G t1 t2 T1 T2 :
      (forall s, (forall x, exists y, s x = typ_fvar y /\ y \notin L) -> typed G t1 (typ_open s T1)) ->
      typed (T1 :: G) t2 T2 ->
      typed G (trm_let t1 t2) T2.
Hint Constructors typed.

Lemma typed_closed G t T :
  typed G t T ->
  typ_bv T =i pred0.
Proof.
  induction 1 => //= n; rewrite !inE; apply /negbTE.
  - apply /negP => /typ_bv_open [ ? [ ] ].
    by rewrite H0 inE.
  - move: (H n) (IHtyped n).
    by rewrite -!topredE => /= -> ->.
  - move: (IHtyped1 n).
    rewrite -!topredE => /= /negbT.
    by rewrite negb_or => /andP [ ].
Qed.

Lemma typed_weaken G t T :
  typed G t T ->
  forall G',
  (forall x T, (forall d, nth d G x = T) -> exists s T', (forall d, nth d G' x = T') /\ T = typ_open s T') ->
  typed G' t T.
Proof.
  induction 1 => /= G' HG'; eauto.
  - case (HG' _ _ H) => ? [ ? [ ? -> ] ].
    rewrite typ_open_comp.
    apply /typed_var => // ? n.
    apply /negbTE /negP => /typ_bv_open [ ? [ ] ].
    by rewrite H0 inE.
  - apply /typed_abs => //.
    apply /IHtyped => [ [ ? | ] /= ]; eauto.
    repeat (eexists; eauto). exact /Logic.eq_sym /typ_open_bvar.
  - apply /typed_let; eauto.
    apply /IHtyped => [ [ ? | ] /= ]; eauto.
    repeat (eexists; eauto). exact /Logic.eq_sym /typ_open_bvar.
Qed.

Lemma typed_subst_typ G t T :
  typed G t T ->
  forall s,
  (forall x, typ_bv (s x) =i pred0) ->
  typed (env_subst s G) t (typ_subst s T).
Proof.
  induction 1 => s0 Hclosed /=; eauto.
  - rewrite typ_subst_open_distr => [ | ? ? ? ].
    + apply /typed_var => [ ? | ? ? ].
      * case (leqP (size G) x) => ?.
         { move: (H (typ_fvar 0)).
           by rewrite -(H (typ_bvar 0)) !nth_default // size_map. }
        by rewrite /env_subst (nth_map (typ_fvar 0)) // H.
      * { apply /negbTE /negP => /typ_bv_subst [ | [ ? [ ] ] ].
          - by rewrite H0.
          - by rewrite Hclosed. }
    + by rewrite Hclosed.
  - apply /typed_abs => [ ? | ].
    + apply /negbTE /negP => /typ_bv_subst [ | [ ? [ ] ] ].
      * by rewrite H.
      * by rewrite Hclosed.
    + exact /IHtyped.
  - apply /(typed_let (env_enum_fv (typ_enum_fv L T1) G)) => [ s' Hs' | ]; [ | exact /IHtyped ].
    rewrite -(typ_subst_ext (fun x => if (x \notin env_fv G) && (x \notin typ_fv T1) then typ_fvar x else s0 x)) => [ | ? -> /= ].
    + rewrite typ_open_subst_distr => [ | x ? ? ].
      { rewrite -(typ_subst_ext (fun x => if (x \notin env_fv G) && (x \notin typ_fv T1) then typ_fvar x else s0 x)) => [ | /= ? /typ_fv_open [ -> /= | [ x [ ] ] ] ].
        - rewrite -(env_subst_ext (fun x => if (x \notin env_fv G) && (x \notin typ_fv T1) then typ_fvar x else s0 x)) => [ | ? -> // ].
          apply H0 => x.
          + case (Hs' x) => ? [ -> ].
            rewrite env_enum_fv_inE typ_enum_fv_inE !negb_or => /andP [ ? /andP [ ] ]. eauto.
          + by case ((x \notin env_fv G) && (x \notin typ_fv T1)).
        - rewrite andbF typ_open_bvar_eq => // ?.
          by rewrite Hclosed.
        - case (Hs' x) => ? [ -> /= ].
          rewrite env_enum_fv_inE typ_enum_fv_inE !negb_or inE => /andP [ HG /andP [ HT1 ? ] ] /eqP ?.
          subst. by rewrite HG HT1. }
      case (Hs' x) => ? [ -> /= ].
      rewrite env_enum_fv_inE typ_enum_fv_inE !negb_or inE => /andP [ HG /andP [ HT1 ? ] ] /eqP ?.
      subst. by rewrite HG HT1.
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

Fixpoint typing n G t :=
  match t with
  | trm_var x =>
      match nth None (map Some G) x with
      | None => None
      | Some T => Some ((n + maximum (typ_enum_bv [::] T)).+1, typ_fvar, typ_open (typ_fvar \o addn n) T)
      end
  | trm_abs t =>
      match typing n.+1 (typ_fvar n :: G) t with
      | None => None
      | Some (m, s, T2) => Some (m, s, typ_arrow (s n) T2)
      end
  | trm_app t1 t2 =>
      match typing n G t1 with
      | None => None
      | Some (n1, s1, T1) =>
          match typing n1 (env_subst s1 G) t2 with
          | None => None
          | Some (n2, s2, T2) =>
              option_map
                (fun s3 => (n2.+1, typ_subst (typ_subst s3 \o s2) \o s1, s3 n2))
                (typ_unify (typ_subst s2 T1) (typ_arrow T2 (typ_fvar n2)))
          end
      end
  | trm_let t1 t2 =>
      match typing n G t1 with
      | None => None
      | Some (n1, s1, T1) =>
          match typing n1 (typ_subst (fun x => if x \in env_fv (env_subst s1 G) then typ_fvar x else typ_bvar x) T1 :: env_subst s1 G) t2 with
          | None => None
          | Some (n2, s2, T2) => Some (n2, typ_subst s2 \o s1, T2)
          end
      end
  end.

(* let f = fun x -> x in f f *)
Eval compute in (typing 0 [::] (trm_let (trm_abs (trm_var 0)) (trm_app (trm_var 0) (trm_var 0)))).
(* (fun f -> f f) (fun x -> x) *)
Eval compute in (typing 0 [::] (trm_app (trm_abs (trm_app (trm_var 0) (trm_var 0))) (trm_abs (trm_var 0)))).

Theorem typing_sound : forall t n m G s T,
  typing n G t = Some (m, s, T) ->
  typed (env_subst s G) t T /\ forall x, typ_bv (s x) =i pred0.
Proof.
  elim => /=
    [ x ? ? G ? ?
    | t IHt n ? G ? ?
    | t1 IHt1 t2 IHt2 n ? G ? ?
    | t1 IHt1 t2 IHt2 n ? G ? ? ].
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
    have Htyped1' : typed (env_subst s2 (env_subst s1 G)) t1 (typ_subst s2 T1); eauto.
    have : forall x : nat, typ_bv (s3 x) =i pred0 => [ ? x | Hs3bv ].
    { apply /negbTE /negP => /(typ_bv_unify _ _ _ Hunify) [ | /= ].
      - by rewrite (typed_closed _ _ _ Htyped1').
      - move: (typed_closed _ _ _ Htyped2 x).
        by rewrite -!topredE => /= ->. }
    split => [ | ? ? ].
    + rewrite -!env_subst_comp.
      apply /(typed_app _ _ _ (typ_subst s3 T2)).
      * move: (typ_unify_sound _ _ _ Hunify) => /= <-.
        apply /typed_subst_typ; eauto.
      * apply /typed_subst_typ; eauto.
    + apply /negbTE /negP => /typ_bv_subst [ | [ ? [ /typ_bv_subst [ | [ ? [ ] ] ] ] ] ].
      + by rewrite Hs1bv.
      + by rewrite Hs2bv.
      + by rewrite Hs3bv.
  - destruct (typing n G t1) as [ [ [ n1 s1 ] T1 ] | ] eqn:Htyping1 => //.
    destruct (typing n1 (typ_subst (fun x => if x \in env_fv (env_subst s1 G) then typ_fvar x else typ_bvar x) T1 :: env_subst s1 G) t2) as [ [ [ n2 s2 ] T2 ] | ] eqn:Htyping2; inversion 1. subst.
    case (IHt1 _ _ _ _ _ Htyping1) => Htyped1 Hclosed1.
    case (IHt2 _ _ _ _ _ Htyping2) => ? Hclosed2.
    split => [ | ? ? ].
    + rewrite -env_subst_comp.
      apply /(typed_let (env_enum_fv [::] (env_subst s1 G))) => [ s Hs | ]; eauto.
      rewrite typ_subst_comp typ_open_subst_distr => [ | ? ].
      { rewrite typ_open_bvar_eq => [ | ? ].
        - rewrite (env_subst_ext s2 (typ_open s \o (typ_subst s2 \o (fun x => if x \in env_fv (env_subst s1 G) then typ_fvar x else typ_bvar x)))) => [ | ? /= -> /= ].
          + apply /typed_subst_typ => //= x ?.
            apply /negbTE /negP => /typ_bv_open [ y [ ] ].
            case (Hs y) => ? [ -> // ].
          + rewrite typ_open_bvar_eq => // ?.
            by rewrite Hclosed2.
        - by rewrite (typed_closed _ _ _ Htyped1). }
      by rewrite (typed_closed _ _ _ Htyped1).
    + apply /negbTE /negP => /typ_bv_subst [ | [ ? [ ] ] ].
      * by rewrite Hclosed1.
      * by rewrite Hclosed2.
Qed.

Theorem typing_complete : forall t n G s T,
  {in env_fv G, forall x, typ_bv (s x) =i pred0} ->
  (forall x, x \in env_fv G -> x < n) ->
  typed (env_subst s G) t T ->
  exists m s' s'' T', typing n G t = Some (m, s', T')
    /\ n <= m
    /\ T = typ_subst s'' T'
    /\ typ_bv T' =i pred0
    /\ (forall x, typ_bv (s' x) =i pred0)
    /\ (forall x y, x \in typ_fv (s' y) -> x = y \/ x < m)
    /\ (forall x, x \in typ_fv T' -> x < m)
    /\ (forall x, x < n -> s x = typ_subst s'' (s' x)).
Proof.
  elim => /= [ x | t IHt | t1 IHt1 t2 IHt2 | t1 IHt1 t2 IHt2 ] n G s T Hclos HG; inversion 1; subst.
  - case (leqP (size G) x) => ?.
    { move: (H1 (typ_fvar 0)).
      by rewrite -(H1 (typ_bvar 0)) !nth_default // size_map. }
    exists ((n + maximum (typ_enum_bv [::] (nth (typ_fvar 0) G x))).+1), typ_fvar, (fun x => if x < n then s x else s0 (x - n)), (typ_open (typ_fvar \o addn n) (nth (typ_fvar 0) G x)).
    (repeat split) => [ | | | ? | ? ? /= | ? /typ_fv_open [ ? | [ ? [ /= ] ] ] | ? /= -> // ].
    + by rewrite (nth_map (typ_fvar 0)).
    + apply /leqW /leq_addr.
    + rewrite -(H1 (typ_fvar 0)) /env_subst (nth_map (typ_fvar 0)) // typ_subst_open_distr => [ | /= x0 ? ? ].
      { rewrite (typ_subst_ext (fun x => if x < n then s x else s0 (x - n)) s) => [ | ? ? ].
        - apply /typ_open_ext => ? ? /=.
          by rewrite ltnNge leq_addr /= addKn.
        - by rewrite HG // (env_fv_intro (nth (typ_fvar 0) G x)) // mem_nth. }
      by rewrite HG ?Hclos // (env_fv_intro (nth (typ_fvar 0) G x)) // mem_nth.
    + apply /negbTE /negP => /typ_bv_open [ ? [ //= ] ].
    + rewrite inE => /eqP. eauto.
    + apply /leqW /ltn_addr /HG /(env_fv_intro (nth (typ_fvar 0) G x)) => //.
      exact /mem_nth.
    + rewrite inE => /eqP -> ?.
      by rewrite ltnS leq_add2l maximum_sup // typ_enum_bv_inE in_nil orbF.
  - move: (IHt n.+1 (typ_fvar n :: G) (fun x => if x < n then s x else T1) T2) => /= [ x | ? | | n1 [ s1 [ s' [ T' [ -> [ Hn1 [ -> [ HT'bv [ Hs1bv [ Hs1fv [ HT'fv Hs1 ] ] ] ] ] ] ] ] ] ] ].
    { rewrite !inE => /orP [ /eqP -> | Hin ].
      - by rewrite ltnn.
      - rewrite HG //. exact /Hclos /Hin. }
    { rewrite !inE => /orP [ /eqP -> | /HG /leqW // ].
      exact /leqnn. }
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
    move: (IHt2 n1 (env_subst s1 G) s' T1) => [ ? /env_fv_subst [ x [ ? ? ] ] z | ? /env_fv_subst [ ? [ /Hs1fv [ -> /HG /((@leq_trans _ _ _)^~Hn1) | ] // ] ] | | n2 [ s2 [ s'' [ T1' [ -> [ Hn2 [ HT1 [ HT1'bv [ Hs2bv [ Hs2fv [ HT1fv Hs' ] ] ] ] ] ] ] ] ] ] ].
    { apply /negbTE /negP => ?.
      have : z \in typ_bv (typ_subst s' (s1 x)).
      { apply /typ_bv_subst_intro_sub; eauto. }
      by rewrite -Hs ?Hclos ?HG. }
    { by rewrite env_subst_comp -(env_subst_ext s) => // ? /= /HG /Hs. }
    move: (typ_unify_complete (typ_subst s2 T2') (typ_arrow T1' (typ_fvar n2)) (fun x => if x < n2 then s'' x else T)) => [ | s3 [ Hunify [ s''' Hgen ] ] ] /=.
    { rewrite ltnn !(typ_subst_ext (fun x => if x < n2 then s'' x else T) s'') => [ | ? /HT1fv -> | ? /typ_fv_subst [ ? [ /Hs2fv [ ] -> // /HTfv /((@leq_trans _ _ _)^~Hn2) -> ] ] ] //.
      rewrite typ_subst_comp (typ_subst_ext (typ_subst s'' \o s2) s') => [ | ? /HTfv /Hs' -> // ].
      congruence. }
    rewrite Hunify.
    have : forall x, typ_bv (s3 x) =i pred0 => [ ? x | Hs3bv ].
    { apply /negbTE /negP => /(typ_bv_unify _ _ _ Hunify) [ /typ_bv_subst [ | [ ? [ ] ] ] | /= ].
      - by rewrite HT2'bv.
      - by rewrite Hs2bv.
      - rewrite !inE orbF.
        exact /negP /negbT /HT1'bv. }
    exists n2.+1, (typ_subst (typ_subst s3 \o s2) \o s1), s''', (s3 n2).
    (repeat split) => [ | | // | x ? | ? ? /typ_fv_subst [ ? [ /typ_fv_subst [ ? [ /(typ_fv_unify _ _ _ Hunify) [ -> /Hs2fv [ -> /Hs1fv [ | /((@leq_trans _ _ _)^~Hn2) ] | ] | [ /typ_fv_subst [ ? [ /Hs2fv [ -> /HTfv /((@leq_trans _ _ _)^~Hn2) | ] ] ] | /= ] ] ] ] ] ] | ? /(typ_fv_unify _ _ _ Hunify) [ -> | [ /typ_fv_subst [ ? [ /Hs2fv [ -> /HTfv /((@leq_trans _ _ _)^~Hn2) | ] ] ] | /= ] ] | ? ? /= ]; eauto.
    + apply /leqW /leq_trans; eauto.
    + by rewrite -(Hgen (typ_fvar n2)) /= ltnn.
    + apply /negbTE /negP => /typ_bv_subst [ | [ ? [ /typ_bv_subst [ | [ ? [ ] ] ] ] ] ].
      * by rewrite Hs1bv.
      * by rewrite Hs2bv.
      * by rewrite Hs3bv.
    + rewrite !inE => /orP [ /HT1fv | /eqP -> ]; eauto.
    + rewrite !inE => /orP [ /HT1fv | /eqP -> ]; eauto.
    + rewrite Hs // (typ_subst_ext s' (typ_subst s'' \o s2)) => [ | ? /Hs1fv /= [ -> | /Hs' -> // ] ].
      * rewrite -!typ_subst_comp -Hgen.
        apply /typ_subst_ext => ? /typ_fv_subst [ ? [ /Hs2fv [ <- /Hs1fv [ -> | /((@leq_trans _ _ _)^~Hn2) -> ] | -> ] // ] ].
        by rewrite ((@leq_trans _ _ _)^~Hn2) // ((@leq_trans _ _ _)^~Hn1).
      * exact /Hs' /((@leq_trans _ _ _)^~Hn1).
  - move: (IHt1 n G s (typ_open (typ_fvar \o addn (maximum (env_enum_fv (typ_enum_fv L T1) (env_subst s G))).+1) T1)) => [ | | | n1' [ s1 [ s' [ T1' [ -> [ Hn1 [ HT [ HT1'bv [ Hs1bv [ Hs1fv [ HTfv Hs ] ] ] ] ] ] ] ] ] ] ] //.
    { apply /H3 => x. repeat eexists.
      apply /negP => HinL.
      have : (maximum (env_enum_fv (typ_enum_fv L T1) (env_subst s G))).+1 + x \in env_enum_fv (typ_enum_fv L T1) (env_subst s G) => [ | /maximum_sup ].
      { by rewrite env_enum_fv_inE typ_enum_fv_inE HinL !orbT. }
      by rewrite addSn ltnNge leq_addr. }
    move: (IHt2 n1' (typ_subst (fun x => if x \in env_fv (env_subst s1 G) then typ_fvar x else typ_bvar x) T1' :: env_subst s1 G) s' T) =>
      /= [ ? | ? | | n2' [ s2 [ s'' [ T2' [ -> [ Hn2 [ HT2' [ HT2'bv [ Hs2bv [ Hs2fv [ HT2fv Hs' ] ] ] ] ] ] ] ] ] ] ] //.
    { rewrite inE => /orP [ /typ_fv_subst [ x [ ] ] | /env_fv_subst [ x [ ? ? ] ] z ].
      - destruct (x \in env_fv (env_subst s1 G)) eqn:Hfv => //=; rewrite inE => /eqP <- ? z.
        apply /negbTE /negP => ?.
        have : z \in typ_bv (typ_subst s' T1').
        { apply /typ_bv_subst_intro_sub; eauto. }
        by rewrite -HT => /typ_bv_open [ ? [ ] ].
      - apply /negbTE /negP => ?.
        have : z \in typ_bv (typ_subst s' (s1 x)).
        { apply/ typ_bv_subst_intro_sub; eauto. }
        by rewrite -Hs ?Hclos ?HG. }
    { rewrite inE => /orP [ /typ_fv_subst [ y [ ] ] | /env_fv_subst [ ? [ /Hs1fv [ -> /HG /((@leq_trans _ _ _)^~Hn1) | ] ] ] ] //.
      move: (y \in env_fv (env_subst s1 G)) => [ /= | // ].
      by rewrite inE => /eqP -> /HTfv. }
    { apply /(typed_weaken _ _ _ H5) => [ [ ? /(_ (typ_fvar 0)) <- | i ? Hnth ] /= ].
      - move: (f_equal (typ_subst (fun x => if x <= maximum (env_enum_fv (typ_enum_fv L T1) (env_subst s G)) then typ_fvar x else typ_bvar (x - (maximum (env_enum_fv (typ_enum_fv L T1) (env_subst s G))).+1))) HT).
        rewrite typ_subst_open_distr => [ | x Hin ? ].
        + rewrite typ_subst_fvar_eq => [ | x Hin ].
          { rewrite typ_open_bvar_eq => [ -> | ? ? /= ].
            - exists (typ_subst (fun x => if x <= maximum (env_enum_fv (typ_enum_fv L T1) (env_subst s G)) then typ_fvar x else typ_bvar (x - (maximum (env_enum_fv (typ_enum_fv L T1) (env_subst s G))).+1)) \o s').
              repeat eexists.
              rewrite !typ_subst_comp typ_open_subst_distr => [ | ? ].
              + rewrite typ_open_bvar_eq => [ | ? ].
                { apply /typ_subst_ext => x ? /=.
                  rewrite fun_if /= fun_if /=.
                  destruct (x \in env_fv (env_subst s1 G)) eqn:Henv => //.
                  rewrite typ_open_bvar_eq => [ | y ? ].
                  - rewrite typ_subst_fvar_eq => [ // | y Hin ].
                    rewrite maximum_sup // env_enum_fv_inE typ_enum_fv_inE -(env_subst_ext (typ_subst s' \o s1)) => [ | ? /HG /Hs // ].
                    by rewrite -env_subst_comp (env_fv_subst_intro _ _ x) // orbT.
                  - have : y \in typ_bv (typ_subst s' T1').
                    { apply /typ_bv_subst_intro_sub; eauto. }
                    by rewrite -HT => /typ_bv_open [ ? [ ] ]. }
                by rewrite HT1'bv.
              + by rewrite HT1'bv.
            - by rewrite addSn ltnNge leq_addr /= subSS addKn. }
          by rewrite maximum_sup // env_enum_fv_inE typ_enum_fv_inE Hin orbT.
        + by rewrite maximum_sup // env_enum_fv_inE typ_enum_fv_inE Hin orbT.
      - rewrite env_subst_comp (env_subst_ext (typ_subst s' \o s1) s) => [ | ? /HG /Hs // ].
        repeat eexists.
        + exact /Hnth.
        + exact /Logic.eq_sym /typ_open_bvar. }
    exists n2', (typ_subst s2 \o s1), s'', T2'.
    (repeat split) => //= [ | ? ? | ? ? /typ_fv_subst [ ? [ /Hs2fv [ -> /Hs1fv [ | /((@leq_trans _ _ _)^~Hn2) ] | ] ] ] | ? ? ]; eauto.
    + exact /(leq_trans Hn1).
    + apply /negbTE /negP => /typ_bv_subst [ | [ ? [ ] ] ].
      * by rewrite Hs1bv.
      * by rewrite Hs2bv.
    + rewrite Hs // (typ_subst_ext s' (typ_subst s'' \o s2)) ?typ_subst_comp => /= [ // | ? /Hs1fv [ -> | ] ];
      apply /Hs'; exact /((@leq_trans _ _ _)^~Hn1).
Qed.
