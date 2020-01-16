From mathcomp Require Import all_ssreflect.
Require Import Types Term.

Definition env := list typ.

Definition env_fv := foldr (cat \o typ_fv) [::].

Lemma env_fv_intro T x (_ : x \in typ_fv T) :
  forall G, T \in G -> x \in env_fv G.
Proof.
  elim => //= ? ? IH.
  rewrite in_cons mem_cat => /orP [ /eqP <- | /IH -> ].
  - by rewrite H.
  - by rewrite orbT.
Qed.

Definition env_subst s := map (typ_subst s).

Lemma env_subst_typ_fvar G : env_subst typ_fvar G = G.
Proof.
  rewrite /env_subst -(@eq_map _ _ id) ?map_id => // ?.
  by rewrite typ_subst_fvar.
Qed.

Lemma env_subst_ext s s' G
  (Hext : { in env_fv G, s =1 s' }) :
  env_subst s G = env_subst s' G.
Proof.
  apply /eq_in_map => ? ?.
  apply /typ_subst_ext => ? ?.
  apply /Hext /env_fv_intro; eauto.
Qed. 

Lemma env_subst_typ_comp s s' G :
  env_subst s (env_subst s' G) = env_subst (typ_subst s \o s') G.
Proof.
  rewrite /env_subst -map_comp.
  exact /eq_map /typ_subst_comp.
Qed.

Lemma env_fv_subst s x : forall G,
  x \in env_fv (env_subst s G) ->
  exists y, x \in typ_fv (s y) /\ y \in env_fv G.
Proof.
  elim => //= ? ? IH.
  rewrite mem_cat => /orP [ /typ_fv_subst | /IH ] [ y [ ? Hin ] ];
  exists y; rewrite mem_cat Hin ?orbT; eauto.
Qed.

Inductive typed : env -> trm -> typ -> Prop :=
  | typed_var G x T :
      (forall d, nth d G x = T) ->
      typed G (trm_var x) T
  | typed_abs G t T1 T2 :
      typed (T1 :: G) t T2 ->
      typed G (trm_abs t) (typ_arrow T1 T2)
  | typed_app G t1 t2 T1 T2 :
      typed G t1 (typ_arrow T1 T2) ->
      typed G t2 T1 ->
      typed G (trm_app t1 t2) T2
  | typed_let G t1 t2 T1 T2 :
      typed G t1 T1 ->
      typed (T1 :: G) t2 T2 ->
      typed G (trm_let t1 t2) T2.
Hint Constructors typed.

Lemma typed_subst_typ s G t T :
  typed G t T ->
  typed (env_subst s G) t (typ_subst s T).
Proof.
  induction 1 => /=; eauto.
  constructor => d.
  case (leqP (size G) x) => ?.
  - move: nth_default (H (typ_arrow T T))
      => -> // /(f_equal typ_size) /= /eq_leq.
    by rewrite ltnNge leq_addr.
  - by rewrite (nth_map d) // H.
Qed.
Hint Resolve typed_subst_typ.

Definition gensym := succn \o foldr maxn 0.

Lemma gensym_fresh L : gensym L \notin L.
Proof.
  have IH : forall x, x \in L -> x < gensym L.
  { elim L => //= ? ? IH ?.
    rewrite in_cons => /orP [ /eqP <- | /IH ];
    rewrite /gensym /= !ltnS leq_max ?leqnn // => ->.
    by rewrite orbT. }
  apply /negP => /IH.
  by rewrite ltnn.
Qed.

Fixpoint typing L G t :=
  match t with
  | trm_var x => nth None (map (Some \o pair (L, typ_fvar)) G) x
  | trm_abs t =>
      let x := gensym L in
      match typing (x :: L) (typ_fvar x :: G) t with
      | None => None
      | Some (L, s, T2) => Some (L, s, typ_arrow (s x) T2)
      end
  | trm_app t1 t2 =>
      match typing L G t1 with
      | None => None
      | Some (L1, s1, T1) =>
          match typing L1 (env_subst s1 G) t2 with
          | None => None
          | Some (L2, s2, T2) =>
              let x := gensym L2 in
              option_map
                (fun s3 => (x :: L2, typ_subst (typ_subst s3 \o s2) \o s1, s3 x))
                (unify (typ_subst s2 T1) (typ_arrow T2 (typ_fvar x)))
          end
      end
  | trm_let t1 t2 =>
      match typing L G t1 with
      | None => None
      | Some (L1, s1, T1) =>
          match typing L1 (T1 :: env_subst s1 G) t2 with
          | None => None
          | Some (L2, s2, T2) => Some (L2, typ_subst s2 \o s1, T2)
          end
      end
  end.

Theorem typing_sound : forall t L L' G s T,
  typing L G t = Some (L', s, T) ->
  typed (env_subst s G) t T.
Proof.
  elim => /= [ x ? ? G ? ? Hnth | t IHt L ? G ? ? | t1 IHt1 t2 IHt2 L ? G ? ? | t1 IHt1 t2 IHt2 L ? G ? ? ].
  - apply /typed_var => d.
    move: (leqP (size G) x) Hnth => [ ? | /(nth_map d _) -> ].
    + by rewrite nth_default // size_map.
    + inversion 1. by rewrite env_subst_typ_fvar.
  - destruct (typing (gensym L :: L) (typ_fvar (gensym L) :: G) t) as [ [ [ ? ? ] ] | ] eqn:Htyping; inversion 1. subst.
    exact /typed_abs /(IHt _ _ _ _ _ Htyping).
  - destruct (typing L G t1) as [ [ [ L1 s1 ] T1 ] | ] eqn:Htyping1 => //.
    destruct (typing L1 (env_subst s1 G) t2) as [ [ [ L2 s2 ] T2 ] | ] eqn:Htyping2 => //.
    destruct (unify (typ_subst s2 T1) (typ_arrow T2 (typ_fvar (gensym L2)))) as [ s3 | ] eqn:Hunify; inversion 1. subst.
    rewrite -!env_subst_typ_comp.
    apply /(typed_app _ _ _ (typ_subst s3 T2)); eauto.
    move: (unify_sound _ _ _ Hunify) => /= <-. eauto.
  - destruct (typing L G t1) as [ [ [ L1 s1 ] T1 ] | ] eqn:Htyping1 => //.
    destruct (typing L1 (T1 :: env_subst s1 G) t2) as [ [ [ ? s2 ] ? ] | ] eqn:Htyping2; inversion 1. subst.
    rewrite -!env_subst_typ_comp.
    apply /typed_let; eauto.
    exact (IHt2 _ _ _ _ _ Htyping2).
Qed.

Theorem typing_complete : forall t L G s T,
  { subset env_fv G <= L } ->
  typed (env_subst s G) t T ->
  exists L' s' s'' T', typing L G t = Some (L', s', T')
    /\ { subset L <= L' } /\ T = typ_subst s'' T'
    /\ (forall x y, x \in typ_fv (s' y) -> x = y \/ x \in L')
    /\ { subset typ_fv T' <= L' }
    /\ { in L, s =1 typ_subst s'' \o s' }.
Proof.
  elim => /= [ x | t IHt | t1 IHt1 t2 IHt2 | t1 IHt1 t2 IHt2 ] L G s T HG; inversion 1; subst.
  - case (leqP (size G) x) => ?.
    { move: (H2 (typ_fvar 0)).
      by rewrite -(H2 (typ_bvar 0)) !nth_default // size_map. }
    exists L, typ_fvar, s, (nth (typ_fvar 0) G x).
    (repeat split) => [ | // | | ? ? /= | ? ? ].
    + by rewrite (nth_map (typ_fvar 0)).
    + by rewrite -(H2 (typ_fvar 0)) /env_subst (nth_map (typ_fvar 0)).
    + rewrite mem_seq1 => /eqP. eauto.
    + apply /HG /env_fv_intro; eauto.
      exact /mem_nth.
  - move: (IHt (gensym L :: L) (typ_fvar (gensym L) :: G) (fun x => if x \in L then s x else T1) T2) => /= [ ? | | L' [ s' [ s'' [ T' [ -> [ HL' [ -> [ Hs' [ HT' Hgen ] ] ] ] ] ] ] ] ].
    + rewrite !in_cons => /orP [ -> // | /HG -> ].
      by rewrite orbT.
    + by rewrite (negbTE (gensym_fresh _)) -(env_subst_ext s) => // ? /HG ->.
    + exists L', s', s'', (typ_arrow (s' (gensym L)) T').
      (repeat split) => [ ? ? | | // | ? /= | ? Hin ].
      * apply /HL'. rewrite in_cons. apply /orP. eauto.
      * move: (Hgen (gensym L)).
        rewrite in_cons eqxx (negbTE (gensym_fresh _)) => -> //.
      * rewrite mem_cat => /orP [ /Hs' [ ] -> | /HT' ] //.
        apply /HL'. by rewrite in_cons eqxx.
      * by rewrite -Hgen ?in_cons Hin // orbT.
  - move: (IHt1 L G s (typ_arrow T1 T)) => [ ] // L1 [ s1 [ s' [ T2' [ -> [ HL1 [ HT [ Hs1fv [ HTfv Hs ] ] ] ] ] ] ] ].
    move: (IHt2 L1 (env_subst s1 G) s' T1) => [ ? /env_fv_subst [ ? [ /Hs1fv [ -> /HG /HL1 | ] // ] ] | | L2 [ s2 [ s'' [ T1' [ -> [ HL2 [ HT1 [ Hs2fv [ HT1fv Hs' ] ] ] ] ] ] ] ] ].
    { by rewrite env_subst_typ_comp -(env_subst_ext s) => // ? /HG /Hs. }
    move: (unify_complete (typ_subst s2 T2') (typ_arrow T1' (typ_fvar (gensym L2))) (fun x => if x \in L2 then s'' x else T)) => [ | s3 [ -> [ [ s''' Hgen ] Hs3fv ] ] ] /=.
    { rewrite (negbTE (gensym_fresh _)) !(typ_subst_ext (fun x => if x \in L2 then s'' x else T) s'') => [ | ? /HT1fv -> | ? /typ_fv_subst [ ? [ /Hs2fv [ <- /HTfv /HL2 | ] -> ] ] ] //.
      rewrite typ_subst_comp (typ_subst_ext (typ_subst s'' \o s2) s') => [ | ? /HTfv /Hs' -> // ].
      congruence. }
    exists (gensym L2 :: L2), (typ_subst (typ_subst s3 \o s2) \o s1), s''', (s3 (gensym L2)).
    (repeat split) => [ ? /HL1 /HL2 | | ? ? /= | ? | ? ? /= ].
    + rewrite in_cons => ->. by rewrite orbT.
    + by rewrite -(Hgen (typ_fvar (gensym L2))) /= (negbTE (gensym_fresh _)).
    + rewrite in_cons -!typ_subst_comp => /typ_fv_subst [ ? [ /Hs3fv /= [ <- /typ_fv_subst [ ? [ /Hs2fv [ <- /Hs1fv [ | /HL2 -> ] | -> ] ] ] | [ /typ_fv_subst [ ? [ /Hs2fv [ <- /HTfv /HL2 | ] -> ] ] | ] ] ] ];
      rewrite ?orbT; eauto.
      rewrite mem_cat mem_seq1 => /orP [ /HT1fv | ] ->; rewrite ?orbT; eauto.
    + rewrite in_cons => /Hs3fv [ /eqP -> | /= [ /typ_fv_subst [ ? [ /Hs2fv [ <- /HTfv /HL2 -> | -> ] ] ] | ] ];
      rewrite ?orbT // mem_cat mem_seq1 => /orP [ /HT1fv | ] -> //.
      by rewrite orbT.
    + rewrite Hs // (typ_subst_ext s' (typ_subst s'' \o s2)) => [ | ? /Hs1fv /= [ -> | /Hs' -> // ] ].
      * rewrite -!typ_subst_comp -Hgen.
        apply /typ_subst_ext => ? /typ_fv_subst [ ? [ /Hs2fv [ <- /Hs1fv [ -> | /HL2 -> ] | -> ] // ] ].
        by rewrite HL2 // HL1.
      * exact /Hs' /HL1.
  - move: (IHt1 L G s T1) => [ ] // L1 [ s1 [ s' [ T1' [ -> [ HL1 [ HT [ Hs1fv [ HTfv Hs ] ] ] ] ] ] ] ].
    move: (IHt2 L1 (T1' :: env_subst s1 G) s' T) => /= [ ? | | L2 [ s2 [ s'' [ T2' [ -> [ HL2 [ HT2 [ Hs2fv [ HT2fv Hs2 ] ] ] ] ] ] ] ] ].
    { by rewrite mem_cat => /orP [ /HTfv | /env_fv_subst [ ? [ /Hs1fv [ <- /HG /HL1 | ] ] ] ]. }
    { by rewrite env_subst_typ_comp -HT -(env_subst_ext s) => // ? /HG /Hs ->. }
    eexists L2, (typ_subst s2 \o s1), s'', T2'.
    (repeat split) => [ ? /HL1 /HL2 | | ? ? /typ_fv_subst [ ? [ /Hs2fv [ <- /Hs1fv [ | /HL2 ] | ] ] ] | | ? ? ]; eauto.
    rewrite Hs // (typ_subst_ext s' (typ_subst s'' \o s2)) ?typ_subst_comp => [ | ? /Hs1fv [ -> /= | /Hs2 ] ] //=.
    by rewrite Hs2 // HL1.
Qed.
