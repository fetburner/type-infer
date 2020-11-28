From mathcomp Require Import all_ssreflect.

Section Rename.
  Definition upren r x :=
    if x is x.+1 then (r x).+1 else 0.
  Definition upnren r n := iter n upren r.

  Corollary upnrenS r n x : upren (upnren r n) x = upnren (upren r) n x.
  Proof. by rewrite /upnren -iterSr. Qed.

  Lemma upnren_unfold r n : forall x,
    upnren r n x = if x < n then x else n + r (x - n).
  Proof.
    induction n => [ ? | [ | ? ] ] //=.
    - by rewrite subn0.
    - by rewrite IHn (fun_if succn).
  Qed.

  Lemma eq_upren r r' : forall x,
    (0 < x -> r x.-1 = r' x.-1) ->
    upren r x = upren r' x.
  Proof. by rewrite /upren => [ [ | ? /= -> ] ]. Qed.

  Lemma eq_upnren r r' n x :
    (n <= x -> r (x - n) = r' (x - n)) ->
    upnren r n x = upnren r' n x.
  Proof.
    rewrite !upnren_unfold.
    by case: (leqP n x) => [ ? -> | ].
  Qed.

  Lemma upren_id : forall x, upren id x = x.
  Proof. by move => [ | ? ]. Qed.

  Lemma upnren_id n : forall x, upnren id n x = x.
  Proof.
    induction n => ? //=.
    by rewrite (eq_upren _ id _ (fun _ => IHn _)) upren_id.
  Qed.

  Lemma upren_comp r r' :
    upren (r \o r') =1 upren r \o upren r'.
  Proof. by move => [ | ? ]. Qed.

  Lemma upnren_comp n : forall r r',
    upnren (r \o r') n =1 upnren r n \o upnren r' n.
  Proof.
    induction n => ? ? ? //=.
    by rewrite (eq_upren _ _ _ (fun _ => IHn _ _ _)) upren_comp.
  Qed.

  Class Rename (term : Set) :=
    { var : nat -> term;
      rename : (nat -> nat) -> term -> term;
      rename_var : forall r x, rename r (var x) = var (r x);
      eq_rename : forall t r r', (forall x, r x = r' x) -> rename r t = rename r' t }.

  Class RenameLemmas (term : Set) {RenameTerm : Rename term} :=
    { rename_id : forall t, rename id t = t;
      rename_rename_comp : forall t r r', rename r (rename r' t) = rename (r \o r') t }.

  Context {term : Set} {RenameTerm : Rename term}.

  Lemma rename_id_upren t :
    rename id t = t ->
    rename (upren id) t = t.
  Proof. by rewrite (eq_rename _ _ _ upren_id). Qed.

  Lemma rename_id_upnren t
    (_ : rename id t = t) n :
    rename (upnren id n) t = t.
  Proof. by rewrite (eq_rename _ _ _ (upnren_id _)). Qed.

  Lemma rename_rename_comp_upren t
    (_ : forall r r', rename r (rename r' t) = rename (r \o r') t) r r' :
    rename (upren r) (rename (upren r') t) = rename (upren (r \o r')) t.
  Proof. by rewrite (eq_rename _ _ _ (upren_comp _ _)). Qed.

  Lemma rename_rename_comp_upnren t
    (_ : forall r r', rename r (rename r' t) = rename (r \o r') t) r r' n :
    rename (upnren r n) (rename (upnren r' n) t) = rename (upnren (r \o r') n) t.
  Proof. by rewrite (eq_rename _ _ _ (upnren_comp _ _ _)). Qed.
End Rename.

Section Subst.
  Context {term : Set} {RenameTerm : Rename term} {RenameLemmaTerm : RenameLemmas term}.

  Definition up s x :=
    if x is x.+1 then rename succn (s x) else var 0.
  Definition upn s n := iter n up s.

  Corollary upnS s n x : up (upn s n) x = upn (up s) n x.
  Proof. by rewrite /upn -iterSr. Qed.

  Lemma upn_unfold s n : forall x,
    upn s n x = if x < n then var x else rename (addn n) (s (x - n)).
  Proof.
    induction n => [ ? | [ | ? ] ] //=.
    - by rewrite subn0 (eq_rename _ _ id) ?rename_id.
    - rewrite ltnS subSS IHn (fun_if (rename succn)) rename_var rename_rename_comp.
      congr (if _ then _ else _).
  Qed.

  Lemma eq_up s s' : forall x,
    (0 < x -> s x.-1 = s' x.-1) ->
    up s x = up s' x.
  Proof. by move => [ | ? /= -> ]. Qed.

  Lemma eq_upn s s' n x :
    (n <= x -> s (x - n) = s' (x - n)) ->
    upn s n x = upn s' n x.
  Proof. rewrite !upn_unfold. by case: (leqP n x) => [ ? -> | ]. Qed.

  Lemma up_var : forall x, up var x = var x.
  Proof. move => [ | ? ] //=. by rewrite rename_var. Qed.

  Lemma upn_var n : forall x, upn var n x = var x.
  Proof.
    induction n => ? //=.
    by rewrite (eq_up _ var _ (fun _ => IHn _)) up_var.
  Qed.

  Lemma up_upren r : var \o upren r =1 up (var \o r).
  Proof. move => [ | ? ] //=. by rewrite rename_var. Qed.

  Lemma upn_upnren r n : var \o upnren r n =1 upn (var \o r) n.
  Proof.
    induction n => ? //=.
    by rewrite -(eq_up _ _ _ (fun _ => IHn _)) -up_upren.
  Qed.

  Lemma up_upren_comp s r :
    up (s \o r) =1 up s \o upren r.
  Proof. by move => [ | ? ]. Qed.

  Lemma upn_upnren_comp s r n :
    upn (s \o r) n =1 upn s n \o upnren r n.
  Proof.
    induction n => ? //=.
    by rewrite (eq_up _ _ _ (fun _ => IHn _)) up_upren_comp.
  Qed.

  Lemma upren_up_comp r s :
    up (rename r \o s) =1 rename (upren r) \o up s.
  Proof.
    move => [ | ? ] /=.
    - by rewrite rename_var.
    - rewrite !rename_rename_comp.
      exact: eq_rename.
  Qed.

  Lemma upnren_upn_comp r s n :
    upn (rename r \o s) n =1 rename (upnren r n) \o upn s n.
  Proof.
    induction n => ? //=.
    by rewrite (eq_up _ _ _ (fun _ => IHn _)) upren_up_comp.
  Qed.

  Class Subst :=
    { subst : (nat -> term) -> term -> term;
      subst_var : forall s x, subst s (var x) = s x;
      eq_subst : forall t s s', (forall x, s x = s' x) -> subst s t = subst s' t }.

  Context {SubstTerm : Subst}.

  Lemma rename_subst_up t
    (_ : forall r, rename r t = subst (var \o r) t) r :
    rename (upren r) t = subst (up (var \o r)) t.
  Proof. by rewrite -(eq_subst _ _ _ (up_upren _)). Qed.

  Lemma rename_subst_upn t
    (_ : forall r, rename r t = subst (var \o r) t) r n :
    rename (upnren r n) t = subst (upn (var \o r) n) t.
  Proof. by rewrite -(eq_subst _ _ _ (upn_upnren _ _)). Qed.

  Lemma subst_id_up t
    (_ : subst var t = t) :
    subst (up var) t = t.
  Proof. by rewrite (eq_subst _ _ _ up_var). Qed.

  Lemma subst_id_upn t
    (_ : subst var t = t) n :
    subst (upn var n) t = t.
  Proof. by rewrite (eq_subst _ _ _ (upn_var _)). Qed.

  Lemma subst_rename_comp_up t
    (_ : forall r s, subst s (rename r t) = subst (s \o r) t) r s :
    subst (up s) (rename (upren r) t) = subst (up (s \o r)) t.
  Proof. by rewrite (eq_subst _ _ _ (up_upren_comp _ _)). Qed.

  Lemma subst_rename_comp_upn t
    (_ : forall r s, subst s (rename r t) = subst (s \o r) t) r s n :
    subst (upn s n) (rename (upnren r n) t) = subst (upn (s \o r) n) t.
  Proof. by rewrite (eq_subst _ _ _ (upn_upnren_comp _ _ _)). Qed.

  Lemma rename_subst_comp_up t
    (_ : forall r s, rename r (subst s t) = subst (rename r \o s) t) r s :
    rename (upren r) (subst (up s) t) = subst (up (rename r \o s)) t.
  Proof. by rewrite (eq_subst _ _ _ (upren_up_comp _ _)). Qed.

  Lemma rename_subst_comp_upn t
    (_ : forall r s, rename r (subst s t) = subst (rename r \o s) t) r s n :
    rename (upnren r n) (subst (upn s n) t) = subst (upn (rename r \o s) n) t.
  Proof. by rewrite (eq_subst _ _ _ (upnren_upn_comp _ _ _)). Qed.

  Class SubstLemmas :=
    { subst_id t : subst var t = t;
      rename_subst t : forall r, rename r t = subst (var \o r) t;
      subst_rename_comp : forall t r s, subst s (rename r t) = subst (s \o r) t;
      rename_subst_comp : forall t r s, rename r (subst s t) = subst (rename r \o s) t }.

  Context {SubstLemmasTerm : SubstLemmas}.

  Lemma up_up_comp s s' :
    up (subst s \o s') =1 subst (up s) \o up s'.
  Proof.
    move => [ | ? ] /=.
    - by rewrite subst_var.
    - rewrite rename_subst_comp subst_rename_comp.
      exact: eq_subst.
  Qed.

  Lemma upn_upn_comp s s' n :
    upn (subst s \o s') n =1 subst (upn s n) \o upn s' n.
  Proof.
    induction n => ? //=.
    by rewrite (eq_up _ _ _ (fun _ => IHn _)) up_up_comp.
  Qed.

  Lemma subst_subst_comp_up t
    (_ : forall s s', subst s (subst s' t) = subst (subst s \o s') t) s s' :
    subst (up s) (subst (up s') t) = subst (up (subst s \o s')) t.
  Proof. by rewrite (eq_subst _ _ _ (up_up_comp _ _)). Qed.

  Lemma subst_subst_comp_upn t
    (_ : forall s s', subst s (subst s' t) = subst (subst s \o s') t) s s' n :
    subst (upn s n) (subst (upn s' n) t) = subst (upn (subst s \o s') n) t.
  Proof. by rewrite (eq_subst _ _ _ (upn_upn_comp _ _ _)). Qed.

  Class SubstLemmas' :=
    { subst_subst_comp : forall t s s', subst s (subst s' t) = subst (subst s \o s') t }.
End Subst.

Arguments Subst term {RenameTerm}.
Arguments SubstLemmas term {RenameTerm SubstTerm}.
Arguments SubstLemmas' term {RenameTerm SubstTerm}.

Definition scons {A} (a : A) s x :=
  if x is x.+1 then s x else a.
