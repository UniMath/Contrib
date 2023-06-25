Require Export UniMath.Foundations.All.
Require Export UniMath.MoreFoundations.All.

Definition apD {X:Type} {Y : X -> Type} (s : ∏ x, Y x) {x x':X} (p : x = x') :
  transportf Y p (s x) = s x'.
Proof.
  now induction p.
Defined.

Module Export S1.

Private Inductive S1 : Type :=
| base : S1.

Axiom loop : base = base.

Definition S1_ind (P : S1 -> Type) (b : P base) (l : transportf P loop b = b)
  : forall x : S1, P x :=
  fun x =>
    match x with
    | base => b
    end.

Axiom S1_ind_loop : forall (P : S1 -> Type) (b : P base) (l : transportf P loop b = b),
  apD (S1_ind P b l) loop = l.

Definition S1_recur (A : Type) (a : A) (l : a = a) : S1 -> A :=
  fun x =>
    match x with
    | base => a
    end.

Axiom S1_recur_loop : forall (A : Type) (a : A) (l : a = a) ,
  maponpaths (S1_recur A a l) loop = l.

End S1.

Lemma circle_connected : forall (z: S1), ∥ z = base ∥.
Proof.
  intro z.
  use (S1_ind (fun z => ∥ z = base ∥) _ _ z).
  - exact (hinhpr (idpath base)). 
  - apply propproperty.
Qed.

Definition ev (A : Type) : 
  (S1 → A) → ∑ (a : A), a = a :=
  fun g => tpair (fun a => a = a) (g base) (maponpaths g loop).

Definition ve (A : Type) :
  (∑ (a : A), a = a) → (S1 → A) :=
  fun p => S1_recur A (pr1 p) (pr2 p).

Theorem evisweq (A : UU) : isweq (ev A).
Proof.
  use isweq_iso.
  - exact (ve A).
  - intro f.
    unfold ve.
    unfold ev.
    simpl.
    apply funextfun. (* provided by Copilot *)
    use S1_ind.
    + reflexivity.
    + simpl.
      rewrite transportf_paths_FlFr.
      rewrite S1_recur_loop.
      simpl.
      use pathsinv0l.
  - intro p.
    unfold ev.
    unfold ve.
    simpl.
    rewrite S1_recur_loop.
    reflexivity.
Qed.

Definition SetBundle (B : UU) : UU := ∑ (A : UU) (f : A -> B), ∏ (b : B), isaset (hfiber f b).

Lemma map_rl {A : UU} : (∑ (B : UU) (f : B -> A) , ∏ (a : A), isaset (hfiber f a)) -> (A -> hSet).
Proof.
  intro Bf.
  intro a.
  exact (make_hSet _ ((pr2 (pr2 Bf)) a)).
Defined.

Lemma map_lr {A : UU} : (A -> hSet) -> (∑ (B : UU) (f : B -> A) , ∏ (a : A), isaset (hfiber f a)).
Proof.
  intro f.
  use tpair.
  - exact (∑ (a : A), f a).
  - simpl.
    use tpair.
    + exact pr1.
    + simpl.
      intro a.
      use (isofhlevelweqf 2).
      * exact (f a).
      * use weq_iso.
        -- intro x.
            use make_hfiber. 
            ++ use tpair.
              ** exact a.
              ** exact x.
            ++ reflexivity.
        -- intro x.
            refine (transportf f _ (pr21 x)).
            exact (pr2 x).
        -- simpl.
            intro x.
            reflexivity.
        -- intro x.
            induction x as [y z].
            induction z.
            reflexivity.
      * set (test := f a).
        apply (pr2 test). (* Given by copilot. *)
Defined.

Lemma map_inv_eq_lrrl {A : Type} (Bf : (∑ (B : UU) (f : B -> A) , ∏ (a : A), isaset (hfiber f a))) : (map_lr (map_rl Bf)) = Bf.
Proof.
  use total2_paths_f.
  - apply weqtopaths.
    apply sum_of_fibers.
  - induction Bf as [B fH].
    induction fH as [f H].
    use subtypePath.
    + intro. 
      apply impred_isaprop.
      intro t.
      apply isapropisaset.
    + simpl. 
      rewrite transportf_total2.
      simpl.
      rewrite transportf_fun.
      rewrite <- eqweqmap_transportb.
      simpl.
      rewrite eqweqmap_pathsinv0.
      rewrite eqweqmap_weqtopaths.
      reflexivity.
Qed.

Lemma map_inv_eq_rllr {A : UU} (f : A -> hSet) : (map_rl (map_lr f)) = f.
Proof.
  apply funextfun.
  intro a.
  apply hSet_univalence.
  cbn.
  use weq_iso.
  - intro fib.
    refine (transportf f _ (pr21 fib)).
    exact (pr2 fib).
  - intro x.
    use make_hfiber. 
    ++ use tpair.
      ** exact a.
      ** exact x.
    ++ reflexivity.
  - simpl.
    intro x.
    induction x as [y z]. 
    induction z.
    reflexivity.
  - simpl.
    intro y.
    reflexivity. 
Qed.

Lemma set_families (A : UU) : (∑ (B : UU) (f : B -> A) , ∏ (a : A), isaset (hfiber f a)) ≃ (A -> hSet).
Proof.
  exists map_rl. 
  apply (isweq_iso map_rl map_lr).
  - exact map_inv_eq_lrrl.
  - exact map_inv_eq_rllr.
Qed.

Theorem ev_set_equiv (B : UU) : isweq (ev (hSet)).
Proof.
  use evisweq.
Qed.

Theorem setbundle_s1_set : SetBundle S1 ≃ (S1 -> hSet).
Proof.
  use (set_families S1).
Qed.

Theorem s1_set_sigmaequals : (S1 -> hSet) ≃ ∑ (X : hSet), X = X.
Proof.
  use tpair.
  - exact (ev hSet).
  - simpl. exact (evisweq hSet).
Qed.

Theorem setbundle_sigmaeq_sigmasimeq : (∑ (X : hSet), X = X) ≃ (∑ (X : hSet), X ≃ X).
Proof.
  apply weqfibtototal.
  intro X.
  apply hSet_univalence.
Qed.

Theorem sigmasimeq_isSet_times_isEquiv : (∑ (X : hSet), X ≃ X) ≃ (∑ (X : UU) (f : X -> X), ((isaset X) × (isweq f))).
Proof.
  use weq_iso.
  - intro Xp.
    induction Xp as [X p].
    use tpair.
    + exact X.
    + simpl.
      use tpair.
      * exact p.
      * split. (* provided by copilot *)
        -- exact (pr2 X).
        -- exact (pr2 p).
  - intro Xfpr.
    induction Xfpr as [X fpr].
    induction fpr as [f pr].
    induction pr as [p r].
    use tpair.
    + exact (make_hSet X p).
    + simpl.
      use tpair.
      * exact f.
      * simpl. exact r.
  - reflexivity.
  - reflexivity.
Qed.

Theorem string_of_equivalences : SetBundle S1 ≃ (∑ (X : UU) (f : X -> X), ((isaset X) × (isweq f))).
Proof.
  use weqcomp.
  - exact (S1 -> hSet).
  - exact setbundle_s1_set.
  - use weqcomp.
    + exact (∑ (X : hSet), X = X).
    + exact s1_set_sigmaequals.
    + use weqcomp.
      * exact ((∑ (X : hSet), X ≃ X)).
      * exact setbundle_sigmaeq_sigmasimeq.
      * exact sigmasimeq_isSet_times_isEquiv.
Qed.