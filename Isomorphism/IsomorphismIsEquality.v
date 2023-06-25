Require Import UniMath.Foundations.All.


Section coding.

Context {U : UU} {El : U -> UU -> UU} {resp : ∏ a, ∏ (B C : UU), B ≃ C -> El a B -> El a C} {resp_id : ∏ a B, ∏ (x : El a B), resp a B B (idweq B) x = x}.


(* Definitions as used in the paper "Isomorphism is equality" *)

Definition Code := ∑ a : U, ∏ C, El a C -> ∑ P, isaprop P.

Definition instance (code : Code) := ∑ C : UU, ∑ x : (El (pr1 code) C), pr1 ((pr2 code) C x). 

Definition isIsomorphism (a : U) {B C} (eq : B ≃ C) (x : El a B) (y : El a C) := (resp a B C eq x) = y.

Definition Isomorphic (code : Code) (x : instance code) (y : instance code) := 
          ∑ eq : (pr1 x) ≃ (pr1 y), isIsomorphism (pr1 code) eq (pr1 (pr2 x)) (pr1 (pr2 y)).

Definition Carrier (code : Code) (inst : instance code) := (pr1 inst).

Definition element (code : Code) (inst : instance code) := pr1 (pr2 inst).



(* Some functions necessary to prove equality_pair_lemma *)
Definition args_to_pair {a : U} (g : ∏ C : UU , El a C -> ∑ P : UU, isaprop P) : 
          (∑ C : UU, El a C) -> (∑ P : UU, isaprop P) := λ x, g (pr1 x) (pr2 x).

Definition from_assoc (a : U) (P: ∏ C : UU, El a C → ∑ P : UU, isaprop P) (delta : ∑ z : ∑ C, El a C, pr1 (P (pr1 z) (pr2 z))) := (tpair (λ iota, ∑ x : El a iota, pr1 (P iota x)) (pr1 (pr1 delta)) (tpair (λ x, pr1 (P (pr1 (pr1 delta)) x)) (pr2 (pr1 delta)) (pr2 delta))).

Lemma equality_pair_lemma : ∏ (c : Code), ∏ (X Y : instance c), (X = Y) ≃ ∑ eq : (Carrier c X = Carrier c Y), 
  transportf (El (pr1 c)) eq ((element c X)) = element c Y.
Proof.
  unfold Code, instance.
  intros code X Y.
  induction code as [a P].
  unfold Carrier, element.
  cbn.
  induction X as [C [x p]].
  induction Y as [D [y q]].
  cbn.
  set (alpha := tpair (λ z, (pr1 (P (pr1 z) (pr2 z)))) (tpair (El (pr1 (a,, P))) C x) p).
  set (beta := tpair (λ z, (pr1 (P (pr1 z) (pr2 z)))) (tpair (El (pr1 (a,, P))) D y) q).
  set (func := λ u : (∑ y, El a y), (pr1 (P (pr1 u) (pr2 u)))).
  set (assoc := @weqtotal2asstor UU (El a) func).
  set (assoc_on_path := weqonpaths assoc alpha beta).
  eapply weqcomp.
  apply invweq.
  apply assoc_on_path.
  unfold alpha, beta.
  set (remove_prop := total2_paths_hProp_equiv (args_to_pair P) ((C,, x),, p) ((D,, y),, q)).
  unfold pr1 in remove_prop.
  eapply weqcomp.
  apply remove_prop.
  (* Equality of sigma types *)
  set (sigma_equality := @total2_paths_equiv UU (El a) (pr1 alpha) (pr1 beta)).
  cbn in sigma_equality.
  unfold PathPair in sigma_equality.
  cbn in sigma_equality.
  apply sigma_equality.
Qed.

Lemma l1f  { X0 X0' : UU } ( ee : X0 = X0' ) ( P : UU -> UU ) ( pp : P X0 ) ( R : ∏ X X' : UU , ∏ w : X ≃ X' , P X -> P X' ) ( r : ∏ X : UU , ∏ p : P X , paths ( R X X ( idweq X ) p ) p ) : paths ( R X0 X0' ( eqweqmap ee ) pp ) (  transportf P ee pp ).
Proof.
  induction ee. simpl. apply r.
Defined.

(* weqtransportbUAH adapted to use transportf and uses axioms instead of UAH could potentially be moved to location of transportbUAH and adapt to use UAH*)
Theorem weqtransportf ( P : UU -> UU )
  ( R : ∏ ( X X' : UU ) ( w :  X ≃ X' ) , P X -> P X' )
  ( r : ∏ X : UU , ∏ p : P X , R X X ( idweq X ) p = p ) :
∏ ( X X' : UU ) ( w :  X ≃ X' ) ( p : P X ),
R X X' w p = transportf P ( weqtopaths w ) p.
Proof.
intros.
set ( uv := weqtopaths w ).
set ( v := eqweqmap uv ).
assert ( e : v = w ) .
- unfold weqtopaths in uv.
  apply ( homotweqinvweq ( univalence X X' ) w ).
- assert ( ee : R X X' v p = R X X' w p ).
  + set ( R' := fun vis : X ≃ X' => R X X' vis p ).
    assert ( ee' : R' v = R' w ).
    * apply (  maponpaths R' e ).
    * assumption.
  + induction ee. apply l1f. assumption.
Defined.

Theorem isomorphism_is_equality : ∏ c X Y, Isomorphic c X Y ≃ (X = Y).
  unfold Isomorphic, isIsomorphism, Code.
  intros code X Y.
  induction code as [a P].
  induction X as [C [x p]].
  induction Y as [D [y q]].
  cbn.
  set ((λ omega pi, (eqweqmap (maponpaths (λ x : El a D, x = y) (weqtransportf (El a) (resp a) (resp_id a) C D pi omega)))) x).
  set (useTransport := weqbandf (idweq (C ≃ D)) _ (λ u, transportf (El a) (weqtopaths u) x = y) w).
  cbn in useTransport.
  eapply weqcomp.
  apply useTransport.
  set (λ x : El a D, x = y).
  set (λ eq : C ≃ D, ((λ x : El a D, x = y) (transportf (El a) (weqtopaths eq) x))).
  set (λ eq, idweq (u0 eq)).
  set (λ eq : C = D, ((λ x : El a D, x = y) (transportf (El a) (eq) x))).
  set (λ eq : C ≃ D, (u0 eq) ≃ (u1 (weqtopaths eq))).
  set (useUnivalence := weqbandf ((invweq (univalence C D))) u0 u1 w0).
  unfold u0, u1 in *.
  eapply weqcomp.
  apply useUnivalence.
  apply invweq.
  apply equality_pair_lemma.
Qed.

End coding.

Section concreteUniverse.

Inductive U : UU :=  
  | id : U
  | type : U
  | k : UU -> U
  | arrow : U -> U -> U
  | cartesian : U -> U -> U
  | binary : U -> U -> U.

Fixpoint El (u : U) (C : UU) : UU :=
  match u with
  | id => C 
  | type => Type
  | k A => A
  | (arrow a b) => (El a C) -> (El b C)
  | (cartesian a b) => (El a C) × (El b C)
  | (binary a b) => (El a C) ⨿ (El b C)
  end.

Definition arrow_eq {A B C D : UU} (x : A ≃ B) (y : C ≃ D) : (A -> C) ≃ (B -> D)
  := (weqcomp (weqbfun C (invweq x)) (weqffun B y)).

Definition cartesian_eq {A B C D : UU} (x : A ≃ B) (y : C ≃ D) : A × C ≃ B × D
    := weqdirprodf x y.    

Definition binary_eq {A B C D : UU} (x : A ≃ B) (y : C ≃ D) : (A ⨿ C) ≃ (B ⨿ D)
  := weqcoprodf x y.

Fixpoint cast (a : U) {B C : UU} (eq : B ≃ C) : (El a B) ≃ (El a C)
 :=
 match a with
 | id => (eq : (El id B) ≃ (El id C))
 | type => (idweq Type)
 | (k A) => (idweq A)
 | (arrow l r) => (@arrow_eq (El l B) (El l C) (El r B) (El r C)  (cast l eq) (cast r eq))
 | (cartesian l r) => (@cartesian_eq (El l B) (El l C) (El r B) (El r C)  (cast l eq) (cast r eq))
 | (binary l r) => (@binary_eq (El l B) (El l C) (El r B) (El r C)  (cast l eq) (cast r eq))
 end.

(* to-do: define cast_id, for isomorphisms is isomorphic: prove function and binary sum cases *)

Definition resp (a : U) (B C : UU) (eq : B ≃ C) : El a B -> El a C := pr1weq (cast a eq).

Context {cast_id : ∏ (a : U) (B : UU), (cast a (idweq B)) = (idweq (El a B))}.

Definition resp_id  (a : U) (B C : UU) (x : El a B) : resp a B B (idweq B) x = x := (@maponpaths (El a B ≃ El a B) (El a B) (λ f, f x) (cast a (idweq B)) (idweq (El a B)) (cast_id a B)).


Definition arrow_rel {a b : U} {B C : UU} (P : (El a B) -> (El a C) -> UU) (Q : (El b B) -> (El b C) -> UU) (f : El (arrow a b) B) (g : El (arrow a b) C) := ∏ x y, P x y -> Q (f x) (g y).

Definition cartesian_rel {a b : U} {B C : UU} (P : (El a B) -> (El a C) -> UU) (Q : (El b B) -> (El b C) -> UU) (l : El (cartesian a b) B) (r : El (cartesian a b) C) := (P (pr1 l) (pr1 r)) × (Q (pr2 l) (pr2 r)).

Definition binary_rel {a b : U} {B C : UU} (P : (El a B) -> (El a C) -> UU) (Q : (El b B) -> (El b C) -> UU) (l : El (binary a b) B) (r : El (binary a b) C)
  :=
  match l, r with
  | ii1 x, ii1 y => P x y
  | ii1 x, ii2 v => ∅
  | ii2 u, ii1 y => ∅
  | ii2 u, ii2 v => Q u v
  end.

Fixpoint isIsomorphism' (a : U) {B C : UU} (eq : B ≃ C) : ∏ (x : El a B) (y : El a C), UU
  :=
  match a with
  | id => λ x y, ((pr1weq eq) (x : El id B)) = (y : El id C)
  | type => λ X Y, X ≃ Y
  | (k A) => λ x y, (x = y)
  | (arrow l r) => arrow_rel (isIsomorphism' l eq) (isIsomorphism' r eq)
  | (cartesian l r) => cartesian_rel (isIsomorphism' l eq) (isIsomorphism' r eq)
  | (binary l r) => binary_rel (isIsomorphism' l eq) (isIsomorphism' r eq)
  end.

Theorem Isomorphisms_are_equivalent (a : U) (B C : UU) (x : El a B) (y : El a C) (eq : B ≃ C) : (@isIsomorphism U El resp a B C eq x y) ≃ (isIsomorphism' a eq x y).
Proof.
  unfold isIsomorphism.
  unfold resp.
  induction a; (try apply idweq).
  - apply univalence.
  - cbn.
    (* unfold arrow_rel.
    set (El (arrow a1 a2) B).
    (* (arrow a1 a2) => (El a1 C) -> (El a2 C) *)
    unfold maponsec.
    unfold maponsec1.
    apply eqweqmap.
    set (@weqfunextsec).
    unfold homot in w.
    set (w (El a1 C)).
    set ((((λ x0 : El a1 C,
    cast a2 eq (x (invmap (cast a1 eq) x0)))) =
   y)).
   set (@arrow_eq).
    set (@maponpaths).
    set (λ x, x = y).
    (* set(w0 (λ x, x = y)). *)
    invmap *)
    admit.
  - cbn.
    unfold cartesian_rel.
    set (weqdirprodf (IHa1 (pr1 x) (pr1 y)) (IHa2 (pr2 x) (pr2 y))).
    apply invweq.
    eapply weqcomp.
    apply (invweq w).
    set (@total2_paths_equiv).
    unfold PathPair in w0.
    apply invweq.
    cbn in x, y.
    set (w0 (El a1 C)).
    set (w1 ((λ _, El a2 C))).
    set (w2 (tpair _ (resp a1 B C eq (pr1 x)) ((λ _, (resp a2 B C eq (pr2 x))) (resp a1 B C eq (pr1 x)))) (tpair _ (pr1 y) (pr2 y))).
    cbn in w3.
    unfold resp in w3.
    unfold dirprodf.
    unfold make_dirprod.
    eapply weqcomp.
    apply w3.
    unfold dirprod.
    cbn.
    set (@weqbandf (cast a1 eq (pr1 x) = pr1 y) (cast a1 eq (pr1 x) = pr1 y) (idweq (cast a1 eq (pr1 x) = pr1 y)) ((λ p, transportf (λ _ : El a1 C, El a2 C) p (cast a2 eq (pr2 x)) = pr2 y)) (λ _, (cast a2 eq (pr2 x) = pr2 y))).
    cbn in w4.
    apply w4.
    intros.
    set (transportf_const x0 (El a2 C)).
    unfold idfun in p.
    set (maponpaths (λ un, un (cast a2 eq (pr2 x))) p).
    cbn in p0.
    apply eqweqmap.
    set (cast a2 eq (pr2 x)).
    set (@maponpaths (El a2 C) UU (λ unk : (El a2 C), unk = (pr2 y)) (transportf (λ _ : El a1 C, El a2 C) x0 e) e).
    apply p1.
    apply p0.
  - cbn.
    unfold binary_rel.
    induction x, y.
    + set (IHa1 a e).
      apply invweq.
      eapply weqcomp.
      apply invweq.
      apply w.
      unfold coprodf.
      set (@ii1_injectivity (El a1 C) unit (cast a1 eq a)  e).
      set (@coprodtobool (El a1 C) unit (ii1 (cast a1 eq a))).
      set (cast a1 eq a = e).
      set (ii1 (cast a1 eq a) = ii1 e).
      set (λ a b : El a1 C, (@ii1 (El a1 C) unit a) = (ii1 b)).
      set (u1 (cast a1 eq a) e).
      set (@maponpaths (El a1 C) ((El a1 C) ⨿ unit) (@ii1 (El a1 C) unit) (cast a1 eq a) e).
      unfold u, u0.
      set (@equality_by_case ).
      unfold equality_cases in e0.
      cbn in e0.
      
      set (@make_weq (cast a1 eq a = e) (inl (cast a1 eq a) = inl e) p0).
      apply idweq.
      (* P OR FALSE IS EQUIVALENT TO P *)
      admit.
    + 
      unfold coprodf.
      apply weqtoempty.
      intros.
      set (@negpathsii1ii2 (El a1 C) (El a2 C) (cast a1 eq a) e).
      unfold neg in n.
      apply (n X).
    + 
      unfold coprodf.
      apply weqtoempty.
      intros.
      set (@negpathsii2ii1 (El a1 C) (El a2 C) e (cast a2 eq b)).
      unfold neg in n.
      apply (n X).
    + 
      set (IHa2 b e).
      apply invweq.
      eapply weqcomp.
      apply invweq.
      apply w.
      unfold coprodf.
      unfold cast.
      apply idweq.
      admit.
Admitted.


End concreteUniverse.
