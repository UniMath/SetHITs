(**
Here we interpret HIT signatures in the category of setoids.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import setoids.base.
Require Import setoids.setoid_category.

Require Import algebras.univalent_algebra.
Require Import algebras.set_algebra.

Open Scope cat.

(**
Action of polynomials on equivalence relations.
 *)
Definition poly_eq_rel
           (P : poly_code)
           (X : setoid)
  : eqrel (⦃ P ⦄ (carrier X)).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (path_rel T).
  - exact (carrier_eq X).
  - exact (sum_rel IHP₁ IHP₂).
  - exact (prod_rel IHP₁ IHP₂).
Defined.

(**
Action of polynomials on setoids
 *)
Definition setoid_poly_obj
           (P : poly_code)
           (X : setoid)
  : setoid.
Proof.
  use make_setoid.
  - exact (⦃ P ⦄ (carrier X)).
  - exact (poly_eq_rel P X).
Defined.

(**
This gives rises to a functor
 *)
Definition setoid_poly_mor
           (P : poly_code)
           {X Y : setoid_cat}
           (f : X --> Y)
  : setoid_poly_obj P X → setoid_poly_obj P Y
  := #⦃ P ⦄ (map_carrier f).

Definition setoid_poly_mor_is_morphism
           (P : poly_code)
           {X Y : setoid_cat}
           (f : X --> Y)
           {x y : setoid_poly_obj P X}
           (p : x ≡ y)
  : setoid_poly_mor P f x ≡ setoid_poly_mor P f y.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact p.
  - exact (map_eq f p).
  - induction x as [x | x], y as [y | y].
    + exact (IHP₁ _ _ p).
    + exact (fromempty p).
    + exact (fromempty p).
    + exact (IHP₂ _ _ p).
  - exact (IHP₁ _ _ (pr1 p) ,, IHP₂ _ _ (pr2 p)).
Qed.

Definition setoid_poly_data
           (P : poly_code)
  : functor_data setoid_cat setoid_cat.
Proof.
  use make_functor_data.
  - exact (setoid_poly_obj P).
  - intros X Y f.
    use make_setoid_morphism.
    + exact (setoid_poly_mor P f).
    + exact (@setoid_poly_mor_is_morphism P _ _ f).
Defined.

Definition setoid_poly_is_functor
           (P : poly_code)
  : is_functor (setoid_poly_data P).
Proof.
  split.
  - intros X.
    use setoid_morphism_eq.
    intros x ; cbn.
    induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    + reflexivity.
    + reflexivity.
    + induction x as [x | x].
      * exact (maponpaths inl (IHP₁ x)).
      * exact (maponpaths inr (IHP₂ x)).
    + apply pathsdirprod.
      * exact (IHP₁ (pr1 x)).
      * exact (IHP₂ (pr2 x)).
  - intros X Y Z f g.
    use setoid_morphism_eq.
    intros x ; cbn.
    induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
    + reflexivity.
    + reflexivity.
    + induction x as [x | x].
      * exact (maponpaths inl (IHP₁ x)).
      * exact (maponpaths inr (IHP₂ x)).
    + apply pathsdirprod.
      * exact (IHP₁ (pr1 x)).
      * exact (IHP₂ (pr2 x)).
Qed.

Definition setoid_poly
           (P : poly_code)
  : setoid_cat ⟶ setoid_cat.
Proof.
  use make_functor.
  - exact (setoid_poly_data P).
  - exact (setoid_poly_is_functor P).
Defined.

Notation "⟨ P ⟩" := (setoid_poly P) (at level 10). (* \< \>} *)
Notation "⟨ P ⟩ X" := (setoid_poly P X : setoid) (at level 10).
Notation "# ⟨ P ⟩" := (#(setoid_poly P)) (at level 10).

(**
Univalent category of setoid prealgebras
 *)
Definition setoid_prealgebras
           (P : poly_code)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (FunctorAlg (⟨ P ⟩)).
  - apply is_univalent_FunctorAlg.
    apply setoid_cat_is_univalent.
Defined.

(**
The carrier of a setoid prealgebra is a set prealgebra
 *)
Definition setoid_prealgebra_to_set_prealgebra
           (P : poly_code)
  : setoid_prealgebras P → set_prealgebras P.
Proof.
  intros X.
  use tpair.
  - exact (pr11 X).
  - exact (pr12 X).
Defined.

(**
Forgetful functor of setoid prealgebras
 *)
Definition prealgebra_setoid
           (P : poly_code)
  : setoid_prealgebras P ⟶ setoid_cat
  := forget_algebras _.

(**
Interpretation of endpoins
 *)
Definition setoid_endpoint
           {A P Q : poly_code}
           (e : endpoint A P Q)
           (X : setoid_prealgebras A)
  : setoid_cat ⟦ ⟨ P ⟩ (pr1 X) , ⟨ Q ⟩ (pr1 X) ⟧.
Proof.
  use make_setoid_morphism.
  - exact (set_endpoint e (setoid_prealgebra_to_set_prealgebra A X)).
  - intros x y p.
    induction e.
    + exact p.
    + exact (IHe2 _ _ (IHe1 _ _ p)).
    + exact p.
    + exact p.
    + exact (pr1 p).
    + exact (pr2 p).
    + split.
      * exact (IHe1 _ _ p).
      * exact (IHe2 _ _ p).
    + reflexivity.
    + exact (maponpaths f p).
    + exact (map_eq _ p).
Defined.

(**
Definition of algebras of HIT signatures in setoids
 *)
Definition is_setoid_algebra
           (Σ : hit_signature)
  : hsubtype (setoid_prealgebras (point_arg Σ)).
Proof.
  intro X.
  refine (∀ (j : path_index Σ)
            (x : ⟨ path_arg Σ j ⟩ (prealgebra_setoid _ X)),
             _).
  simple refine (make_hProp _ _).
  + exact (
        (pr1 (setoid_endpoint (path_lhs Σ j) X) x)
          ≡
          pr1 (setoid_endpoint (path_rhs Σ j) X) x).
  + apply isaprop_setoid_eq.
Defined.

(**
Univalent category of setoid algebras
 *)
Definition setoid_algebra
           (Σ : hit_signature)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (full_sub_precategory (is_setoid_algebra Σ)).
  - apply is_univalent_full_subcat.
    apply univalent_category_is_univalent.
Defined.

(**
Projections of algebras
 *)
Section AlgebraProjections.
  Context {Σ : hit_signature}.
  Variable (X : setoid_algebra Σ).
  
  Definition alg_to_prealg
    : setoid_prealgebras (point_arg Σ)
    := pr1 X.

  Definition alg_carrier
    : setoid
    := pr1 alg_to_prealg.

  Definition alg_operation
    : setoid_cat ⟦ ⟨ point_arg Σ ⟩ alg_carrier , alg_carrier ⟧
    := pr2 alg_to_prealg.

  Definition alg_paths
             (j : path_index Σ)
             (x : ⟨ path_arg Σ j ⟩ alg_carrier)
    : pr1 (setoid_endpoint (path_lhs Σ j) alg_to_prealg) x
      ≡
      pr1 (setoid_endpoint (path_rhs Σ j) alg_to_prealg) x
    := pr2 X j x.
End AlgebraProjections.

(**
Projections of algebra maps
 *)
Section AlgebraMapProjections.
  Context {Σ : hit_signature}
          {X Y : setoid_algebra Σ}.
  Variable (f : X --> Y).

  Definition alg_map_carrier
    : setoid_morphism (alg_carrier X) (alg_carrier Y)
    := pr11 f.

  Definition alg_map_is_alg_mor
    : is_algebra_mor (⟨ point_arg Σ ⟩) (alg_to_prealg X) (alg_to_prealg Y) alg_map_carrier
    := pr21 f.
End AlgebraMapProjections.

(**
Builder
 *)
Definition make_prealgebra
           {P : poly_code}
           (X : setoid)
           (c : setoid_cat ⟦ ⟨ P ⟩ X , X ⟧)
  : setoid_prealgebras P.
Proof.
  use tpair.
  - exact X.
  - exact c.
Defined.
           
Definition make_algebra
           {Σ : hit_signature}
           (X : setoid)
           (c : setoid_cat ⟦ ⟨ point_arg Σ ⟩ X , X ⟧)
           (p : ∏ (j : path_index Σ) (x : ⟨ path_arg Σ j ⟩ X),
                pr1 (setoid_endpoint (path_lhs Σ j) (make_prealgebra X c)) x
                ≡
                pr1 (setoid_endpoint (path_rhs Σ j) (make_prealgebra X c)) x)
  : setoid_algebra Σ.
Proof.
  use tpair.
  - exact (make_prealgebra X c).
  - exact p.
Defined.

Definition make_algebra_map
           {Σ : hit_signature}
           {X Y : setoid_algebra Σ}
           (f : setoid_cat ⟦ alg_carrier X , alg_carrier Y ⟧)
           (p : ∏ (x : ⦃ point_arg Σ ⦄ (pr1 (alg_carrier X))),
                pr1 f (pr1 (alg_operation X) x)
                =
                pr1 (alg_operation Y) (#⦃ point_arg Σ ⦄ (pr1 f) x))
  : X --> Y.
Proof.
  use tpair.
  - use tpair.
    + exact f.
    + use setoid_morphism_eq.
      exact p.
  - exact tt.
Defined.

(**
Equality principle for maps beween algebras
 *)
Definition algebra_map_eq
           {Σ : hit_signature}
           {X Y : setoid_algebra Σ}
           {f g : X --> Y}
           (e : ∏ (x : alg_carrier X), alg_map_carrier f x = alg_map_carrier g x)
  : f = g.
Proof.
  use subtypePath.
  {
    intro ; exact isapropunit.
  }
  use subtypePath.
  {
    intro ; simpl.
    apply setoid_cat.
  }
  exact (setoid_morphism_eq _ _ e).
Qed.
