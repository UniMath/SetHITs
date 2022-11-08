(**
Here we interpret HIT signatures in the category of sets.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import algebras.univalent_algebra.

Open Scope cat.

(**
Algebras of functors in sets.
 *)
Definition set_poly
           (P : poly_code)
  : HSET ⟶ HSET.
Proof.
  use sem_poly.
  - exact (functor_identity HSET).
  - exact BinProductsHSET.
  - exact BinCoproductsHSET.
  - exact P.
Defined.

Notation "⦃ P ⦄" := (set_poly P) (at level 10). (* \{{ \}} *)
Notation "⦃ P ⦄ X" := (set_poly P X : hSet) (at level 10).
Notation "# ⦃ P ⦄" := (#(set_poly P)) (at level 10).

Definition set_prealgebras
           (P : poly_code)
  : univalent_category.
Proof.
  use univalent_prealgebras.
  - exact HSET_univalent_category.
  - exact (functor_identity HSET).
  - exact BinProductsHSET.
  - exact BinCoproductsHSET.
  - exact P.
Defined.

Definition prealgebra_to_set
           (P : poly_code)
  : set_prealgebras P ⟶ HSET
  := prealgebra_carrier HSET _ _ _ P.

(**
Algebras of HIT signatures in sets.
 *)
Definition set_endpoint
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : prealgebra_to_set A ∙ ⦃ P ⦄ ⟹ prealgebra_to_set A ∙ ⦃ Q ⦄.
Proof.
  use sem_endpoint.
  - intros T t Y ; cbn in *.
    use make_nat_trans.
    + intros ? ?.
      exact t.
    + intro ; intros.
      reflexivity.
  - exact e.
Defined.

Definition is_set_algebra
           (Σ : hit_signature)           
  : hsubtype (set_prealgebras (point_arg Σ)).
Proof.
  intro X.
  refine (∀ (j : path_index Σ)
            (x : ⦃ path_arg Σ j ⦄ (prealgebra_to_set _ X)),
             _).
  simple refine (make_hProp _ _).
  - exact (set_endpoint (path_lhs Σ j) X x = set_endpoint (path_rhs Σ j) X x).
  - simpl in *.
    apply (prealgebra_to_set _ X).
Defined.

Definition set_algebra
           (Σ : hit_signature)
  : univalent_category.
Proof.
  use make_univalent_category.
  - exact (full_sub_precategory (is_set_algebra Σ)).
  - apply is_univalent_full_subcat.
    apply univalent_category_is_univalent.
Defined.

(**
Projections of prealgebras
 *)
Section PrealgebraProjections.
  Context {P : poly_code}.
  Variable (X : set_prealgebras P).
  
  Definition prealg_carrier
    : hSet
    := pr1 X.

  Definition prealg_operation
    : ⦃ P ⦄ prealg_carrier → prealg_carrier
    := pr2 X.
End PrealgebraProjections.

(**
Projections of algebras
 *)
Section AlgebraProjections.
  Context {Σ : hit_signature}.
  Variable (X : set_algebra Σ).
  
  Definition alg_to_prealg
    : set_prealgebras (point_arg Σ)
    := pr1 X.

  Definition alg_carrier
    : hSet
    := prealg_carrier alg_to_prealg.

  Definition alg_operation
    : ⦃ point_arg Σ ⦄ alg_carrier → alg_carrier
    := prealg_operation alg_to_prealg.

  Definition alg_paths
             (j : path_index Σ)
             (x : ⦃ path_arg Σ j ⦄ alg_carrier)
    : set_endpoint (path_lhs Σ j) alg_to_prealg x
      =
      set_endpoint (path_rhs Σ j) alg_to_prealg x
    := pr2 X j x.
End AlgebraProjections.

(**
Projections of algebra maps
 *)
Section AlgebraMapProjections.
  Context {Σ : hit_signature}
          {X Y : set_algebra Σ}.
  Variable (f : X --> Y).

  Definition alg_map_carrier
    : alg_carrier X → alg_carrier Y
    := pr11 f.

  Definition alg_map_is_alg_mor
    : is_algebra_mor (⦃ point_arg Σ ⦄) (alg_to_prealg X) (alg_to_prealg Y) alg_map_carrier
    := pr21 f.
End AlgebraMapProjections.

(**
Builder for algebras and algebra maps
 *)
Definition make_algebra
           {Σ : hit_signature}
           (X : hSet)
           (c : ⦃ point_arg Σ ⦄ X → X)
           (p : ∏ (j : path_index Σ) (x : ⦃ path_arg Σ j ⦄ X),
                set_endpoint (path_lhs Σ j) (X,, c) x
                =
                set_endpoint (path_rhs Σ j) (X,, c) x)
  : set_algebra Σ
  := (X ,, c) ,, p.

Definition make_algebra_map
           {Σ : hit_signature}
           {X Y : set_algebra Σ}
           (f : alg_carrier X → alg_carrier Y)
           (p : ∏ (x : ⦃ point_arg Σ ⦄ (alg_carrier X)),
                f (alg_operation X x)
                =
                alg_operation Y (#⦃ point_arg Σ ⦄ f x))
  : X --> Y
  := ((f ,, funextsec _ _ _ p) ,, tt).

(**
Equality principle for maps beween algebras
 *)
Definition algebra_map_eq
           {Σ : hit_signature}
           {X Y : set_algebra Σ}
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
    apply SET.
  }
  use funextsec.
  exact e.
Qed.

(** Underlying *)
Definition forgetful
           (Σ : hit_signature)
  : set_algebra Σ ⟶ HSET.
Proof.
  use make_functor.
  - use make_functor_data.
    + intros X.
      apply X.
    + intros X Y f.
      apply f.
  - split ; intro ; reflexivity.
Defined.
