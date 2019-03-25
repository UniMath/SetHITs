Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import algebras.univalent_algebra.

Open Scope cat.

(**
Algebras in sets.
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
  := prealgebra_carrier HSET _ _ _ _ P.

(**
Algebras in sets
 *)
Definition set_endpoint
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : prealgebra_to_set A ∙ ⦃ P ⦄ ⟹ prealgebra_to_set A ∙ ⦃ Q ⦄.
Proof.
  use sem_endpoint.
  - intros T t Y ; cbn in *.
    use mk_nat_trans.
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
  simple refine (hProppair _ _).
  - exact (set_endpoint (path_lhs Σ j) X x = set_endpoint (path_rhs Σ j) X x).
  - simpl in *.
    apply (prealgebra_to_set _ X).
Defined.

Definition set_algebra
           (Σ : hit_signature)
  : univalent_category.
Proof.
  use mk_category.
  - use (full_sub_precategory _).
    + exact (set_prealgebras (point_arg Σ)).
    + exact (is_set_algebra Σ).
  - apply is_univalent_full_subcat.
    apply set_prealgebras.
Defined.

(**
Prealgebra (of sets) projections
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
Builder
 *)
Definition mk_algebra
           {Σ : hit_signature}
           (X : hSet)
           (c : ⦃ point_arg Σ ⦄ X → X)
           (p : ∏ (j : path_index Σ) (x : ⦃ path_arg Σ j ⦄ X),
                set_endpoint (path_lhs Σ j) (X,, c) x
                =
                set_endpoint (path_rhs Σ j) (X,, c) x)
  : set_algebra Σ
  := (X ,, c) ,, p.

Definition mk_algebra_map
           {Σ : hit_signature}
           {X Y : set_algebra Σ}
           (f : alg_carrier X → alg_carrier Y)
           (p : ∏ (x : ⦃ point_arg Σ ⦄ (alg_carrier X)),
                f (alg_operation X x)
                =
                alg_operation Y (#⦃ point_arg Σ ⦄ f x))
  : X --> Y.
Proof.
  refine ((f ,, _) ,, tt).
  use funextsec.
  exact p.
Defined.