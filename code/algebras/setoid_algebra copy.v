Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import setoids.base.
Require Import setoids.setoid_category.

Require Import algebras.univalent_algebra.
Require Import algebras.set_algebra.

Open Scope cat.
      
(**
Algebras in setoids.
 *)
Definition setoid_poly
           (P : poly_code)
  : setoid_cat ⟶ setoid_cat.
Proof.
  use sem_poly.
  - exact path_setoid.
  - exact setoid_cat_biproducts.
  - exact setoid_cat_bicoproducts.
  - exact P.
Defined.

Notation "⟨ P ⟩" := (setoid_poly P) (at level 10). (* \< \>} *)
Notation "⟨ P ⟩ X" := (setoid_poly P X : setoid) (at level 10).
Notation "# ⟨ P ⟩" := (#(setoid_poly P)) (at level 10).

Definition setoid_prealgebras
           (P : poly_code)
  : category.
Proof.
  use tpair.
  - use (prealgebras setoid_cat).
    + exact path_setoid.
    + exact setoid_cat_biproducts.
    + exact setoid_cat_bicoproducts.
    + apply setoid_cat.
    + exact P.
  - apply has_homsets_FunctorAlg.
Defined.

Definition prealgebra_setoid
           (P : poly_code)
  : setoid_prealgebras P ⟶ setoid_cat
  := prealgebra_carrier setoid_cat _ _ _ _ P.

Definition setoid_endpoint
           {A P Q : poly_code}
           (e : endpoint A P Q)
  : prealgebra_setoid A ∙ (⟨ P ⟩) ⟹ prealgebra_setoid A ∙ ⟨ Q ⟩.
Proof.
  use sem_endpoint.
  - intros T t Y ; cbn in *.
    use mk_nat_trans.
    + intro ; cbn in *.
      use mk_setoid_morphism.
      * intro ; cbn.
        exact t.
      * reflexivity.
    + intro ; intros.
      reflexivity.
  - exact e.
Defined.

Definition is_setoid_prealgebra
           (Σ : hit_signature)
  : hsubtype (setoid_prealgebras (point_arg Σ)).
Proof.
  intro X.
  refine (∀ (j : path_index Σ)
            (x : ⟨ path_arg Σ j ⟩ (prealgebra_setoid _ X)),
             _).
  simple refine (hProppair _ _).
  + exact (
        ((setoid_endpoint (path_lhs Σ j) X : setoid_morphism _ _) x)
          ≡
          ((setoid_endpoint (path_rhs Σ j) X) : setoid_morphism _ _) x).
  + apply isaprop_setoid_eq.
Defined.

Definition setoid_algebra
           (Σ : hit_signature)
  : category.
Proof.
  use tpair.
  - use (full_sub_precategory _).
    + exact (setoid_prealgebras (point_arg Σ)).
    + exact (is_setoid_prealgebra Σ).
  - intros X Y.
    apply isaset_total2.
    + apply homset_property.
    + intro.
      apply isasetunit.
Defined.