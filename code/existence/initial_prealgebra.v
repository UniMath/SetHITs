(**
Here we define the adjunction between set and setoid algebras.
We first construct an adjunction between the prealgebras and then we factor it through the full subcategory.
 *)
Require Import prelude.all.

Require Import syntax.hit_signature.
Require Import algebras.set_algebra.
Require Import algebras.univalent_algebra.

Definition poly_is_omega_cocont
           (P : poly_code)
  : is_omega_cocont (⦃ P ⦄).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply is_omega_cocont_constant_functor.
    exact has_homsets_HSET.
  - apply is_omega_cocont_functor_identity.
    exact has_homsets_HSET.
  - apply is_omega_cocont_BinCoproduct_of_functors.
    + exact has_homsets_HSET.
    + exact IHP₁.
    + exact IHP₂.
  - apply is_omega_cocont_BinProduct_of_functors.
    + exact BinProductsHSET.
    + exact has_homsets_HSET.
    + exact has_homsets_HSET.
    + apply is_omega_cocont_constprod_functor1.
      * exact has_homsets_HSET.
      * exact Exponentials_HSET.
    + exact IHP₁.
    + exact IHP₂.
Defined.

Definition initial_prealgebra
           (P : poly_code)
  : Initial (set_prealgebras P).
Proof.
  use colimAlgInitial.
  - exact InitialHSET.
  - exact (poly_is_omega_cocont P).
  - apply ColimCoconeHSET.
Defined.