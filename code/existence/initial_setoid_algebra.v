(**
Here we define the initial setoid algebra.
The carrier of this setoid is the initial prealgebra of the point constructor.
The equivalence relation is the freely generated congruence relation.
 *)
Require Import prelude.all.

Require Import setoids.base.
Require Import setoids.setoid_category.

Require Import syntax.hit_signature.

Require Import algebras.set_algebra.
Require Import algebras.setoid_algebra.
Require Import algebras.univalent_algebra.

Require Import existence.initial_prealgebra.
Require Import existence.free_congruence.

Section InitialSetoidAlgebra.
  Variable (Σ : hit_signature).

  Local Notation P := (point_arg Σ).

  Local Definition carrier_initial
    : Initial (set_prealgebras P)
    := initial_prealgebra P.

  (** The carrier *)
  Local Definition carrier
    : set_prealgebras P
    := pr1 carrier_initial.

  (** The equivalence relation *)
  Definition initial_setoid_algebra_carrier
    := mod_congruence carrier.

  (** Proof of initiality *)
  Definition initial_setoid_algebra_is_initial
    : isInitial _ initial_setoid_algebra_carrier.
  Proof.
    intros X.
    apply iscontraprop1.
    - apply invproofirrelevance.
      intros f g.
      use subtypePath.
      { intro ; apply isapropunit. }
      use subtypePath.
      { intro ; apply homset_property. }
      use setoid_morphism_eq.
      intros x.
      pose (φ :=
              (pr111 f ,, funextsec _ _ _ (λ z, eqtohomot (maponpaths pr1 (pr21 f)) z))
              : set_prealgebras P ⟦ pr1 carrier_initial,
                                    setoid_prealgebra_to_set_prealgebra P (pr1 X) ⟧).
      pose (χ :=
              (pr111 g ,, funextsec _ _ _ (λ z, eqtohomot (maponpaths pr1 (pr21 g)) z))
              : set_prealgebras P ⟦ pr1 carrier_initial,
                                    setoid_prealgebra_to_set_prealgebra P (pr1 X) ⟧).
      pose (proofirrelevance
              _
              (isapropifcontr
                 (pr2 carrier_initial (setoid_prealgebra_to_set_prealgebra _ (pr1 X))))
              φ χ) as i.
      exact (eqtohomot (maponpaths pr1 i) x).
    - apply map_mod_congruence.
      apply carrier_initial.
  Defined.

  Definition initial_setoid_algebra
    : Initial (setoid_algebra Σ).
  Proof.
    use tpair.
    - exact initial_setoid_algebra_carrier.
    - exact initial_setoid_algebra_is_initial.
  Defined.
End InitialSetoidAlgebra.