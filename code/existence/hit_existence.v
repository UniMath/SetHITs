(**
Consruction of set truncated HITs
 *)
Require Import prelude.all.

Require Import syntax.hit_signature.
Require Import algebras.set_algebra.
Require Import algebras.setoid_algebra.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.constant_display.
Require Import displayed_algebras.total_algebra_map.
Require Import syntax.hit.

Require Import existence.initial_setoid_algebra.
Require Import existence.algebra_adjunction.

Definition is_initial_is_a_HIT
           {Σ : hit_signature}
           (H : set_algebra Σ)
  : isInitial _ H → is_a_HIT H.
Proof.
  intros HI Y.
  use test2.
  - apply HI.
  - apply (isapropifcontr (HI H)).
Defined.

Definition initial_to_HIT
           {Σ : hit_signature}
           (H : Initial (set_algebra Σ))
  : HIT Σ.
Proof.
  use tpair.
  - apply H.
  - apply is_initial_is_a_HIT.
    apply H.
Defined.

Definition HIT_exists
      (Σ : hit_signature)
  : HIT Σ.
Proof.
  apply initial_to_HIT.
  use tpair.
  - exact (quotient_algebra Σ (initial_setoid_algebra_carrier Σ)).
  - refine (adj_initial (quotient_algebra_adjunction Σ) _ _).
    apply initial_setoid_algebra_is_initial.
Defined.