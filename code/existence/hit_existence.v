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

Require Import existence.free_congruence.
Require Import existence.initial_prealgebra.
Require Import existence.initial_setoid_algebra.
Require Import existence.algebra_adjunction.

Require Import setoids.base.

(**
First, we conclude that initiality is sufficient to be a HIT
 *)
Definition is_initial_is_a_HIT
           {Σ : hit_signature}
           (H : set_algebra Σ)
  : isInitial _ H → is_a_HIT H.
Proof.
  intros HI Y.
  use section_to_disp_alg_map.
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

(**
We conclude that HITs exist.
To construct an initial object, we use the quotient adjunction.
Note that we have an initial algebra in setoids.
 *)
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

(**
From this construction, we get a characterization of the path space of a HIT as inductive type.
 *)
Section HITPathSpace.
  Context {Σ : hit_signature}.

  Local Notation H := (pr111 (HIT_exists Σ) : hSet).
  
  Definition hit_path_space
             {x₁ x₂ : prealg_carrier (InitialObject (initial_prealgebra (point_arg Σ)))}
    : (generated_eqrel
                (pr11 (initial_prealgebra (point_arg Σ)))
                (pr21 (initial_prealgebra (point_arg Σ)))
                (rel Σ _ (pr21 (initial_prealgebra (point_arg Σ))))
                x₁ x₂)
        ≃
        (setquotpr _ x₁ : H) = setquotpr _ x₂.
  Proof.
    apply weqpathsinsetquot.
  Defined.
End HITPathSpace.