(**
The propositional truncation of a set.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import syntax.hit.
Require Import algebras.set_algebra.

Require Import existence.hit_existence.

Open Scope cat.

(** We first define the signature. *)

(** Operations *)
Section Truncation.
  Variable (A : hSet).
  
  Definition truncation_operations
    : poly_code
    := C A.

  (** Labels of group axioms *)
  Inductive truncation_ax : Type :=
  | all_paths : truncation_ax.

  (** Arguments for each label *)
  Definition truncation_arg
    : truncation_ax → poly_code
    := λ z, I * I.

  (** The left hand side of each equation *)
  Definition truncation_lhs
    : ∏ (j : truncation_ax), endpoint truncation_operations (truncation_arg j) I
    := λ _, comp (id_e _ (I * I)) (π₁ I I).

  (** The right hand side of each equation *)
  Definition truncation_rhs
    : ∏ (j : truncation_ax), endpoint truncation_operations (truncation_arg j) I
    := λ _, comp (id_e _ (I * I)) (π₂ I I).

  (** The signature of the truncation as a HIT signature *)
  Definition truncation_signature
    : hit_signature.
  Proof.
    use tpair.
    - exact truncation_operations.
    - use tpair.
      + exact truncation_ax.
      + use tpair.
        * exact truncation_arg.
        * split.
          ** exact truncation_lhs.
          ** exact truncation_rhs.
  Defined.
End Truncation.

Definition propositonal_truncation
           (A : hSet)
  : hProp.
Proof.
  pose (H := HIT_exists (truncation_signature A)).
  use hProppair.
  - apply H.
  - apply invproofirrelevance.
    intros x y.
    exact (alg_paths H all_paths (x ,, y)).
Defined.