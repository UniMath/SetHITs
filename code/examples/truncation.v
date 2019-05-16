(**
The propositional truncation of a set.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import syntax.hit.
Require Import syntax.hit_properties.
Require Import algebras.set_algebra.
Require Import existence.hit_existence.
Require Import displayed_algebras.displayed_algebra.

Require Import existence.hit_existence.

Open Scope cat.
Opaque HIT_exists hit_ind hit_ind_prop hit_rec.

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

Definition propositional_truncation_HIT
           (A : hSet)
  : HIT (truncation_signature A)
  := HIT_exists (truncation_signature A).

Definition propositional_truncation
           (A : hSet)
  : hProp.
Proof.
  use make_hProp.
  - apply (propositional_truncation_HIT A).
  - apply invproofirrelevance.
    intros x y.
    exact (alg_paths (propositional_truncation_HIT A) all_paths (x ,, y)).
Defined.

Definition trunc_inc
           {A : hSet}
  : A → propositional_truncation A
  := alg_operation (propositional_truncation_HIT A).

Definition trunc_ind_disp_alg
           (A : hSet)
           {Y : propositional_truncation A → UU}
           (Yprop : ∏ (a : propositional_truncation A), isaprop (Y a))
           (f : ∏ (a : A), Y (trunc_inc a))
  : disp_algebra (propositional_truncation_HIT A).
Proof.
  use make_disp_algebra.
  - intro x.
    use make_hSet.
    + exact (Y x).
    + apply isasetaprop.
      exact (Yprop x).
  - intros x Hx.
    exact (f x).
  - intros.
    apply Yprop.
Defined.

Definition trunc_ind
           {A : hSet}
           {Y : propositional_truncation A → UU}
           (Yprop : ∏ (a : propositional_truncation A), isaprop (Y a))
           (f : ∏ (a : A), Y (trunc_inc a))
  : ∏ (a : propositional_truncation A), Y a
  := pr1 (pr2 (propositional_truncation_HIT A) (trunc_ind_disp_alg A Yprop f)).
