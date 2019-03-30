(**
Signature of integers modulo 2
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import algebras.set_algebra.

Open Scope cat.

(** We first define the signature. *)

(** Operations *)
Definition mod2_operations
  : poly_code
  := I + C unitset.

(** Labels of axioms *)
Inductive mod2_ax : Type :=
| mod2_paths : mod2_ax.

(** Arguments for each label *)
Definition mod2_arg
  : mod2_ax → poly_code
  := fun j => I.

(** Some convenient notation for the constructor terms. These represent the operations *)
Definition S
           {P : poly_code}
           (e : endpoint mod2_operations P I)
  : endpoint mod2_operations P I
  := comp (comp e (ι₁ _ _)) constr.

Definition Z
           {P : poly_code}
  : endpoint mod2_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₂ _ _)).
  apply c.
  exact tt.
Defined.

(** The left hand side of each equation *)
Definition mod2_lhs
  : ∏ (j : mod2_ax), endpoint mod2_operations (mod2_arg j) I
  := λ j, S(S(id_e _ I)).

(** The right hand side of each equation *)
Definition mod2_rhs
  : ∏ (j : mod2_ax), endpoint mod2_operations (mod2_arg j) I
  := λ j, id_e _ I.

(** The signature of the integers modulo 2 *)
Definition mod2_signature
  : hit_signature.
Proof.
  use tpair.
  - exact mod2_operations.
  - use tpair.
    + exact mod2_ax.
    + use tpair.
      * exact mod2_arg.
      * split.
        ** exact mod2_lhs.
        ** exact mod2_rhs.
Defined.