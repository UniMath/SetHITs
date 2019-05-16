(** Here we define signatures for HITs *)
Require Import UniMath.Foundations.All.
Require Import UniMath.MoreFoundations.All.

(**
Data type of polynomials.
These are used for both the point constructor and the arguments of the path constructors.
 *)
Inductive poly_code : UU :=
| C : hSet → poly_code
| I : poly_code
| plus : poly_code → poly_code → poly_code
| times : poly_code → poly_code → poly_code.

Notation "P + Q" := (plus P Q).
Notation "P * Q" := (times P Q).

(**
Type of endpoints
 *)
Inductive endpoint (A : poly_code) : poly_code → poly_code → UU :=
| id_e : forall (P : poly_code), endpoint A P P
| comp : forall (P Q R : poly_code), endpoint A P Q → endpoint A Q R → endpoint A P R
| ι₁ : forall (P Q : poly_code), endpoint A P (P + Q)
| ι₂ : forall (P Q : poly_code), endpoint A Q (P + Q)
| π₁ : forall (P Q : poly_code), endpoint A (P * Q) P
| π₂ : forall (P Q : poly_code), endpoint A (P * Q) Q
| pair : forall (P Q R : poly_code),
    endpoint A P Q -> endpoint A P R → endpoint A P (Q * R)
| c : forall (P : poly_code) (T : hSet), T → endpoint A P (C T)
| fmap : forall {X Y : hSet} (f : X → Y), endpoint A (C X) (C Y)
| constr : endpoint A A I.

Arguments id {_} _.
Arguments comp {A} {P} {Q} {R} _ _.
Arguments ι₁ {_} P Q.
Arguments ι₂ {_} P Q.
Arguments π₁ {_} P Q.
Arguments π₂ {_} P Q.
Arguments pair {A} {P} {Q} {R} _ _.
Arguments c {_} P {_} _.
Arguments fmap {_} {X Y} f.
Arguments constr {_}.

(**
The signature of a HIT
 *)
Definition hit_signature
  := ∑ (A : poly_code) (J : Type) (Q : J → poly_code),
     (∏ (j : J), endpoint A (Q j) I)
     ×
      ∏ (j : J), endpoint A (Q j) I.

(**
Projections of HIT signatures
 *)
Section SignatureProjections.
  Variable (Σ : hit_signature).

  Definition point_arg
    : poly_code
    := pr1 Σ.

  Definition path_index
    : UU
    := pr12 Σ.

  Definition path_arg
    : path_index → poly_code
    := pr122 Σ.

  Definition path_lhs
    : ∏ (j : path_index), endpoint point_arg (path_arg j) I
    := pr1 (pr222 Σ).

  Definition path_rhs
    : ∏ (j : path_index), endpoint point_arg (path_arg j) I
    := pr2 (pr222 Σ).
End SignatureProjections.
