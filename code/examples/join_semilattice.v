(**
Here we define the category of join semilattices using the mechanism of algebras.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import algebras.set_algebra.
Require Import examples.free.

Open Scope cat.

(** We first define the signature. *)

(** Operations *)
Definition semilattice_operations
  : poly_code
  := (I * I) (* join *)
     + C unitset (* empty *).

(** Labels of group axioms *)
Inductive semilattice_ax :=
| nl : semilattice_ax
| idem : semilattice_ax
| com : semilattice_ax
| assoc : semilattice_ax.

(** Arguments for each label *)
Definition semilattice_arg
  : semilattice_ax → poly_code
  := fun j =>
       match j with
       | nl => I
       | idem => I
       | com => I * I
       | assoc => I * I * I
       end.

(** Some convenient notation for the constructor terms. These represent the operations.
    For the signature, we call the operation `join`.
*)
Definition join_e
           {P : poly_code}
           (e₁ e₂ : endpoint semilattice_operations P I)
  : endpoint semilattice_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₁ _ _)).
  exact (pair e₁ e₂).
Defined.

Definition empty_e
           {P : poly_code}
  : endpoint semilattice_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₂ _ _)).
  apply c.
  exact tt.
Defined.

(** The left hand side of each equation *)
Definition semilattice_lhs
  : ∏ (j : semilattice_ax), endpoint semilattice_operations (semilattice_arg j) I.
Proof.
  induction j ; cbn.
  - refine (join_e _ _). (* nl *)
    + exact empty_e.
    + exact (id_e _ _).
  - refine (join_e _ _). (* idem *)
    + exact (id_e _ _).
    + exact (id_e _ _).
  - refine (join_e _ _). (* com *)
    + exact (π₁ _ _).
    + exact (π₂ _ _).
  - refine (join_e (join_e _ _) _). (* assoc *)
    + exact (comp (π₁ _ _) (π₁ _ _)).
    + exact (comp (π₁ _ _) (π₂ _ _)).
    + exact (π₂ _ _).
Defined.

(** The right hand side of each equation *)
Definition semilattice_rhs
  : ∏ (j : semilattice_ax), endpoint semilattice_operations (semilattice_arg j) I.
Proof.
  induction j ; cbn.
  - exact (id_e _ _). (* nl *)
  - exact (id_e _ _). (* idem *)
  - refine (join_e _ _). (* com *)
    + exact (π₂ _ _).
    + exact (π₁ _ _).
  - refine (join_e _ (join_e _ _)). (* assoc *)
    + exact (comp (π₁ _ _) (π₁ _ _)).
    + exact (comp (π₁ _ _) (π₂ _ _)).
    + exact (π₂ _ _).
Defined.

(** The signature of ring as a HIT signature *)
Definition semilattice_signature
  : hit_signature.
Proof.
  use tpair.
  - exact semilattice_operations.
  - use tpair.
    + exact semilattice_ax.
    + use tpair.
      * exact semilattice_arg.
      * split.
        ** exact semilattice_lhs.
        ** exact semilattice_rhs.
Defined.

(** The interpretation of ring in set *)
Definition semilattice_cat
  : univalent_category
  := set_algebra semilattice_signature.

(** Projections of a ring *)
Section JoinSemiLatticeProjections.
  Variable (S : semilattice_cat).

  Definition join_semilattice_carrier : hSet
    := pr11 S.

  Definition join
    : join_semilattice_carrier → join_semilattice_carrier → join_semilattice_carrier
    := λ x₁ x₂, pr21 S (inl (x₁ ,, x₂)).

  Local Notation "x₁ ∪ x₂" := (join x₁ x₂) (at level 45).

  Definition empty
    : join_semilattice_carrier
    := pr21 S (inr tt).

  Local Notation "'0'" := empty.

  Definition join_semilattice_nl
    : ∏ (x : join_semilattice_carrier), 0 ∪ x = x
    := λ x, pr2 S nl x.

  Definition join_semilattice_idem
    : ∏ (x : join_semilattice_carrier), x ∪ x = x
    := λ x, pr2 S idem x.  

  Definition join_semilattice_com
    : ∏ (x y : join_semilattice_carrier), x ∪ y = y ∪ x
    := λ x y, pr2 S com (x ,, y).

  Definition join_semilattice_assoc
    : ∏ (x y z : join_semilattice_carrier), (x ∪ y) ∪ z = x ∪ (y ∪ z)
    := λ x y z, pr2 S assoc ((x ,, y) ,, z).

  Definition join_semilattice_nr
    : ∏ (x : join_semilattice_carrier), x ∪ 0 = x
    := λ x, join_semilattice_com x 0 @ join_semilattice_nl x.
End JoinSemiLatticeProjections.

(** Builder for semilattices *)
Definition mk_semilattice
           {S : hSet}
           (e : S)
           (j : S → S → S)
           (j_nl : ∏ (x : S), j e x = x)
           (j_idem : ∏ (x : S), j x x = x)
           (j_com : ∏ (x y : S), j x y = j y x)
           (j_assoc : ∏ (x y z : S), j (j x y) z = j x (j y z))
  : semilattice_cat.
Proof.
  simple refine ((S ,, _) ,, _).
  - cbn.
    intros x.
    induction x as [x | x].
    + exact (j (pr1 x) (pr2 x)).
    + exact e.
  - intros k.
    induction k.
    + exact j_nl.
    + exact j_idem.
    + exact (λ z, j_com (pr1 z) (pr2 z)).
    + exact (λ z, j_assoc (pr11 z) (pr21 z) (pr2 z)).
Defined.

(** Kuratowski finite sets *)
Definition K
           (X : hSet)
  : semilattice_cat
  := free_algebra semilattice_signature X.
