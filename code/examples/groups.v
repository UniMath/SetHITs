(**
Here we define the category of groups using the mechanism of algebras.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import algebras.set_algebra.

Open Scope cat.

(** We first define the signature. *)

(** Operations *)
Definition group_operations
  : poly_code
  := (I * I) + I + C unitset.

(** Labels of group axioms *)
Inductive group_ax :=
| assoc : group_ax
| unit_l : group_ax
| unit_r : group_ax
| inv_l : group_ax
| inv_r : group_ax.

(** Arguments for each label *)
Definition group_arg
  : group_ax → poly_code
  := fun j =>
       match j with
       | assoc => I * I * I
       | unit_l => I
       | unit_r => I
       | inv_l => I
       | inv_r => I
       end.

(** Some convenient notation for the constructor terms. These represent the operations *)
Definition mult
           {P : poly_code}
           (e₁ e₂ : endpoint group_operations P I)
  : endpoint group_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₁ _ _)).
  refine (comp _ (ι₁ _ _)).
  exact (pair e₁ e₂).
Defined.

Definition inverse
           {P : poly_code}
           (e : endpoint group_operations P I)
  : endpoint group_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₁ _ _)).
  refine (comp _ (ι₂ _ _)).
  exact e.
Defined.

Definition unit_el
           {P : poly_code}
  : endpoint group_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₂ _ _)).
  apply c.
  exact tt.
Defined.

(** The left hand side of each equation *)
Definition group_lhs
  : ∏ (j : group_ax), endpoint group_operations (group_arg j) I.
Proof.
  induction j ; cbn.
  - refine (mult (mult _ _) _). (* assoc *)
    + exact (comp (π₁ _ _) (π₁ _ _)).
    + exact (comp (π₁ _ _) (π₂ _ _)).
    + exact (π₂ _ _).
  - refine (mult _ _). (* unit_l *)
    + apply unit_el.
    + apply id_e.
  - refine (mult _ _). (* unit_r *)
    + apply id_e.
    + apply unit_el.
  - refine (mult _ _). (* inv_l *)
    + apply inverse.
      apply id_e.
    + apply id_e.
  - refine (mult _ _). (* inv_r *)
    + apply id_e.
    + apply inverse.
      apply id_e.
Defined.

(** The right hand side of each equation *)
Definition group_rhs
  : ∏ (j : group_ax), endpoint group_operations (group_arg j) I.
Proof.
  induction j ; cbn.
  - refine (mult _ (mult _ _)). (* assoc *)
    + exact (comp (π₁ _ _) (π₁ _ _)).
    + exact (comp (π₁ _ _) (π₂ _ _)).
    + exact (π₂ _ _).
  - apply id_e. (* unit_l *)
  - apply id_e. (* unit_r *)
  - apply unit_el. (* inv_l *)
  - apply unit_el. (* inv_r *)
Defined.

(** The signature of groups as a HIT signature *)
Definition group_signature
  : hit_signature.
Proof.
  use tpair.
  - exact group_operations.
  - use tpair.
    + exact group_ax.
    + use tpair.
      * exact group_arg.
      * split.
        ** exact group_lhs.
        ** exact group_rhs.
Defined.

(** The interpretation of groups in set *)
Definition group_cat
  : univalent_category
  := set_algebra group_signature.

(** Projections of a group *)
Section GroupProjections.
  Variable (G : group_cat).

  Definition group_carrier : hSet
    := pr11 G.

  Definition group_mult
    : group_carrier → group_carrier → group_carrier
    := λ g₁ g₂, pr21 G (inl(inl (g₁ ,, g₂))).

  Local Notation "g₁ · g₂" := (group_mult g₁ g₂).

  Definition group_inverse
    : group_carrier → group_carrier
    := λ g, pr21 G (inl(inr g)).

  Local Notation "g ^-1" := (group_inverse g).

  Definition group_unit
    : group_carrier
    := pr21 G (inr tt).

  Local Notation "'e'" := group_unit.

  Definition group_assoc
    : ∏ (g₁ g₂ g₃ : group_carrier), (g₁ · g₂) · g₃ = g₁ · (g₂ · g₃)
    := λ g₁ g₂ g₃, pr2 G assoc ((g₁ ,, g₂) ,, g₃).

  Definition group_unit_l
    : ∏ (g : group_carrier), e · g = g
    := λ g, pr2 G unit_l g.

  Definition group_unit_r
    : ∏ (g : group_carrier), g · e = g
    := λ g, pr2 G unit_r g.
  
  Definition group_inv_l
    : ∏ (g : group_carrier), (g ^-1) · g = e
    := λ g, pr2 G inv_l g.
  
  Definition group_inv_r
    : ∏ (g : group_carrier), g · (g ^-1) = e
    := λ g, pr2 G inv_r g.
End GroupProjections.

(** Builder for groups *)
Definition mk_group
           (G : hSet)
           (m : G → G → G)
           (i : G → G)
           (e : G)
           (assoc : ∏ (g₁ g₂ g₃ : G), m (m g₁ g₂) g₃ = m g₁ (m g₂ g₃))
           (e_l : ∏ (g : G), m e g = g)
           (e_r : ∏ (g : G), m g e = g)
           (i_l : ∏ (g : G), m (i g) g = e)
           (i_r : ∏ (g : G), m g (i g) = e)
  : group_cat.
Proof.
  simple refine ((G ,, _) ,, _).
  - cbn.
    intros x.
    induction x as [x | x].
    + induction x as [x | x].
      * exact (m (pr1 x) (pr2 x)).
      * exact (i x).
    + exact e.
  - intro j.
    destruct j.
    + exact (λ g, assoc (pr11 g) (pr21 g) (pr2 g)).
    + exact e_l.
    + exact e_r.
    + exact i_l.
    + exact i_r.
Defined.