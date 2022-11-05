(**
Here we define the category of monoids using the mechanism of algebras.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import syntax.hit_properties.
Require Import existence.hit_existence.
Require Import algebras.set_algebra.
Require Import examples.free.
Require Import UniMath.Combinatorics.Lists.

Open Scope cat.

Opaque HIT_exists.
Opaque hit_rec.

(** We first define the signature. *)

(** Operations *)
Definition monoid_operations
  : poly_code
  := (I * I) + C unitset.

(** Labels of monoid axioms *)
Inductive monoid_ax :=
| assoc : monoid_ax
| unit_l : monoid_ax
| unit_r : monoid_ax.

(** Arguments for each label *)
Definition monoid_arg
  : monoid_ax → poly_code
  := fun j =>
       match j with
       | assoc => I * I * I
       | unit_l => I
       | unit_r => I
       end.

(** Some convenient notation for the constructor terms. These represent the operations *)
Definition mult
           {P : poly_code}
           (e₁ e₂ : endpoint monoid_operations P I)
  : endpoint monoid_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₁ _ _)).
  exact (pair e₁ e₂).
Defined.

Definition unit_el
           {P : poly_code}
  : endpoint monoid_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₂ _ _)).
  apply c.
  exact tt.
Defined.

(** The left hand side of each equation *)
Definition monoid_lhs
  : ∏ (j : monoid_ax), endpoint monoid_operations (monoid_arg j) I.
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
Defined.

(** The right hand side of each equation *)
Definition monoid_rhs
  : ∏ (j : monoid_ax), endpoint monoid_operations (monoid_arg j) I.
Proof.
  induction j ; cbn.
  - refine (mult _ (mult _ _)). (* assoc *)
    + exact (comp (π₁ _ _) (π₁ _ _)).
    + exact (comp (π₁ _ _) (π₂ _ _)).
    + exact (π₂ _ _).
  - apply id_e. (* unit_l *)
  - apply id_e. (* unit_r *)
Defined.

(** The signature of monoid as a HIT signature *)
Definition monoid_signature
  : hit_signature.
Proof.
  use tpair.
  - exact monoid_operations.
  - use tpair.
    + exact monoid_ax.
    + use tpair.
      * exact monoid_arg.
      * split.
        ** exact monoid_lhs.
        ** exact monoid_rhs.
Defined.

(** The interpretation of monoid in set *)
Definition monoid_cat
  : univalent_category
  := set_algebra monoid_signature.

(** Projections of a group *)
Section MonoidProjections.
  Variable (M : monoid_cat).

  Definition monoid_carrier : hSet
    := pr11 M.

  Definition monoid_mult
    : monoid_carrier → monoid_carrier → monoid_carrier
    := λ m₁ m₂, pr21 M (inl (m₁ ,, m₂)).

  Local Notation "m₁ · m₂" := (monoid_mult m₁ m₂).

  Definition monoid_unit
    : monoid_carrier
    := pr21 M (inr tt).

  Local Notation "'e'" := monoid_unit.

  Definition monoid_assoc
    : ∏ (m₁ m₂ m₃ : monoid_carrier), (m₁ · m₂) · m₃ = m₁ · (m₂ · m₃)
    := λ m₁ m₂ m₃, pr2 M assoc ((m₁ ,, m₂) ,, m₃).

  Definition monoid_unit_l
    : ∏ (m : monoid_carrier), e · m = m
    := λ m, pr2 M unit_l m.

  Definition monoid_unit_r
    : ∏ (m : monoid_carrier), m · e = m
    := λ m, pr2 M unit_r m.
End MonoidProjections.

Notation "m₁ · m₂" := (monoid_mult _ m₁ m₂).

(** Builder for monoids *)
Definition mk_monoid
           (M : hSet)
           (m : M → M → M)
           (e : M)
           (assoc : ∏ (x₁ x₂ x₃ : M), m (m x₁ x₂) x₃ = m x₁ (m x₂ x₃))
           (e_l : ∏ (x : M), m e x = x)
           (e_r : ∏ (x : M), m x e = x)
  : monoid_cat.
Proof.
  simple refine ((M ,, _) ,, _).
  - cbn.
    intros x.
    induction x as [x | x].
    + exact (m (pr1 x) (pr2 x)).
    + exact e.
  - intro j.
    destruct j.
    + exact (λ g, assoc (pr11 g) (pr21 g) (pr2 g)).
    + exact e_l.
    + exact e_r.
Defined.

(** Free monoid *)
Definition free_monoid
           (X : hSet)
  : monoid_cat
  := free_algebra monoid_signature X.

(** Lists as a monoid *)
Definition list_free_monoid
           (X : hSet)
  : set_algebra (free_signature monoid_signature X).
Proof.
  use make_algebra.
  - use make_hSet.
    + exact (list X).
    + apply isofhlevellist.
      apply X.
  - intros j.
    induction j as [x | j].
    + exact (cons x nil).
    + induction j as [l | t].
      * exact (concatenate (pr1 l) (pr2 l)).
      * exact nil.
  - intros j x ; simpl in *.
    induction j as [ |  | ].
    + induction x as [x l₃].
      induction x as [l₁ l₂].
      exact (assoc_concatenate l₁ l₂ l₃).
    + apply nil_concatenate.
    + apply concatenate_nil.
Defined.

Definition list_monoid
           (X : hSet)
  : monoid_cat
  := free_alg_to_alg _ (list_free_monoid X).

(** We can map `list` to monoids *)
Definition list_to_monoid
           {X : hSet}
           (M : monoid_cat)
           (f : X → alg_carrier M)
  : alg_carrier (list_free_monoid X) → alg_carrier M.
Proof.
  use foldr.
  - exact (λ x m, monoid_mult M (f x) m).
  - exact (monoid_unit M).
Defined.

Definition list_to_monoid_cons
           {X : hSet}
           (M : monoid_cat)
           (f : X → alg_carrier M)
           (x : X)
           (l : list X)
  : list_to_monoid M f (cons x l) = monoid_mult M (f x) (list_to_monoid M f l).
Proof.
  reflexivity.
Qed.

Definition list_to_monoid_singleton
           {X : hSet}
           (M : monoid_cat)
           (f : X → alg_carrier M)
           (x : X)
  : list_to_monoid M f (cons x nil) = f x.
Proof.
  cbn.
  apply monoid_unit_r.
Qed.

Definition list_to_monoid_nil
           {X : hSet}
           (M : monoid_cat)
           (f : X → alg_carrier M)
  : list_to_monoid M f nil = monoid_unit M.
Proof.
  apply idpath.
Qed.

Definition list_to_monoid_concatenate
           {X : hSet}
           (M : monoid_cat)
           (f : X → alg_carrier M)
           (l₁ l₂ : list X)
  : list_to_monoid M f (concatenate l₁ l₂)
    =
    monoid_mult M (list_to_monoid M f l₁) (list_to_monoid M f l₂).
Proof.
  revert l₁.
  use list_ind.
  - simpl.
    rewrite list_to_monoid_nil.
    rewrite nil_concatenate.
    rewrite monoid_unit_l.
    reflexivity.
  - simpl ; intros x l₁ IH.
    rewrite concatenateStep.
    rewrite !list_to_monoid_cons.
    rewrite IH.
    rewrite monoid_assoc.
    reflexivity.
Qed.

Definition list_free_monoid_map
           {X : hSet}
           (M : set_algebra (free_signature monoid_signature X))
  : list_free_monoid X --> M.
Proof.
  pose (M' := free_alg_to_alg _ M).
  pose (f := (λ x, alg_operation M (inl x)) : X → alg_carrier M).
  use make_algebra_map.
  - exact (list_to_monoid M' f).
  - intros x.
    induction x as [x | l].
    + exact (list_to_monoid_singleton M' f x).
    + induction l as [l | ].
      * induction l as [l₁ l₂].
        exact (list_to_monoid_concatenate M' f l₁ l₂).
      * induction b.
        exact (list_to_monoid_nil M' f).
Defined.

Definition list_free_monoid_isInitial
           (X : hSet)
  : isInitial _ (list_free_monoid X).
Proof.           
  intros M.
  use tpair.
  - exact (list_free_monoid_map M).
  - intro f.
    use algebra_map_eq.
    use list_ind ; simpl.
    + apply (eqtohomot (pr21 f) (inr (inr tt))).
    + intros x l H.
      assert (cons x l = concatenate (cons x nil) l) as p.
      { reflexivity. }
      rewrite p ; clear p.
      pose (p := eqtohomot (pr21 f)).
      assert (alg_map_carrier f (concatenate (cons x nil) l)
              =
              monoid_mult (free_alg_to_alg _ M)
                          (alg_map_carrier f (cons x nil))
                          (alg_map_carrier f l)) as q.
      {
        apply (p (inr (inl (cons x nil ,, l)))).
      }
      refine (q @ _) ; clear q.
      refine (_ @ _).
      {
        apply maponpaths.
        exact H.
      }
      unfold alg_map_carrier ; simpl.
      rewrite list_to_monoid_concatenate.
      apply maponpaths_2.
      rewrite list_to_monoid_cons, list_to_monoid_nil.
      rewrite monoid_unit_r.
      exact (p (inl x)).
Qed.

Definition free_algebra_is_list_free_monoid
           (X : hSet)
  : free_algebra_help monoid_signature X = list_free_monoid X.
Proof.
  apply isotoid.
  {
    apply (set_algebra (free_signature monoid_signature X)).
  }
  apply initial_z_iso.
  - apply HIT_is_initial.
  - apply list_free_monoid_isInitial.
Defined.
  
Definition free_monoid_is_list_monoid
           (X : hSet)
  : free_monoid X = list_monoid X.
Proof.
  pose (free_algebra_is_list_free_monoid X) as p.
  exact (maponpaths (free_alg_to_alg monoid_signature) p).
Qed.
