(**
Here we define the category of rings using the mechanism of algebras.
Note: rings are commutative and always have `0` and `1`.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import algebras.set_algebra.

Open Scope cat.

(** We first define the signature. *)

(** Operations *)
Definition ring_operations
  : poly_code
  := (I * I) (* plus *)
     + (I * I) (* mult *)
     + I (* minus *) 
     + C unitset (* zero *)
     + C unitset (* one *).

(** Labels of group axioms *)
Inductive ring_ax :=
| p_assoc : ring_ax
| p_unit : ring_ax
| p_inv : ring_ax
| p_com : ring_ax
| m_assoc : ring_ax
| m_unit : ring_ax
| m_com : ring_ax
| distr : ring_ax.

(** Arguments for each label *)
Definition ring_arg
  : ring_ax → poly_code
  := fun j =>
       match j with
       | p_assoc => I * I * I 
       | p_unit => I
       | p_inv => I
       | p_com => I * I
       | m_assoc => I * I * I
       | m_unit => I
       | m_com => I * I
       | distr => I * I * I
       end.

(** Some convenient notation for the constructor terms. These represent the operations *)
Definition plus
           {P : poly_code}
           (e₁ e₂ : endpoint ring_operations P I)
  : endpoint ring_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₁ _ _)).
  refine (comp _ (ι₁ _ _)).
  refine (comp _ (ι₁ _ _)).
  refine (comp _ (ι₁ _ _)).
  exact (pair e₁ e₂).
Defined.

Definition mult
           {P : poly_code}
           (e₁ e₂ : endpoint ring_operations P I)
  : endpoint ring_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₁ _ _)).
  refine (comp _ (ι₁ _ _)).
  refine (comp _ (ι₁ _ _)).
  refine (comp _ (ι₂ _ _)).  
  exact (pair e₁ e₂).
Defined.

Definition minus
           {P : poly_code}
           (e : endpoint ring_operations P I)
  : endpoint ring_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₁ _ _)).
  refine (comp _ (ι₁ _ _)).
  refine (comp _ (ι₂ _ _)).
  exact e.
Defined.

Definition zero_el
           {P : poly_code}
  : endpoint ring_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₁ _ _)).
  refine (comp _ (ι₂ _ _)).
  apply c.
  exact tt.
Defined.

Definition one_el
           {P : poly_code}
  : endpoint ring_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₂ _ _)).
  apply c.
  exact tt.
Defined.

(** The left hand side of each equation *)
Definition ring_lhs
  : ∏ (j : ring_ax), endpoint ring_operations (ring_arg j) I.
Proof.
  induction j ; cbn.
  - refine (plus (plus _ _) _). (* plus assoc *)
    + exact (comp (π₁ _ _) (π₁ _ _)).
    + exact (comp (π₁ _ _) (π₂ _ _)).
    + exact (π₂ _ _).
  - refine (plus _ _). (* plus zero *)
    + apply zero_el.
    + apply id_e.
  - refine (plus _ _). (* plus minus *)
    + apply minus.
      apply id_e.
    + apply id_e.
  - refine (plus _ _). (* plus com *)
    + exact (π₁ _ _).
    + exact (π₂ _ _).
  - refine (mult (mult _ _) _). (* mult assoc *)
    + exact (comp (π₁ _ _) (π₁ _ _)).
    + exact (comp (π₁ _ _) (π₂ _ _)).
    + exact (π₂ _ _).
  - refine (mult _ _). (* mult one *)
    + apply one_el.
    + apply id_e.
  - refine (mult _ _). (* mult com *)
    + exact (π₁ _ _).
    + exact (π₂ _ _).
  - refine (mult _ _). (* distr *)
    + refine (comp _ _).
      * exact (π₁ _ _).
      * exact (π₁ _ _).
    + refine (plus _ _).
      * refine (comp _ _).
        ** exact (π₁ _ _).
        ** exact (π₂ _ _).
      * exact (π₂ _ _).
Defined.

(** The right hand side of each equation *)
Definition ring_rhs
  : ∏ (j : ring_ax), endpoint ring_operations (ring_arg j) I.
Proof.
  induction j ; cbn.
  - refine (plus _ (plus _ _)). (* plus assoc *)
    + exact (comp (π₁ _ _) (π₁ _ _)).
    + exact (comp (π₁ _ _) (π₂ _ _)).
    + exact (π₂ _ _).
  - apply id_e. (* plus zero *)
  - apply zero_el. (* plus minus *)
  - refine (plus _ _). (* plus com *)
    + exact (π₂ _ _).
    + exact (π₁ _ _).
  - refine (mult _ (mult _ _)). (* mult assoc *)
    + exact (comp (π₁ _ _) (π₁ _ _)).
    + exact (comp (π₁ _ _) (π₂ _ _)).
    + exact (π₂ _ _).
  - apply id_e. (* mult one *)
  - refine (mult _ _). (* mult com *)
    + exact (π₂ _ _).
    + exact (π₁ _ _).
  - refine (plus _ _). (* distr *)
    + refine (mult _ _).
      * refine (comp _ _).
        ** exact (π₁ _ _).
        ** exact (π₁ _ _).
      * refine (comp _ _).
        ** exact (π₁ _ _).
        ** exact (π₂ _ _).
    + refine (mult _ _).
      * refine (comp _ _).
        ** exact (π₁ _ _).
        ** exact (π₁ _ _).
      * exact (π₂ _ _).
Defined.

(** The signature of ring as a HIT signature *)
Definition ring_signature
  : hit_signature.
Proof.
  use tpair.
  - exact ring_operations.
  - use tpair.
    + exact ring_ax.
    + use tpair.
      * exact ring_arg.
      * split.
        ** exact ring_lhs.
        ** exact ring_rhs.
Defined.

(** The interpretation of ring in set *)
Definition ring_cat
  : univalent_category
  := set_algebra ring_signature.

(** Projections of a ring *)
Section RingProjections.
  Variable (R : ring_cat).

  Definition ring_carrier : hSet
    := pr11 R.

  Definition ring_plus
    : ring_carrier → ring_carrier → ring_carrier
    := λ x₁ x₂, pr21 R (inl (inl (inl (inl (x₁ ,, x₂))))).

  Local Notation "x₁ + x₂" := (ring_plus x₁ x₂).

  Definition ring_mult
    : ring_carrier → ring_carrier → ring_carrier
    := λ x₁ x₂, pr21 R (inl (inl (inl (inr (x₁ ,, x₂))))).

  Local Notation "x₁ * x₂" := (ring_mult x₁ x₂).

  Definition ring_minus
    : ring_carrier → ring_carrier
    := λ x, pr21 R (inl (inl (inr x))).

  Local Notation "- x" := (ring_minus x).

  Definition ring_zero
    : ring_carrier
    := pr21 R (inl (inr tt)).

  Local Notation "'0'" := ring_zero.

  Definition ring_one
    : ring_carrier
    := pr21 R (inr tt).

  Local Notation "'1'" := ring_one.

  Definition ring_plus_assoc
    : ∏ (x₁ x₂ x₃ : ring_carrier), (x₁ + x₂) + x₃ = x₁ + (x₂ + x₃)
    := λ x₁ x₂ x₃, pr2 R p_assoc ((x₁ ,, x₂) ,, x₃).

  Definition ring_zero_plus
    : ∏ (x : ring_carrier), 0 + x = x
    := λ x, pr2 R p_unit x.

  Definition ring_min_plus
    : ∏ (x : ring_carrier), (- x) + x = 0
    := λ x, pr2 R p_inv x.

  Definition ring_plus_com
    : ∏ (x y : ring_carrier), x + y = y + x
    := λ x y, pr2 R p_com (x ,, y).

  Definition ring_plus_zero
    : ∏ (x : ring_carrier), x + 0 = x
    := λ x, ring_plus_com x 0 @ ring_zero_plus x.

  Definition ring_plus_min
    : ∏ (x : ring_carrier), x + (- x) = 0
    := λ x, ring_plus_com x (- x) @ ring_min_plus x.

  Definition ring_mult_assoc
    : ∏ (x₁ x₂ x₃ : ring_carrier), (x₁ * x₂) * x₃ = x₁ * (x₂ * x₃)
    := λ x₁ x₂ x₃, pr2 R m_assoc ((x₁ ,, x₂) ,, x₃).

  Definition ring_one_mult
    : ∏ (x : ring_carrier), 1 * x = x
    := λ x, pr2 R m_unit x.

  Definition ring_mult_com
    : ∏ (x y : ring_carrier), x * y = y * x
    := λ x y, pr2 R m_com (x ,, y).

  Definition ring_mult_one
    : ∏ (x : ring_carrier), x * 1 = x
    := λ x, ring_mult_com x 1 @ ring_one_mult x.

  Definition ring_left_distr
    : ∏ (x₁ x₂ x₃ : ring_carrier), x₁ * (x₂ + x₃) = (x₁ * x₂) + (x₁ * x₃)
    := λ x₁ x₂ x₃, pr2 R distr ((x₁ ,, x₂) ,, x₃).

  Definition ring_right_distr
    : ∏ (x₁ x₂ x₃ : ring_carrier), (x₂ + x₃) * x₁ = (x₂ * x₁) + (x₃ * x₁).
  Proof.
    intros x₁ x₂ x₃.
    rewrite ring_mult_com.
    rewrite ring_left_distr.
    rewrite !(ring_mult_com _ x₁).
    reflexivity.
  Qed.
End RingProjections.

(** Builder for rings *)
Definition mk_ring
           (R : hSet)
           (plus : R → R → R)
           (mult : R → R → R)
           (min : R → R)
           (z : R)
           (o : R)
           (plus_assoc : ∏ (x₁ x₂ x₃ : R),
                         plus (plus x₁ x₂) x₃ = plus x₁ (plus x₂ x₃))
           (zero_plus : ∏ (x : R), plus z x = x)
           (plus_min : ∏ (x : R), plus (min x) x = z)
           (plus_com : ∏ (x y : R), plus x y = plus y x)
           (mult_assoc : ∏ (x₁ x₂ x₃ : R),
                         mult (mult x₁ x₂) x₃ = mult x₁ (mult x₂ x₃))
           (mult_one : ∏ (x : R), mult o x = x)
           (mult_com : ∏ (x y : R), mult x y = mult y x)
           (distr : ∏ (x y z : R), mult x (plus y z) = plus (mult x y) (mult x z))
  : ring_cat.
Proof.
  simple refine ((R ,, _) ,, _).
  - cbn.
    intros x.
    induction x as [x | x].
    + induction x as [x | x].
      * induction x as [x | x].
        ** induction x as [x | x].
           *** exact (plus (pr1 x) (pr2 x)).
           *** exact (mult (pr1 x) (pr2 x)).
        ** exact (min x).
      * exact z.
    +  exact o.
  - intros j.
    induction j.
    + exact (λ x, plus_assoc (pr11 x) (pr21 x) (pr2 x)).
    + exact zero_plus.
    + exact plus_min.
    + exact (λ x, plus_com (pr1 x) (pr2 x)).
    + exact (λ x, mult_assoc (pr11 x) (pr21 x) (pr2 x)).
    + exact mult_one.
    + exact (λ x, mult_com (pr1 x) (pr2 x)).
    + exact (λ x, distr (pr11 x) (pr21 x) (pr2 x)).
Defined.

(** Some laws for rings *)
Section Laws.
  Context {Ring : ring_cat}.

  Local Notation "'R'" := (alg_carrier Ring).
  Local Notation "x + y" := (ring_plus Ring x y).
  Local Notation "x * y" := (ring_mult Ring x y).
  Local Notation "- x" := (ring_minus Ring x).
  Local Notation "'0'" := (ring_zero Ring).
  Local Notation "'1'" := (ring_one Ring).

  Definition ring_cancel_plus_left
    : ∏ {x y : R} (z : R), z + x = z + y → x = y.
  Proof.
    intros x y z H.
    refine (_ @ maponpaths (λ r, (- z) + r) H @ _).
    - rewrite <- ring_plus_assoc.
      rewrite ring_min_plus.
      rewrite ring_zero_plus.
      reflexivity.
    - rewrite <- ring_plus_assoc.
      rewrite ring_min_plus.
      rewrite ring_zero_plus.
      reflexivity.
  Qed.

  Definition ring_cancel_plus_right
    : ∏ {x y : R} ( z : R), x + z = y + z → x = y.
  Proof.
    intros x y z H.
    refine (_ @ maponpaths (λ r, r + (- z)) H @ _).
    - rewrite ring_plus_assoc.
      rewrite ring_plus_min.
      rewrite ring_plus_zero.
      reflexivity.
    - rewrite ring_plus_assoc.
      rewrite ring_plus_min.
      rewrite ring_plus_zero.
      reflexivity.
  Qed.      

  Definition ring_minus_eq
    : ∏ (x y : R), x + y = 0 → x = - y.
  Proof.
    intros x y H.
    apply (ring_cancel_plus_right y).
    rewrite H.
    rewrite ring_min_plus.
    reflexivity.
  Qed.

  Definition ring_inverse_unique'
    : ∏ (x : R) {y z : R}, x + y = 0 → x + z = 0 → y = z.
  Proof.
    intros x y z H₁ H₂.
    apply (ring_cancel_plus_left x).
    exact (H₁ @ !H₂).
  Qed.

  Definition ring_inverse_unique
    : ∏ {x y : R}, x + y = 0 → -x = y.
  Proof.
    intros x y H.
    symmetry.
    apply (ring_inverse_unique' x).
    - exact H.
    - apply ring_plus_min.
  Qed.

  Definition ring_mult_zero
    : ∏ (x : R), x * 0 = 0.
  Proof.
    intro x.
    apply (ring_cancel_plus_right (x * 0)).
    rewrite ring_zero_plus.
    rewrite <- ring_left_distr.
    rewrite ring_zero_plus.
    reflexivity.
  Qed.
  
  Definition ring_zero_mult
    : ∏ (x : R), 0 * x = 0.
  Proof.
    intro x.
    rewrite ring_mult_com.
    apply ring_mult_zero.
  Qed.
  
  Definition ring_mult_minus
    : ∏ (x y : R), x * (- y) = -(x * y).
  Proof.
    intros x y.
    apply (ring_inverse_unique' (x * y)).
    - rewrite <- ring_left_distr.
      rewrite ring_plus_min.
      apply ring_mult_zero.
    - apply ring_plus_min.
  Qed.

  Definition ring_minus_zero
    : - 0 = 0.
  Proof.
    apply ring_inverse_unique.
    apply ring_plus_zero.
  Qed.

  Definition ring_minus_minus
    : ∏ (x : R), -(- x) = x.
  Proof.
    intro x.
    apply ring_inverse_unique.
    apply ring_min_plus.
  Qed.

  Definition ring_inv_plus
    : ∏ (x y : R), -(x + y) = (-x) + (-y).
  Proof.
    intros x y.
    apply ring_inverse_unique.
    rewrite (ring_plus_com _ x y).
    rewrite ring_plus_assoc.
    refine (_ @ _).
    {
      apply maponpaths.
      rewrite <- ring_plus_assoc.
      rewrite ring_plus_min.
      apply ring_zero_plus.
    }
    apply ring_plus_min.
  Qed.    
End Laws.

(** Builder for ring homomorphisms *)
Section BuildRingMap.
  Context {R₁ R₂ : ring_cat}.
  Variable (f : alg_carrier R₁ → alg_carrier R₂)
           (f_p : ∏ (x₁ x₂ : alg_carrier R₁),
                  f (ring_plus R₁ x₁ x₂)
                  =
                  ring_plus R₂ (f x₁) (f x₂))
           (f_m : ∏ (x₁ x₂ : alg_carrier R₁),
                  f (ring_mult R₁ x₁ x₂)
                  =
                  ring_mult R₂ (f x₁) (f x₂))
           (f_o : f (ring_one R₁) = ring_one R₂).

  Local Definition f_z
    : f (ring_zero R₁) = ring_zero R₂.
  Proof.
    apply (ring_cancel_plus_right (f (ring_zero R₁))).
    rewrite ring_zero_plus.
    rewrite <- f_p.
    exact (maponpaths f (ring_plus_zero _ _)).
  Qed.

  Local Definition f_minus
    : ∏ (x : alg_carrier R₁), f (ring_minus R₁ x) = ring_minus R₂ (f x).
  Proof.
    intro x.
    apply ring_minus_eq.
    rewrite <- f_p.
    refine (_ @ f_z).
    apply maponpaths.
    apply ring_min_plus.
  Qed.

  Definition mk_ring_map
    : R₁ --> R₂.
  Proof.
    use mk_algebra_map.
    - exact f.
    - intros x.
      induction x as [x | x].
      + induction x as [x | x].
        * induction x as [x | x].
          ** induction x as [x | x].
             *** apply f_p.
             *** apply f_m.
          ** exact (f_minus x).
        * induction x.
          exact f_z.
      + induction x.
        exact f_o.
  Defined.
End BuildRingMap.

(** Laws of ring homomorphism *)
Section RingMapProjections.
  Context {R₁ R₂ : ring_cat}.
  Variable (f : R₁ --> R₂).

  Definition ring_map_plus
    : ∏ (x y : alg_carrier R₁),
      alg_map_carrier f (ring_plus R₁ x y)
      =
      ring_plus R₂ (alg_map_carrier f x) (alg_map_carrier f y)
    := λ x y, eqtohomot (pr21 f) (inl (inl (inl (inl (x ,, y))))).

  Definition ring_map_mult
    : ∏ (x y : alg_carrier R₁),
      alg_map_carrier f (ring_mult R₁ x y)
      =
      ring_mult R₂ (alg_map_carrier f x) (alg_map_carrier f y)
    := λ x y, eqtohomot (pr21 f) (inl (inl (inl (inr (x ,, y))))).

  Definition ring_map_minus
    : ∏ (x : alg_carrier R₁),
      alg_map_carrier f (ring_minus R₁ x)
      =
      ring_minus R₂ (alg_map_carrier f x)
    := λ x, eqtohomot (pr21 f) (inl (inl (inr x))).

  Definition ring_map_zero
    : alg_map_carrier f (ring_zero R₁)
      =
      ring_zero R₂
    := eqtohomot (pr21 f) (inl (inr tt)).

  Definition ring_map_one
    : alg_map_carrier f (ring_one R₁)
      =
      ring_one R₂
    := eqtohomot (pr21 f) (inr tt).
End RingMapProjections.
