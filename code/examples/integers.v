(**
We define the integers as a HIT
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import syntax.hit.
Require Import syntax.hit_properties.
Require Import algebras.set_algebra.
Require Import existence.hit_existence.
Require Import examples.rings.
Require Import displayed_algebras.displayed_algebra.

Open Scope cat.

Opaque HIT_exists hit_ind hit_ind_prop hit_rec.

(** We first define the signature. *)

(** Operations *)
Definition Z_operations
  : poly_code
  := I (* suc *) + I (* pred *) + C unitset (* zero *).

(** Labels of group axioms *)
Inductive Z_ax : UU :=
| PS : Z_ax
| SP : Z_ax.

(** Arguments for each label *)
Definition Z_arg
  : Z_ax → poly_code
  := fun j =>
       match j with
       | PS => I
       | SP => I
       end.

(** Some convenient notation for the constructor terms. These represent the operations *)
Definition suc
           {P : poly_code}
           (e : endpoint Z_operations P I)
  : endpoint Z_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₁ _ _)).  
  refine (comp _ (ι₁ _ _)).
  exact e.
Defined.

Definition pred
           {P : poly_code}
           (e : endpoint Z_operations P I)
  : endpoint Z_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₁ _ _)).  
  refine (comp _ (ι₂ _ _)).
  exact e.
Defined.

Definition zero
           {P : poly_code}
  : endpoint Z_operations P I.
Proof.
  refine (comp _ constr).
  refine (comp _ (ι₂ _ _)).
  apply c.
  exact tt.
Defined.

(** The left hand side of each equation *)
Definition Z_lhs
  : ∏ (j : Z_ax), endpoint Z_operations (Z_arg j) I.
Proof.
  induction j ; cbn.
  - exact (pred(suc (id_e _ _))).
  - exact (suc(pred (id_e _ _))).
Defined.

(** The right hand side of each equation *)
Definition Z_rhs
  : ∏ (j : Z_ax), endpoint Z_operations (Z_arg j) I.
Proof.
  induction j ; cbn.
  - apply id_e.
  - apply id_e.
Defined.

(** The signature of Z as a HIT signature *)
Definition Z_signature
  : hit_signature.
Proof.
  use tpair.
  - exact Z_operations.
  - use tpair.
    + exact Z_ax.
    + use tpair.
      * exact Z_arg.
      * split.
        ** exact Z_lhs.
        ** exact Z_rhs.
Defined.

(** The integers as a HIT *)
Definition Z_HIT : HIT Z_signature
  := HIT_exists Z_signature.

Definition ℤ : hSet
  := alg_carrier Z_HIT.

Definition Sℤ : ℤ → ℤ
  := λ x, alg_operation Z_HIT (inl(inl x)).

Definition Pℤ : ℤ → ℤ
  := λ x, alg_operation Z_HIT (inl(inr x)).

Definition Zℤ : ℤ
  := alg_operation Z_HIT (inr tt).

Definition PSℤ
  : ∏ (x : ℤ), Pℤ (Sℤ x) = x
  := λ x, alg_paths Z_HIT PS x.

Definition SPℤ
  : ∏ (x : ℤ), Sℤ (Pℤ x) = x
  := λ x, alg_paths Z_HIT SP x.

(** Induction on ℤ *)
Definition Z_ind_disp_algebra
           {Y : ℤ → UU}
           (SY : ∏ (x : ℤ), Y x → Y(Sℤ x))
           (PY : ∏ (x : ℤ), Y x → Y(Pℤ x))
           (ZY : Y Zℤ)
           (PSY : ∏ (x : ℤ) (y : Y x), transportf Y (PSℤ x) (PY (Sℤ x) (SY x y)) = y)
           (SPY : ∏ (x : ℤ) (y : Y x), transportf Y (SPℤ x) (SY (Pℤ x) (PY x y)) = y)
           (Yset : ∏ (x : ℤ), isaset (Y x))
  : disp_algebra Z_HIT.
Proof.
  use make_disp_algebra.
  - intros x.
    use make_hSet.
    + exact (Y x).
    + exact (Yset x).
  - intros x.
    induction x as [x | x].
    + induction x as [x | x].
      * exact (SY x).
      * exact (PY x).
    + induction x.
      exact (λ _, ZY).
  - intros j x.
    induction j.
    + exact (PSY x).
    + exact (SPY x).
Defined.

Definition Z_ind_help
           {Y : ℤ → UU}
           (SY : ∏ (x : ℤ), Y x → Y(Sℤ x))
           (PY : ∏ (x : ℤ), Y x → Y(Pℤ x))
           (ZY : Y Zℤ)
           (PSY : ∏ (x : ℤ) (y : Y x), transportf Y (PSℤ x) (PY (Sℤ x) (SY x y)) = y)
           (SPY : ∏ (x : ℤ) (y : Y x), transportf Y (SPℤ x) (SY (Pℤ x) (PY x y)) = y)
           (Yset : ∏ (x : ℤ), isaset (Y x))
  : disp_algebra_map (Z_ind_disp_algebra SY PY ZY PSY SPY Yset)
  := pr2 Z_HIT (Z_ind_disp_algebra SY PY ZY PSY SPY Yset).

Definition Z_ind
           {Y : ℤ → UU}
           (SY : ∏ (x : ℤ), Y x → Y(Sℤ x))
           (PY : ∏ (x : ℤ), Y x → Y(Pℤ x))
           (ZY : Y Zℤ)
           (PSY : ∏ (x : ℤ) (y : Y x), transportf Y (PSℤ x) (PY (Sℤ x) (SY x y)) = y)
           (SPY : ∏ (x : ℤ) (y : Y x), transportf Y (SPℤ x) (SY (Pℤ x) (PY x y)) = y)
           (Yset : ∏ (x : ℤ), isaset (Y x))
  : ∏ (x : ℤ), Y x
  := pr1 (Z_ind_help SY PY ZY PSY SPY Yset).

Definition Z_ind_S
           {Y : ℤ → UU}
           (SY : ∏ (x : ℤ), Y x → Y(Sℤ x))
           (PY : ∏ (x : ℤ), Y x → Y(Pℤ x))
           (ZY : Y Zℤ)
           (PSY : ∏ (x : ℤ) (y : Y x), transportf Y (PSℤ x) (PY (Sℤ x) (SY x y)) = y)
           (SPY : ∏ (x : ℤ) (y : Y x), transportf Y (SPℤ x) (SY (Pℤ x) (PY x y)) = y)
           (Yset : ∏ (x : ℤ), isaset (Y x))
           (x : ℤ)
  : Z_ind SY PY ZY PSY SPY Yset (Sℤ x)
    =
    SY x (Z_ind SY PY ZY PSY SPY Yset x)
  := pr2 (Z_ind_help SY PY ZY PSY SPY Yset) (inl (inl x)).

Definition Z_ind_P
           {Y : ℤ → UU}
           (SY : ∏ (x : ℤ), Y x → Y(Sℤ x))
           (PY : ∏ (x : ℤ), Y x → Y(Pℤ x))
           (ZY : Y Zℤ)
           (PSY : ∏ (x : ℤ) (y : Y x), transportf Y (PSℤ x) (PY (Sℤ x) (SY x y)) = y)
           (SPY : ∏ (x : ℤ) (y : Y x), transportf Y (SPℤ x) (SY (Pℤ x) (PY x y)) = y)
           (Yset : ∏ (x : ℤ), isaset (Y x))
           (x : ℤ)
  : Z_ind SY PY ZY PSY SPY Yset (Pℤ x)
    =
    PY x (Z_ind SY PY ZY PSY SPY Yset x)
  := pr2 (Z_ind_help SY PY ZY PSY SPY Yset) (inl (inr x)).

Definition Z_ind_Z
           {Y : ℤ → UU}
           (SY : ∏ (x : ℤ), Y x → Y(Sℤ x))
           (PY : ∏ (x : ℤ), Y x → Y(Pℤ x))
           (ZY : Y Zℤ)
           (PSY : ∏ (x : ℤ) (y : Y x), transportf Y (PSℤ x) (PY (Sℤ x) (SY x y)) = y)
           (SPY : ∏ (x : ℤ) (y : Y x), transportf Y (SPℤ x) (SY (Pℤ x) (PY x y)) = y)
           (Yset : ∏ (x : ℤ), isaset (Y x))
  : Z_ind SY PY ZY PSY SPY Yset Zℤ
    =
    ZY
  := pr2 (Z_ind_help SY PY ZY PSY SPY Yset) (inr tt).

(** Induction on a family of propositions *)
Definition Z_ind_prop
           {Y : ℤ → UU}
           (SY : ∏ (x : ℤ), Y x → Y(Sℤ x))
           (PY : ∏ (x : ℤ), Y x → Y(Pℤ x))
           (ZY : Y Zℤ)
           (Yprop : ∏ (x : ℤ), isaprop (Y x))
  : ∏ (x : ℤ), Y x.
Proof.
  use Z_ind.
  - exact SY.
  - exact PY.
  - exact ZY.
  - intros ; apply Yprop.
  - intros ; apply Yprop.
  - intros.
    apply isasetaprop.
    apply Yprop.
Defined.
    
(** Recursion on ℤ *)
Definition Z_rec_alg
           {A : hSet}
           (SA : A → A)
           (PA : A → A)
           (ZA : A)
           (PSA : ∏ (x : A), PA (SA x) = x)
           (SPA : ∏ (x : A), SA (PA x) = x)
  : set_algebra Z_signature.
Proof.
  use make_algebra.
  - exact A.
  - intros x.
    induction x as [x | x].
    + induction x as [x | x].
      * exact (SA x).
      * exact (PA x).
    + exact ZA.
  - intros j x.
    induction j.
    + exact (PSA x).
    + exact (SPA x).
Defined.

Definition Z_rec_help
           {A : hSet}
           (SA : A → A)
           (PA : A → A)
           (ZA : A)
           (PSA : ∏ (x : A), PA (SA x) = x)
           (SPA : ∏ (x : A), SA (PA x) = x)
  : Z_HIT --> Z_rec_alg SA PA ZA PSA SPA
  := hit_rec Z_HIT (Z_rec_alg SA PA ZA PSA SPA).

Definition Z_rec
           {A : hSet}
           (SA : A → A)
           (PA : A → A)
           (ZA : A)
           (PSA : ∏ (x : A), PA (SA x) = x)
           (SPA : ∏ (x : A), SA (PA x) = x)
  : ℤ → A
  := alg_map_carrier (Z_rec_help SA PA ZA PSA SPA).

Definition Z_rec_S
           {A : hSet}
           (SA : A → A)
           (PA : A → A)
           (ZA : A)
           (PSA : ∏ (x : A), PA (SA x) = x)
           (SPA : ∏ (x : A), SA (PA x) = x)
           (x : ℤ)
  : Z_rec SA PA ZA PSA SPA (Sℤ x)
    =
    SA (Z_rec SA PA ZA PSA SPA x)
  := eqtohomot (pr21 (Z_rec_help SA PA ZA PSA SPA)) (inl(inl x)).

Definition Z_rec_P
           {A : hSet}
           (SA : A → A)
           (PA : A → A)
           (ZA : A)
           (PSA : ∏ (x : A), PA (SA x) = x)
           (SPA : ∏ (x : A), SA (PA x) = x)
           (x : ℤ)
  : Z_rec SA PA ZA PSA SPA (Pℤ x)
    =
    PA (Z_rec SA PA ZA PSA SPA x)
  := eqtohomot (pr21 (Z_rec_help SA PA ZA PSA SPA)) (inl(inr x)).

Definition Z_rec_Z
           {A : hSet}
           (SA : A → A)
           (PA : A → A)
           (ZA : A)
           (PSA : ∏ (x : A), PA (SA x) = x)
           (SPA : ∏ (x : A), SA (PA x) = x)
  : Z_rec SA PA ZA PSA SPA Zℤ
    =
    ZA
  := eqtohomot (pr21 (Z_rec_help SA PA ZA PSA SPA)) (inr tt).

(** One *)
Definition ℤ_one
  : ℤ
  := Sℤ Zℤ.

(** Addition on ℤ *)
Definition ℤ_plus
  : ℤ → ℤ → ℤ
  := λ x, Z_rec Sℤ Pℤ x PSℤ SPℤ.

(** Properties of addition *)
Definition Z_plus_xS
  : ∏ (x y : ℤ), ℤ_plus x (Sℤ y) = Sℤ (ℤ_plus x y).
Proof.
  intros x y ; unfold ℤ_plus.
  apply Z_rec_S.
Qed.

Definition Z_plus_Sx
  : ∏ (x y : ℤ), ℤ_plus (Sℤ x) y = Sℤ (ℤ_plus x y).
Proof.
  intros x ; unfold ℤ_plus.
  use Z_ind_prop.
  - intros z IH ; cbn.
    rewrite !Z_rec_S.
    rewrite IH.
    reflexivity.
  - intros z IH ; cbn.
    rewrite !Z_rec_P.
    rewrite IH.
    exact (PSℤ _ @ !(SPℤ _)).
  - cbn.
    rewrite !Z_rec_Z.
    reflexivity.
  - intro ; apply ℤ.
Qed.

Definition Z_plus_xP
  : ∏ (x y : ℤ), ℤ_plus x (Pℤ y) = Pℤ (ℤ_plus x y).
Proof.
  intros x y ; unfold ℤ_plus.
  apply Z_rec_P.
Qed.

Definition Z_plus_Px
  : ∏ (x y : ℤ), ℤ_plus (Pℤ x) y = Pℤ (ℤ_plus x y).
Proof.
  intros x ; unfold ℤ_plus.
  use Z_ind_prop.
  - intros z IH ; cbn.
    rewrite !Z_rec_S.
    rewrite IH.
    exact (SPℤ _ @ !(PSℤ _)).
  - intros z IH ; cbn.
    rewrite !Z_rec_P.
    rewrite IH.
    reflexivity.
  - cbn.
    rewrite !Z_rec_Z.
    reflexivity.
  - intro ; apply ℤ.
Qed.

Definition Z_plus_x0
  : ∏ (x : ℤ), ℤ_plus x Zℤ = x.
Proof.
  intros x.
  exact (Z_rec_Z _ _ _ _ _).
Qed.

Definition Z_plus_0x
  : ∏ (x : ℤ), ℤ_plus Zℤ x = x.
Proof.
  use Z_ind_prop.
  - intros x IH ; cbn in *.
    rewrite Z_plus_xS, IH.
    reflexivity.
  - intros x IH ; cbn in *.
    rewrite Z_plus_xP, IH.
    reflexivity.
  - cbn.
    rewrite Z_plus_x0.
    reflexivity.
  - intro ; apply ℤ.
Qed.

Definition Z_plus_com
  : ∏ (x y : ℤ), ℤ_plus x y = ℤ_plus y x.
Proof.
  intros x.
  use Z_ind_prop.
  - intros y IH ; cbn in *.
    rewrite Z_plus_xS, Z_plus_Sx.
    rewrite IH.
    reflexivity.
  - intros y IH ; cbn in *.
    rewrite Z_plus_xP, Z_plus_Px.
    rewrite IH.
    reflexivity.
  - cbn.
    rewrite Z_plus_0x, Z_plus_x0.
    reflexivity.
  - intro ; apply ℤ.
Qed.

Definition Z_plus_assoc
  : ∏ (x y z : ℤ), ℤ_plus (ℤ_plus x y) z = ℤ_plus x (ℤ_plus y z).
Proof.
  intros x y.
  use Z_ind_prop.
  - intros z IH ; cbn in *.
    rewrite !Z_plus_xS.
    rewrite IH.
    reflexivity.
  - intros z IH ; cbn in *.
    rewrite !Z_plus_xP.
    rewrite IH.
    reflexivity.
  - cbn.
    rewrite !Z_plus_x0.
    reflexivity.
  - intro ; apply ℤ.
Qed.

(** Inverse of addition *)
Definition ℤ_minus
  : ℤ → ℤ
  := Z_rec Pℤ Sℤ Zℤ SPℤ PSℤ.

Definition Z_minus_S
  : ∏ (x : ℤ), ℤ_minus (Sℤ x) = Pℤ (ℤ_minus x).
Proof.
  exact (Z_rec_S _ _ _ _ _).
Qed.

Definition Z_minus_P
  : ∏ (x : ℤ), ℤ_minus (Pℤ x) = Sℤ (ℤ_minus x).
Proof.
  exact (Z_rec_P _ _ _ _ _).
Qed.

Definition Z_minus_Z
  : ℤ_minus Zℤ = Zℤ.
Proof.
  apply Z_rec_Z.
Qed.

Definition Z_plus_minus_x
  : ∏ (x : ℤ), ℤ_plus (ℤ_minus x) x = Zℤ.
Proof.
  use Z_ind_prop.
  - intros x IH ; cbn in *.
    rewrite (Z_minus_S x).
    rewrite Z_plus_Px, Z_plus_xS.
    rewrite IH.
    apply PSℤ.
  - intros x IH ; cbn in *.
    rewrite (Z_minus_P x).
    rewrite Z_plus_Sx, Z_plus_xP.
    rewrite IH.
    apply SPℤ.
  - cbn.
    rewrite Z_minus_Z.
    rewrite Z_plus_x0.
    reflexivity.
  - intro ; apply ℤ.
Qed.

Definition Z_plus_x_minus
  : ∏ (x : ℤ), ℤ_plus x (ℤ_minus x) = Zℤ.
Proof.
  intro x.
  rewrite Z_plus_com.
  apply Z_plus_minus_x.
Qed.

Definition Z_minus_minus
  : ∏ (x : ℤ), ℤ_minus (ℤ_minus x) = x.
Proof.
  use Z_ind_prop.
  - intros z IH ; cbn in *.
    exact (maponpaths ℤ_minus (Z_minus_S z) @ Z_minus_P _ @ maponpaths Sℤ IH).
  - intros z IH ; cbn in *.
    exact (maponpaths ℤ_minus (Z_minus_P z) @ Z_minus_S _ @ maponpaths Pℤ IH).
  - cbn.
    exact (maponpaths ℤ_minus Z_minus_Z @ Z_minus_Z).
  - intro ; apply ℤ.
Qed.

Definition Z_plus_minus
  : ∏ (x y : ℤ), ℤ_minus (ℤ_plus x y) = ℤ_plus (ℤ_minus x) (ℤ_minus y).
Proof.
  intros x.
  use Z_ind_prop.
  - intros z IH ; cbn in *.
    refine (maponpaths ℤ_minus (Z_plus_xS x z) @ Z_minus_S _ @ _).
    rewrite IH.
    exact (!(Z_plus_xP _ _) @ !(maponpaths (ℤ_plus (ℤ_minus x)) (Z_minus_S z))).
  - intros z IH ; cbn in *.
    refine (maponpaths ℤ_minus (Z_plus_xP x z) @ Z_minus_P _ @ _).
    rewrite IH.
    exact (!(Z_plus_xS _ _) @ !(maponpaths (ℤ_plus (ℤ_minus x)) (Z_minus_P z))).
  - cbn.
    refine (maponpaths ℤ_minus (Z_plus_x0 x) @ _).
    refine (_ @ maponpaths (ℤ_plus _) (!Z_minus_Z)).
    exact (!(Z_plus_x0 _)).
  - intro ; apply ℤ.
Qed.

(** The minus operation on integers *) 
Definition ℤ_min
  : ℤ → ℤ → ℤ
  := λ x y, ℤ_plus x (ℤ_minus y).

Definition Z_min_x
  : ∏ (x : ℤ), ℤ_min x x = Zℤ.
Proof.
  intro x ; unfold ℤ_min.
  apply Z_plus_x_minus.
Qed.

(** Multiplication on integers *)
Definition Z_mult_help_1
  : ∏ (x z : ℤ), ℤ_plus (ℤ_plus x z) (ℤ_minus x) = z.
Proof.
  intros x z ; cbn ; unfold ℤ_min.
  rewrite (Z_plus_com x z).
  rewrite Z_plus_assoc.
  rewrite (Z_plus_x_minus x).
  apply Z_plus_x0.
Qed.

Definition Z_mult_help_2
  : ∏ (x z : ℤ), ℤ_plus x (ℤ_plus z (ℤ_minus x)) = z.
Proof.
  intros x z ; cbn ; unfold ℤ_min.
  rewrite <- Z_plus_assoc.
  rewrite (Z_plus_com x z).
  rewrite Z_plus_assoc.
  rewrite (Z_plus_x_minus x).
  apply Z_plus_x0.
Qed.

Definition ℤ_mult
  : ℤ → ℤ → ℤ
  := λ x, Z_rec (ℤ_plus x) (λ z, ℤ_min z x) Zℤ (Z_mult_help_1 x) (Z_mult_help_2 x).

(** Properties of multiplication *)
Definition Z_mult_xS
  : ∏ (x y : ℤ), ℤ_mult x (Sℤ y) = ℤ_plus x (ℤ_mult x y).
Proof.
  intro.
  exact (Z_rec_S _ _ _ _ _).
Qed.

Definition Z_mult_xP
  : ∏ (x y : ℤ), ℤ_mult x (Pℤ y) = ℤ_min (ℤ_mult x y) x.
Proof.
  intro.
  exact (Z_rec_P _ _ _ _ _).
Qed.

Definition Z_mult_x0
  : ∏ (x : ℤ), ℤ_mult x Zℤ = Zℤ.
Proof.
  intro.
  exact (Z_rec_Z _ _ _ _ _).
Qed.

Definition Z_mult_Sx
  : ∏ (x y : ℤ), ℤ_mult (Sℤ x) y = ℤ_plus y (ℤ_mult x y).
Proof.
  intro x.
  use Z_ind_prop.
  - intros z IH ; cbn in *.
    rewrite (Z_mult_xS x z), (Z_mult_xS (Sℤ x) z).
    rewrite IH.
    refine (Z_plus_Sx x _ @ _ @ !(Z_plus_Sx z _)).
    apply maponpaths.
    refine (!(Z_plus_assoc _ _ _) @ _ @ Z_plus_assoc _ _ _).
    rewrite (Z_plus_com x z).
    reflexivity.
  - intros z IH ; cbn in *.
    rewrite (Z_mult_xP x z), (Z_mult_xP (Sℤ x) z).
    unfold ℤ_min.
    rewrite IH.
    rewrite (Z_minus_S x).
    refine (Z_plus_xP _ (ℤ_minus x) @ _ @ !(Z_plus_Px z _)).
    rewrite Z_plus_assoc.
    reflexivity.
  - cbn.
    refine (Z_mult_x0 _ @ !_ @ maponpaths _ (!(Z_mult_x0 _))).
    apply Z_plus_0x.
  - intro ; apply ℤ.
Qed.

Definition Z_mult_Px
  : ∏ (x y : ℤ), ℤ_mult (Pℤ x) y = ℤ_min (ℤ_mult x y) y.
Proof.
  intro x.
  use Z_ind_prop.
  - intros z IH ; cbn in *.
    refine (Z_mult_xS _ z @ _ @ maponpaths (λ q, ℤ_min q _) (!(Z_mult_xS x z))).
    rewrite IH ; unfold ℤ_min.
    rewrite (Z_minus_S z).
    refine (Z_plus_Px x _ @ !_ @ !(Z_plus_xP _ (ℤ_minus z))).
    apply maponpaths.
    apply Z_plus_assoc.
  - intros z IH ; cbn in *.
    refine (Z_mult_xP _ z @ _ @ maponpaths (λ q, ℤ_min q _) (!(Z_mult_xP x z))).
    rewrite IH ; unfold ℤ_min.
    rewrite (Z_minus_P x), (Z_minus_P z).
    refine (Z_plus_xS _ _ @ _ @ !(Z_plus_xS _ _)).
    apply maponpaths.
    refine (Z_plus_assoc _ _ _ @ _).    
    rewrite (Z_plus_com (ℤ_minus z) (ℤ_minus x)).
    rewrite <- Z_plus_assoc.
    reflexivity.
  - cbn.
    rewrite !Z_mult_x0.
    apply (!(Z_min_x Zℤ)).
  - intro ; apply ℤ.
Qed.

Definition Z_mult_0x
  : ∏ (x : ℤ), ℤ_mult Zℤ x = Zℤ.
Proof.
  use Z_ind_prop.
  - intros z IH ; cbn in *.
    rewrite Z_mult_xS.
    rewrite IH.
    apply Z_plus_0x.
  - intros z IH ; cbn in *.
    rewrite Z_mult_xP.
    rewrite IH.
    apply Z_min_x.
  - cbn.
    apply Z_mult_x0.
  - intro ; apply ℤ.
Qed.

Definition Z_mult_1x
  : ∏ (x : ℤ), ℤ_mult ℤ_one x = x.
Proof.
  intro x ; unfold ℤ_one.
  rewrite Z_mult_Sx.
  refine (maponpaths (ℤ_plus x) (Z_mult_0x x) @ _).
  apply Z_plus_x0.
Qed.

Definition Z_mult_com
  : ∏ (x y : ℤ), ℤ_mult x y = ℤ_mult y x.
Proof.
  intros x.
  use Z_ind_prop.
  - intros z IH ; cbn in *.
    refine (Z_mult_xS x z @ _ @ !(Z_mult_Sx z x)).
    rewrite IH.
    reflexivity.
  - intros z IH ; cbn in *.
    refine (Z_mult_xP x z @ _ @ !(Z_mult_Px z x)).
    rewrite IH.
    reflexivity.
  - exact (Z_mult_x0 x @ !(Z_mult_0x x)).
  - intro ; apply ℤ.
Qed.

Definition Z_mult_minus
  : ∏ (x y : ℤ), ℤ_mult x (ℤ_minus y) = ℤ_minus (ℤ_mult x y).
Proof.
  intro x.
  use Z_ind_prop.
  - intros z IH ; cbn in *.
    refine (maponpaths (ℤ_mult x) (Z_minus_S z) @ _).
    refine (Z_mult_xP x _ @ _) ; unfold ℤ_min.
    rewrite IH.
    refine (_ @ maponpaths ℤ_minus (!(Z_mult_xS x z))).
    refine (_ @ !(Z_plus_minus _ _)).
    apply Z_plus_com.
  - intros z IH ; cbn in *.
    refine (maponpaths (ℤ_mult x) (Z_minus_P z) @ _).
    refine (Z_mult_xS x _ @ _).
    rewrite IH.
    refine (_ @ maponpaths ℤ_minus (!(Z_mult_xP x z))) ; unfold ℤ_min.
    refine (_ @ !(Z_plus_minus _ _)).
    refine (Z_plus_com _ _ @ _).
    apply maponpaths.
    exact (!(Z_minus_minus x)).
  - cbn.
    rewrite Z_minus_Z.
    rewrite Z_mult_x0.
    rewrite Z_minus_Z.
    reflexivity.
  - intro ; apply ℤ.
Qed.

Definition Z_distr
  : ∏ (x y z : ℤ), ℤ_mult x (ℤ_plus y z) = ℤ_plus (ℤ_mult x y) (ℤ_mult x z).
Proof.
  intros x y.
  use Z_ind_prop.
  - intros z IH ; cbn in *.
    refine (maponpaths (ℤ_mult x) (Z_plus_xS y z) @ _).
    refine (Z_mult_xS x _ @ _).
    rewrite IH.
    refine (_ @ maponpaths (ℤ_plus _) (!(Z_mult_xS x z))).
    refine (_ @ Z_plus_assoc _ _ _).
    refine (!_ @ maponpaths (λ z, ℤ_plus z _) (Z_plus_com x _)).
    apply Z_plus_assoc.
  - intros z IH ; cbn in *.
    refine (maponpaths (ℤ_mult x) (Z_plus_xP y z) @ _).
    refine (Z_mult_xP x _ @ _).
    rewrite IH.
    refine (_ @ maponpaths (ℤ_plus _) (!(Z_mult_xP x z))) ; unfold ℤ_min.
    refine (_ @ Z_plus_assoc _ _ _).
    reflexivity.
  - cbn.
    refine (_ @ _).
    {
      apply maponpaths.
      apply Z_plus_x0.
    }
    refine (!(_ @ _)).
    {
      apply maponpaths.
      apply Z_mult_x0.
    }
    apply Z_plus_x0.
  - intro ; apply ℤ.
Qed.

Definition Z_distr_min
  : ∏ (x y z : ℤ), ℤ_mult x (ℤ_min y z) = ℤ_min (ℤ_mult x y) (ℤ_mult x z).
Proof.
  intros x y z ; unfold ℤ_min.
  rewrite Z_distr.
  apply maponpaths.
  apply Z_mult_minus.
Qed.

Definition Z_mult_assoc
  : ∏ (x y z : ℤ), ℤ_mult (ℤ_mult x y) z = ℤ_mult x (ℤ_mult y z).
Proof.
  intros x y.
  use Z_ind_prop.
  - intros z IH ; cbn in *.
    refine (Z_mult_xS _ z @ _ @ maponpaths (ℤ_mult x) (!(Z_mult_xS y z))).
    rewrite IH.
    exact (!(Z_distr x y (ℤ_mult y z))).
  - intros z IH ; cbn in *.
    refine (Z_mult_xP _ z @ _ @ maponpaths (ℤ_mult x) (!(Z_mult_xP y z))).
    rewrite IH.
    exact (!(Z_distr_min _ _ _)).
  - cbn.
    exact (Z_mult_x0 _ @ !(Z_mult_x0 x) @ maponpaths (ℤ_mult x) (!(Z_mult_x0 y))).
  - intro ; apply ℤ.
Qed.

Definition Z_mult_x1
  : ∏ (x : ℤ), ℤ_mult x ℤ_one = x.
Proof.
  intro x.
  rewrite Z_mult_com.
  apply Z_mult_1x.
Qed.

(** The integers form a ring *)
Definition ℤ_ring
  : ring_cat.
Proof.
  use mk_ring.
  - exact ℤ.
  - exact ℤ_plus.
  - exact ℤ_mult.
  - exact ℤ_minus.
  - exact Zℤ.
  - exact ℤ_one.
  - exact Z_plus_assoc.
  - exact Z_plus_0x.
  - exact Z_plus_minus_x.
  - exact Z_plus_com.
  - exact Z_mult_assoc.
  - exact Z_mult_1x.
  - exact Z_mult_com.
  - exact Z_distr.
Defined.

(** Integers form initial ring *)
Definition ℤ_map_unique
           {R : ring_cat}
           (f g : ℤ_ring --> R)
  : f = g.
Proof.
  use algebra_map_eq.
  use Z_ind_prop.
  - intros z IH ; cbn ; cbn in IH.
    assert (Sℤ z = ℤ_plus z ℤ_one) as ->.
    {
      exact (maponpaths Sℤ (!(Z_plus_x0 _)) @ !(Z_plus_xS z Zℤ)).      
    }
    rewrite (ring_map_plus f), (ring_map_plus g).
    rewrite !IH.
    apply maponpaths.
    exact (ring_map_one f @ !(ring_map_one g)).
  - intros z IH ; cbn ; cbn in IH.
    assert (Pℤ z = ℤ_plus z (ℤ_minus ℤ_one)) as ->.
    {
      refine (!(maponpaths (ℤ_plus z) (Z_minus_S Zℤ) @ _)).
      refine (Z_plus_xP z _ @ _).
      apply maponpaths.
      refine (maponpaths (ℤ_plus z) Z_minus_Z @ _).
      exact (Z_plus_x0 _).
    }
    rewrite (ring_map_plus f), (ring_map_plus g).
    rewrite (ring_map_minus f), (ring_map_minus g).
    rewrite !IH.
    do 2 apply maponpaths.
    exact (ring_map_one f @ !(ring_map_one g)).
  - cbn.
    exact (ring_map_zero f @ !(ring_map_zero g)).
  - intro ; apply (alg_carrier R).
Qed.

Section ZMapExistence.
  Variable (R : ring_cat).

  Local Definition ℤ_to_ring_map
    : ℤ → alg_carrier R.
  Proof.
    use Z_rec.
    - exact (λ x, ring_plus R x (ring_one R)).
    - exact (λ x, ring_plus R x (ring_minus R (ring_one R))).
    - exact (ring_zero R).
    - intro x ; cbn.
      rewrite ring_plus_assoc.
      rewrite ring_plus_min.
      apply ring_plus_zero.
    - intro x ; cbn.
      rewrite ring_plus_assoc.
      rewrite ring_min_plus.
      apply ring_plus_zero.
  Defined.

  Local Definition Z_to_ring_map_S
        (x : ℤ)
    : ℤ_to_ring_map (Sℤ x)
      =
      ring_plus R (ℤ_to_ring_map x) (ring_one R).
  Proof.
    exact (Z_rec_S _ _ _ _ _ x).
  Qed.

  Local Definition Z_to_ring_map_P
        (x : ℤ)
    : ℤ_to_ring_map (Pℤ x)
      =
      ring_plus R (ℤ_to_ring_map x) (ring_minus R (ring_one R)).
  Proof.
    exact (Z_rec_P _ _ _ _ _ x).
  Qed.

  Local Definition Z_to_ring_map_Z
    : ℤ_to_ring_map Zℤ = ring_zero R.
  Proof.
    exact (Z_rec_Z _ _ _ _ _).
  Qed.

  Local Definition Z_to_ring_map_plus
    : ∏ (x y : ℤ),
      ℤ_to_ring_map (ℤ_plus x y)
      =
      ring_plus R (ℤ_to_ring_map x) (ℤ_to_ring_map y).
  Proof.
    intro x.
    use Z_ind_prop.
    - intros z IH ; cbn in *.
      rewrite Z_plus_xS.
      rewrite !Z_to_ring_map_S.
      rewrite IH.
      rewrite ring_plus_assoc.
      reflexivity.
    - intros z IH ; cbn in *.
      rewrite Z_plus_xP.
      rewrite !Z_to_ring_map_P.
      rewrite IH.
      rewrite ring_plus_assoc.
      reflexivity.
    - cbn.
      rewrite Z_plus_x0.
      rewrite Z_to_ring_map_Z.
      rewrite ring_plus_zero.
      reflexivity.
    - intro ; apply (alg_carrier R).
  Qed.

  Local Definition Z_to_ring_map_minus
    : ∏ (x : ℤ),
      ℤ_to_ring_map (ℤ_minus x)
      =
      ring_minus R (ℤ_to_ring_map x).
  Proof.
    use Z_ind_prop.
    - intros z IH ; cbn in *.
      rewrite Z_minus_S.
      rewrite Z_to_ring_map_P, Z_to_ring_map_S.
      rewrite IH.
      rewrite ring_inv_plus.
      reflexivity.
    - intros z IH ; cbn in *.
      rewrite Z_minus_P.
      rewrite Z_to_ring_map_S, Z_to_ring_map_P.
      rewrite IH.
      rewrite ring_inv_plus.
      rewrite ring_minus_minus.
      reflexivity.
    - cbn.
      rewrite Z_minus_Z.
      rewrite !Z_to_ring_map_Z.
      rewrite ring_minus_zero.
      reflexivity.
    - intro ; apply (alg_carrier R).
  Qed.

  Local Definition Z_to_ring_map_mult
    : ∏ (x y : ℤ),
      ℤ_to_ring_map (ℤ_mult x y)
      =
      ring_mult R (ℤ_to_ring_map x) (ℤ_to_ring_map y).
  Proof.
    intro x.
    use Z_ind_prop.
    - intros z IH ; cbn in *.
      rewrite Z_mult_xS.
      rewrite Z_to_ring_map_plus.
      rewrite Z_to_ring_map_S.
      rewrite IH.
      rewrite ring_left_distr.
      rewrite ring_mult_one.
      rewrite ring_plus_com.
      reflexivity.
    - intros z IH ; cbn in *.
      rewrite Z_mult_xP ; unfold ℤ_min.
      rewrite Z_to_ring_map_plus.
      rewrite Z_to_ring_map_P.
      rewrite IH.
      rewrite ring_left_distr.
      apply maponpaths.
      rewrite ring_mult_minus.
      rewrite Z_to_ring_map_minus.
      rewrite ring_mult_one.
      reflexivity.
    - cbn.
      rewrite Z_mult_x0.
      rewrite !Z_to_ring_map_Z.
      rewrite ring_mult_zero.
      reflexivity.
    - intro ; apply (alg_carrier R).
  Qed.

  Local Definition Z_to_ring_map_one
    : ℤ_to_ring_map ℤ_one = ring_one R.
  Proof.
    unfold ℤ_one.
    rewrite Z_to_ring_map_S.
    rewrite Z_to_ring_map_Z.
    apply ring_zero_plus.
  Qed.

  Definition ℤ_to_ring
    : ℤ_ring --> R.
  Proof.
    use mk_ring_map.
    - exact ℤ_to_ring_map.
    - exact Z_to_ring_map_plus.
    - exact Z_to_ring_map_mult.
    - exact Z_to_ring_map_one.
  Defined.
End ZMapExistence.

Definition ℤ_isInitial
  : isInitial _ ℤ_ring.
Proof.
  use make_isInitial.
  intro R.
  apply iscontraprop1.
  - apply invproofirrelevance.
    exact ℤ_map_unique.
  - exact (ℤ_to_ring R).
Defined.
