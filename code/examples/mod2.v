(**
Signature of integers modulo 2
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import syntax.hit.
Require Import syntax.hit_properties.
Require Import algebras.set_algebra.
Require Import existence.hit_existence.
Require Import displayed_algebras.displayed_algebra.

Open Scope cat.
Opaque HIT_exists hit_ind hit_ind_prop hit_rec.

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

(** Integers modulo 2 *)
Definition mod2_HIT
  : HIT mod2_signature
  := HIT_exists mod2_signature.

Definition mod2
  : hSet
  := alg_carrier mod2_HIT.

Definition mod2_S
  : mod2 → mod2
  := λ x, alg_operation mod2_HIT (inl x).

Definition mod2_Z
  : mod2
  := alg_operation mod2_HIT (inr tt).

Definition mod2_mod
  : ∏ (n : mod2), mod2_S (mod2_S n) = n
  := alg_paths mod2_HIT mod2_paths.

(** Induction for integers modulo 2 *)
Section Mod2Ind.
  Context {Y : mod2 → UU}.
  Variable (YZ : Y mod2_Z)
           (YS : ∏ (x : mod2), Y x → Y (mod2_S x))
           (Ymod : ∏ (x : mod2) (y : Y x),
                   transportf Y (mod2_mod x) (YS (mod2_S x) (YS x y)) = y)
           (Yset : ∏ (x : mod2), isaset (Y x)).

  Definition mod2_ind_disp_alg
    : disp_algebra mod2_HIT.
  Proof.
    use make_disp_algebra.
    - intro x.
      use make_hSet.
      + exact (Y x).
      + exact (Yset x).
    - intros x.
      induction x as [x | x].
      + exact (YS x).
      + induction x.
        exact (λ _, YZ).
    - intros j.
      induction j.
      exact Ymod.
  Defined.

  Definition mod2_ind_help
    : disp_algebra_map mod2_ind_disp_alg
    := pr2 mod2_HIT mod2_ind_disp_alg.

  Definition mod2_ind
    : ∏ (x : mod2), Y x
    := pr1 mod2_ind_help.

  Definition mod2_ind_S
    : ∏ (x : mod2), mod2_ind (mod2_S x) = YS x (mod2_ind x).
  Proof.
    intro x.
    apply mod2_ind_help.
  Qed.

  Definition mod2_ind_Z
    : mod2_ind mod2_Z = YZ.
  Proof.
    apply mod2_ind_help.
  Qed.
End Mod2Ind.

(** Induction on propositions for integers modulo 2 *)
Section Mod2IndProp.
  Context {Y : mod2 → UU}.
  Variable (YZ : Y mod2_Z)
           (YS : ∏ (x : mod2), Y x → Y (mod2_S x))
           (Yprop : ∏ (x : mod2), isaprop (Y x)).

  Definition mod2_ind_prop
    : ∏ (x : mod2), Y x.
  Proof.
    use mod2_ind.
    - exact YZ.
    - exact YS.
    - intros x y ; apply Yprop.
    - intro.
      apply isasetaprop.
      apply Yprop.
  Defined.
End Mod2IndProp.

(** Recursion on integers modulo 2 *)
Section Mod2Rec.
  Context {Y : UU}.
  Variable (YZ : Y)
           (YS : Y → Y)
           (Ymod : ∏ (y : Y), YS(YS y) = y)
           (Yset : isaset Y).

  Definition mod2_rec_alg
    : set_algebra mod2_signature.
  Proof.
    use make_algebra.
    - use make_hSet.
      + exact Y.
      + exact Yset.
    - intros x.
      induction x as [x | x].
      + exact (YS x).
      + exact YZ.
    - intros j.
      induction j.
      exact Ymod.
  Defined.

  Definition mod2_rec_help
    : mod2_HIT --> mod2_rec_alg
    := hit_rec mod2_HIT mod2_rec_alg.

  Definition mod2_rec
    : mod2 → Y
    := alg_map_carrier mod2_rec_help.

  Definition mod2_rec_S
    : ∏ (x : mod2), mod2_rec (mod2_S x) = YS (mod2_rec x).
  Proof.
    intro x.
    apply (eqtohomot (pr21 mod2_rec_help)).
  Qed.

  Definition mod2_rec_Z
    : mod2_rec mod2_Z = YZ.
  Proof.
    apply (eqtohomot (pr21 mod2_rec_help)).
  Qed.
End Mod2Rec.

(** Integers modulo 2 are bool *)
Definition bool_to_mod2 : bool → mod2.
Proof.
  intro b.
  induction b.
  - exact (mod2_S mod2_Z).
  - exact mod2_Z.
Defined.

Definition bool_to_mod2_negb
  : ∏ (b : bool), bool_to_mod2 (negb b) = mod2_S (bool_to_mod2 b).
Proof.
  intro b.
  induction b ; cbn.
  - rewrite mod2_mod.
    reflexivity.
  - reflexivity.
Qed.

Lemma negbnegb : ∏ (b : bool), negb(negb b) = b.
Proof.
  induction b ; reflexivity.
Qed.

Definition mod2_to_bool : mod2 → bool
  := mod2_rec false negb negbnegb isasetbool.

Definition bool_to_mod2_to_bool
  : ∏ (b : bool), mod2_to_bool(bool_to_mod2 b) = b.
Proof.
  induction b ; cbn ; unfold mod2_to_bool.
  - rewrite mod2_rec_S, mod2_rec_Z.
    reflexivity.
  - rewrite mod2_rec_Z.
    reflexivity.
Qed.

Definition mod2_to_bool_to_mod2
  : ∏ (x : mod2), bool_to_mod2(mod2_to_bool x) = x.
Proof.
  use mod2_ind_prop.
  - cbn ; unfold mod2_to_bool.
    rewrite mod2_rec_Z.
    reflexivity.
  - cbn ; unfold mod2_to_bool.
    intros x IH.
    rewrite mod2_rec_S.
    rewrite bool_to_mod2_negb.
    rewrite IH.
    reflexivity.
  - intro ; apply mod2.
Qed.

Definition mod2_equiv_bool
  : mod2 ≃ bool.
Proof.
  use make_weq.
  - exact mod2_to_bool.
  - use gradth.
    + exact bool_to_mod2.
    + exact mod2_to_bool_to_mod2.
    + exact bool_to_mod2_to_bool.
Defined.

Definition mod2_is_bool
  : mod2 = boolset.
Proof.
  apply hSet_univalence.
  exact mod2_equiv_bool.
Defined.
