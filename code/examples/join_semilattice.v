(**
Here we define the category of join semilattices using the mechanism of algebras.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import syntax.hit.
Require Import syntax.hit_properties.
Require Import algebras.set_algebra.
Require Import existence.hit_existence.
Require Import displayed_algebras.displayed_algebra.
Require Import examples.free.

Open Scope cat.

Opaque HIT_exists hit_ind hit_ind_prop hit_rec.

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
Section KFinite.
  Variable (X : hSet).

  Local Definition kuratowski_free_HIT
    : set_algebra (free_signature semilattice_signature X)
    := free_algebra_help semilattice_signature X.

  Definition kuratowski_HIT
    : semilattice_cat
    := free_alg_to_alg _ kuratowski_free_HIT.

  (** Constructors *)
  Definition kuratowski
    : hSet
    := alg_carrier kuratowski_HIT.

  Definition k_empty
    : kuratowski
    := alg_operation kuratowski_HIT (inr tt).

  Definition k_singleton
    : X → kuratowski
    := free_algebra_inc semilattice_signature X.

  Definition k_union
    : kuratowski → kuratowski → kuratowski
    := λ x y, alg_operation kuratowski_HIT (inl (x ,, y)).

  Definition k_nl
    : ∏ (x : kuratowski), k_union k_empty x = x
    := alg_paths kuratowski_free_HIT nl.

  Definition k_nr
    : ∏ (x : kuratowski), k_union x k_empty = x
    := join_semilattice_nr kuratowski_HIT.

  Definition k_idem
    : ∏ (x : kuratowski), k_union x x = x
    := alg_paths kuratowski_free_HIT idem.

  Definition k_com
    : ∏ (x y : kuratowski), k_union x y = k_union y x
    := λ x y, alg_paths kuratowski_free_HIT com (x ,, y).

  Definition k_assoc
    : ∏ (x y z : kuratowski), k_union (k_union x y) z = k_union x (k_union y z)
    := λ x y z, alg_paths kuratowski_free_HIT assoc ((x ,, y) ,, z).

  (** Induction *)
  Section KInduction.
    Context {Y : kuratowski → UU}.
    Variable (Ye : Y k_empty)
             (Ys : ∏ (x : X), Y (k_singleton x))
             (Yu : ∏ (z₁ z₂ : kuratowski), Y z₁ → Y z₂ → Y (k_union z₁ z₂))
             (Ynl : ∏ (x : kuratowski) (y : Y x),
                     transportf Y (k_nl x) (Yu k_empty x Ye y)
                     =
                     y)
             (Yidem : ∏ (x : kuratowski) (y : Y x),
                      transportf Y (k_idem x) (Yu x x y y)
                      =
                      y)
             (Ycom : ∏ (x₁ x₂ : kuratowski) (y₁ : Y x₁) (y₂ : Y x₂),
                     transportf Y (k_com x₁ x₂) (Yu x₁ x₂ y₁ y₂)
                     =
                     Yu x₂ x₁ y₂ y₁)
             (Yassoc : ∏ (x₁ x₂ x₃ : kuratowski)
                         (y₁ : Y x₁) (y₂ : Y x₂) (y₃ : Y x₃),
                       transportf Y
                                  (k_assoc x₁ x₂ x₃)
                                  (Yu (k_union x₁ x₂) x₃ (Yu x₁ x₂ y₁ y₂) y₃)
                       =
                       Yu x₁ (k_union x₂ x₃) y₁ (Yu x₂ x₃ y₂ y₃))
             (Yset : ∏ (x : kuratowski), isaset (Y x)).

    Definition K_ind_disp_algebra
      : disp_algebra kuratowski_free_HIT.
    Proof.
      use mk_disp_algebra.
      - intros x.
        use hSetpair.
        + exact (Y x).
        + exact (Yset x).
      - intros x.
        induction x as [x | x].
        + exact (λ _, Ys x).
        + induction x as [x | x].
          * intros y.
            exact (Yu (pr1 x) (pr2 x) (pr1 y) (pr2 y)).
          * induction x.
            exact (λ _, Ye).
      - intros j.
        simpl.
        induction j.
        + exact Ynl.
        + exact Yidem.
        + exact (λ x y, Ycom (pr1 x) (pr2 x) (pr1 y) (pr2 y)).
        + exact (λ x y, Yassoc (pr11 x) (pr21 x) (pr2 x) (pr11 y) (pr21 y) (pr2 y)).
    Defined.

    Definition K_ind_help
      : disp_algebra_map K_ind_disp_algebra
      := pr2 (HIT_exists (free_signature semilattice_signature X)) K_ind_disp_algebra.
    
    Definition K_ind
      : ∏ (x : kuratowski), Y x
      := pr1 K_ind_help.

    Definition K_ind_e
      : K_ind k_empty = Ye.
    Proof.
      apply K_ind_help.
    Qed.

    Definition K_ind_s
      : ∏ (x : X), K_ind (k_singleton x) = Ys x.
    Proof.
      intro x.
      apply K_ind_help.
    Qed.

    Definition K_ind_u
      : ∏ (x₁ x₂ : kuratowski),
        K_ind (k_union x₁ x₂)
        =
        Yu x₁ x₂ (K_ind x₁) (K_ind x₂).
    Proof.
      intros x₁ x₂.
      apply K_ind_help.
    Qed.
  End KInduction.

  (** Induction on families of propositions *)
  Section KInductionProp.
    Context {Y : kuratowski → UU}.
    Variable (Ye : Y k_empty)
             (Ys : ∏ (x : X), Y (k_singleton x))
             (Yu : ∏ (z₁ z₂ : kuratowski), Y z₁ → Y z₂ → Y (k_union z₁ z₂))
             (Yprop : ∏ (x : kuratowski), isaprop (Y x)).

    Definition K_ind_prop
      : ∏ (x : kuratowski), Y x.
    Proof.
      use K_ind.
      - exact Ye.
      - exact Ys.
      - exact Yu.
      - intros ; apply Yprop.
      - intros ; apply Yprop.
      - intros ; apply Yprop.
      - intros ; apply Yprop.
      - intro x.
        apply isasetaprop.
        apply Yprop.
    Defined.
  End KInductionProp.

  (** Recursion *)
  Section KRecusion.
    Context {A : UU}.
    Variable (Ae : A)
             (As : X → A)
             (Au : A → A → A)
             (Anl : ∏ (a : A), Au Ae a = a)
             (Aidem : ∏ (a : A), Au a a = a)
             (Acom : ∏ (a₁ a₂ : A), Au a₁ a₂ = Au a₂ a₁)
             (Aassoc : ∏ (a₁ a₂ a₃ : A), Au (Au a₁ a₂) a₃ = Au a₁ (Au a₂ a₃))
             (Aset : isaset A).

    Definition K_rec_algebra
      : set_algebra (free_signature semilattice_signature X).
    Proof.
      use mk_algebra.
      - use hSetpair.
        + exact A.
        + exact Aset.
      - intros a ; cbn in a.
        induction a as [x | a].
        + exact (As x).
        + induction a as [a | a].
          * exact (Au (pr1 a) (pr2 a)).
          * exact Ae.
      - intros j.
        induction j.
        + exact Anl.
        + exact Aidem.
        + exact (λ x, Acom (pr1 x) (pr2 x)).
        + exact (λ x, Aassoc (pr11 x) (pr21 x) (pr2 x)).
    Defined.

    Definition K_rec_help
      : kuratowski_free_HIT --> K_rec_algebra
      := hit_rec _ K_rec_algebra.

    Definition K_rec
      : kuratowski → A
      := alg_map_carrier K_rec_help.

    Definition K_rec_e
      : K_rec k_empty = Ae.
    Proof.
      apply (eqtohomot (pr21 K_rec_help)).
    Qed.

    Definition K_rec_s
      : ∏ (x : X), K_rec (k_singleton x) = As x.
    Proof.
      intro x.
      apply (eqtohomot (pr21 K_rec_help)).
    Qed.

    Definition K_rec_u
      : ∏ (x₁ x₂ : kuratowski), K_rec (k_union x₁ x₂) = Au (K_rec x₁) (K_rec x₂).
    Proof.
      intros x₁ x₂.
      apply (eqtohomot (pr21 K_rec_help)).
    Qed.
  End KRecusion.
End KFinite.
