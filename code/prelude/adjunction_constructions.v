(**
Here we define two constructions for adjunctions.
The first construction says how to get an adjunction between the category of algebras.
The second construction factors an adjunction through the full subcategory.
 *)
Require Import prelude.imports.

Open Scope cat.

(**
For this, we use a general method to construct functors between categories of algebras.
We need a natural transformation witnessing commutation.
 *)
Section AlgebraFunctor.
  Context {C D : category}.
  Variable (A₁ : C ⟶ C)
           (A₂ : D ⟶ D)
           (F : C ⟶ D)
           (n : F ∙ A₂ ⟹ A₁ ∙ F).

  Local Definition object_part
    : FunctorAlg A₁ (homset_property _) → FunctorAlg A₂ (homset_property _).
  Proof.
    intros X.
    use tpair.
    - exact (F (pr1 X)).
    - exact (#F (pr2 X) ∘ n (pr1 X)).
  Defined.

  Definition morphism_part
             {X Y : FunctorAlg A₁ (homset_property _)}
             (f : X --> Y)
    : D ⟦ F (pr1 X), F (pr1 Y) ⟧
    := #F (pr1 f).

  Definition morphism_part_is_morph
             {X Y : FunctorAlg A₁ (homset_property _)}
             (f : X --> Y)
    : is_algebra_mor A₂ (object_part X) (object_part Y) (morphism_part f).
  Proof.
    unfold is_algebra_mor, alg_map, morphism_part ; simpl.
    rewrite !assoc.
    symmetry.
    refine (_ @ _).
    {
      apply maponpaths_2.
      exact (pr2 n _ _ (pr1 f)).
    }
    rewrite <- !assoc.
    apply maponpaths ; simpl.
    rewrite <- !functor_comp.
    apply maponpaths.
    exact (!(pr2 f)).
  Qed.

  Definition algebra_functor
    : FunctorAlg A₁ (homset_property _) ⟶ FunctorAlg A₂ (homset_property _).
  Proof.
    use mk_functor.
    - use mk_functor_data.
      + exact object_part.
      + intros X Y f.
        use tpair ; simpl.
        * exact (morphism_part f).
        * exact (morphism_part_is_morph f).
  - split.
    + unfold functor_idax ; simpl.
      intros X.
      use subtypeEquality.
      {
        intro.
        unfold is_algebra_mor.
        apply D.
      }
      unfold morphism_part ; cbn.
      rewrite functor_id.
      reflexivity.
    + unfold functor_compax ; simpl.
      intros X Y Z f g.
      use subtypeEquality.
      {
        intro.
        unfold is_algebra_mor.
        apply D.
      }
      unfold morphism_part ; cbn.
      rewrite functor_comp.
      reflexivity.
  Defined.
End AlgebraFunctor.

(**
Here we give how a condition to show a natural transformation is an algebra morphism at each coodinate.
 *)
Section AlgebraNatTrans.
  Context {C D : category}
          {F G : C ⟶ D}.
  Variable (A₁ : C ⟶ C)
           (A₂ : D ⟶ D)
           (nF : F ∙ A₂ ⟹ A₁ ∙ F)
           (nG : G ∙ A₂ ⟹ A₁ ∙ G)
           (η : F ⟹ G)
           (H : ∏ (X : C), nF X · η (A₁ X) = # A₂ (η X) · nG X).

  Local Notation FA := (algebra_functor A₁ A₂ F nF).
  Local Notation GA := (algebra_functor A₁ A₂ G nG).

  Definition nat_trans_is_algebra_mor
             (X : FunctorAlg A₁ (homset_property _))
    : is_algebra_mor A₂ (FA X) (GA X) (η (pr1 X)).
  Proof.
    unfold is_algebra_mor, alg_map.
    simpl.
    rewrite <- !assoc.
    refine (_ @ _).
    {
      apply maponpaths.
      exact (pr2 η _ _ (pr2 X)).
    }
    rewrite !assoc.
    apply maponpaths_2.
    exact (H (pr1 X)).
  Qed.
End AlgebraNatTrans.

(**
Before we apply this construction to adjunctions, we need two lemmata.
 *)
Lemma nat_trans_is_algebra_mor_counit_help
      {C : category}
      {F : C ⟶ C}
      (A : C ⟶ C)
      (nF : F ∙ A ⟹ A ∙ F)
      (η : F ⟹ functor_identity _)
      (H : ∏ (X : C), nF X · η (A X) = # A (η X))
      (X : FunctorAlg A (homset_property _))
  : is_algebra_mor A (algebra_functor A A F nF X) X (η (pr1 X)).
Proof.
  refine (nat_trans_is_algebra_mor
          A
          A
          nF
          (nat_trans_comp _ _ _
                          (nat_trans_functor_id_left _)
                          (nat_trans_functor_id_right_inv _))
          η
          (λ X, H X @ !(id_right _) @ !(id_right _) @ !(assoc _ _ _))
          X
          @ _).
  simpl.
  apply maponpaths.
  rewrite !id_left.
  reflexivity.
Qed.

Lemma nat_trans_is_algebra_mor_unit_help
      {C : category}
      {F : C ⟶ C}
      (A : C ⟶ C)
      (nF : F ∙ A ⟹ A ∙ F)
      (η : functor_identity _ ⟹ F)
      (H : ∏ (X : C), η (A X) = # A (η X) · nF X)
      (X : FunctorAlg A (homset_property _))
  : is_algebra_mor A X (algebra_functor A A F nF X) (η (pr1 X)).
Proof.
  pose (nat_trans_is_algebra_mor
          A
          A
          (nat_trans_comp _ _ _
                          (nat_trans_functor_id_left _)
                          (nat_trans_functor_id_right_inv _))
          nF
          η
          (λ X, !(assoc _ _ _) @ id_left _ @ id_left _ @ H X)
          X) as p.
  refine (_ @ p).
  simpl.
  rewrite !id_left.
  reflexivity.
Qed.

(**
Now we apply the previous two constructions to adjunctions.
 *)
Section PreAlgebraAdjunction.
  Context {Std St : category}
          {L : Std ⟶ St}
          {R : St ⟶ Std}.
  Variable (A₁ : Std ⟶ Std)
           (A₂ : St ⟶ St)
           (adj : are_adjoints L R).

  Local Notation η := (unit_from_are_adjoints adj).
  Local Notation ε := (counit_from_are_adjoints adj).

  Variable (nL : L ∙ A₂ ⟹ A₁ ∙ L)
           (nR : R ∙ A₁ ⟹ A₂ ∙ R).

  Local Definition counit_θ : (R ∙ L) ∙ A₂ ⟹ A₂ ∙ (R ∙ L)
    := nat_trans_comp
         _ _ _
         (nat_trans_functor_assoc _ _ _)
         (nat_trans_comp
            _ _ _
            (pre_whisker R nL)
            (nat_trans_comp
               _ _ _
               (nat_trans_functor_assoc_inv _ _ _)
               (nat_trans_comp
                  _ _ _
                  (post_whisker nR L)
                  (nat_trans_functor_assoc _ _ _)))).

  Local Definition unit_θ : (L ∙ R) ∙ A₁ ⟹ A₁ ∙ (L ∙ R)
    := nat_trans_comp
         _ _ _
         (nat_trans_functor_assoc _ _ _)
         (nat_trans_comp
            _ _ _
            (pre_whisker L nR)
            (nat_trans_comp
               _ _ _
               (nat_trans_functor_assoc_inv _ _ _)
               (nat_trans_comp
                  _ _ _
                  (post_whisker nL R)
                  (nat_trans_functor_assoc _ _ _)))).
  
  Variable (H₁ : ∏ (X : St), nL (R X) · #L (nR X) · ε (A₂ X) = # A₂ (ε X))
           (H₂ : ∏ (X : Std), η (A₁ X) = # A₁ (η X) · nR (L X) · #R (nL X)).
  
  Definition lift_L := algebra_functor A₁ A₂ L nL.

  Definition lift_R := algebra_functor A₂ A₁ R nR.
  
  Definition nat_trans_is_algebra_mor_counit
             (X : FunctorAlg A₂ (homset_property _))
    : is_algebra_mor
        A₂
        (algebra_functor A₁ A₂ L nL (algebra_functor A₂ A₁ R nR X))
        X
        (ε (pr1 X)).
  Proof.
    refine (_ @ nat_trans_is_algebra_mor_counit_help A₂ counit_θ ε _ X).
    - simpl.
      rewrite functor_comp.
      rewrite !assoc.
      rewrite id_left, !id_right.
      reflexivity.
    - intros Z.
      simpl.
      rewrite !id_left, !id_right.
      exact (H₁ Z).
  Qed.

  Definition nat_trans_is_algebra_mor_unit
             (X : FunctorAlg A₁ (homset_property _))
    : is_algebra_mor
        A₁
        X
        (algebra_functor A₂ A₁ R nR (algebra_functor A₁ A₂ L nL X))
        (η (pr1 X)).
  Proof.
    refine (nat_trans_is_algebra_mor_unit_help A₁ unit_θ η _ X @ _).
    - intros Z ; simpl.
      rewrite !id_left, id_right, assoc.
      exact (H₂ Z).
    - simpl.
      rewrite functor_comp.
      rewrite !assoc.
      rewrite !id_right.
      reflexivity.
  Qed.

  Definition lift_η_data
    : nat_trans_data (functor_identity _) (lift_L ∙ lift_R).
  Proof.
    intros X.
    use tpair.
    - exact (η (pr1 X)).
    - exact (nat_trans_is_algebra_mor_unit X).
  Defined.

  Definition lift_η_is_nat_trans
    : is_nat_trans _ _ lift_η_data.
  Proof.
    intros X Y f.
    use subtypeEquality.
    {
      intro.
      apply Std.
    }
    apply η.
  Qed.

  Definition lift_η
    : functor_identity _ ⟹ lift_L ∙ lift_R.
  Proof.
    use mk_nat_trans.
    - exact lift_η_data.
    - exact lift_η_is_nat_trans.
  Defined.

  Definition lift_ε_data
    : nat_trans_data (lift_R ∙ lift_L) (functor_identity _).
  Proof.
    intros X.
    use tpair.
    - exact (ε (pr1 X)).
    - exact (nat_trans_is_algebra_mor_counit X).
  Defined.

  Definition lift_ε_is_nat_trans
    : is_nat_trans _ _ lift_ε_data.
  Proof.
    intros X Y f.
    use subtypeEquality.
    {
      intro.
      apply St.
    }
    apply ε.
  Qed.

  Definition lift_ε
    : lift_R ∙ lift_L ⟹ functor_identity _.
  Proof.
    use mk_nat_trans.
    - exact lift_ε_data.
    - exact lift_ε_is_nat_trans.
  Defined.

  Definition prealgebra_adjunction
    : are_adjoints lift_L lift_R.
  Proof.
    use mk_are_adjoints.
    - exact lift_η.
    - exact lift_ε.
    - split.
      + intro X.
        use subtypeEquality.
        {
          intro.
          apply homset_property.
        }
        exact (pr12 adj (pr1 X)).
      + intro X.
        use subtypeEquality.
        {
          intro.
          apply homset_property.
        }
        exact (pr22 adj (pr1 X)).
  Defined.
End PreAlgebraAdjunction.

(**
Next we show how to factor functors in full subcategories. We also show this gives rise to an adjunction when applied to an adjunction.
 *)
Definition factor_functor_data
           {C D : precategory}
           (PC : hsubtype C)
           (PD : hsubtype D)
           (F : C ⟶ D)
           (HF : ∏ (X : C), PC X → PD(F X))
  : functor_data (full_sub_precategory PC) (full_sub_precategory PD).
Proof.
  use mk_functor_data.
  - intros X.
    use tpair.
    + exact (F (pr1 X)).
    + exact (HF _ (pr2 X)).
  - exact (λ _ _ f, #F (pr1 f) ,, tt).
Defined.

Definition factor_functor_is_functor
           {C D : precategory}
           (PC : hsubtype C)
           (PD : hsubtype D)
           (F : C ⟶ D)
           (HF : ∏ (X : C), PC X → PD(F X))
  : is_functor (factor_functor_data PC PD F HF).
Proof.
  split.
  - intros X.
    use subtypeEquality.
    { intro ; apply isapropunit. }
    exact (functor_id F (pr1 X)).
  - intros X Y Z f g.
    use subtypeEquality.
    { intro ; apply isapropunit. }
    exact (functor_comp F (pr1 f) (pr1 g)).
Qed.

Definition factor_functor
           {C D : precategory}
           (PC : hsubtype C)
           (PD : hsubtype D)
           (F : C ⟶ D)
           (HF : ∏ (X : C), PC X → PD(F X))
  : full_sub_precategory PC ⟶ full_sub_precategory PD.
Proof.
  use mk_functor.
  - exact (factor_functor_data PC PD F HF).
  - exact (factor_functor_is_functor PC PD F HF).
Defined.

Section FactorFunctorAdjunction.
  Context {C D : precategory}
          {L : C ⟶ D}
          {R : D ⟶ C}.
  Variable (PC : hsubtype C)
           (PD : hsubtype D)
           (adj : are_adjoints L R).

  Variable (HL : ∏ (X : C), PC X → PD(L X))
           (HR : ∏ (X : D), PD X → PC(R X)).

  Local Notation η := (unit_from_are_adjoints adj).
  Local Notation ε := (counit_from_are_adjoints adj).

  Local Notation FL := (factor_functor PC PD L HL).
  Local Notation FR := (factor_functor PD PC R HR).

  Definition factor_η_data
    : nat_trans_data (functor_identity _) (FL ∙ FR)
    := λ X, η (pr1 X) ,, tt.

  Definition factor_η_is_nat_trans
    : is_nat_trans _ _ factor_η_data.
  Proof.
    intros X Y f.
    use subtypeEquality.
    {
      intro ; apply isapropunit.
    }
    apply η.
  Qed.

  Definition factor_η
    : functor_identity _ ⟹ FL ∙ FR.
  Proof.
    use mk_nat_trans.
    - exact factor_η_data.
    - exact factor_η_is_nat_trans.
  Defined.

  Definition factor_ε_data
    : nat_trans_data (FR ∙ FL) (functor_identity _)
    := λ X, ε (pr1 X) ,, tt.

  Definition factor_ε_is_nat_trans
    : is_nat_trans _ _ factor_ε_data.
  Proof.
    intros X Y f.
    use subtypeEquality.
    {
      intro ; apply isapropunit.
    }
    apply ε.
  Qed.

  Definition factor_ε
    : FR ∙ FL ⟹ functor_identity _.
  Proof.
    use mk_nat_trans.
    - exact factor_ε_data.
    - exact factor_ε_is_nat_trans.
  Defined.

  Definition factor_adjoints
    : are_adjoints FL FR.
  Proof.
    use mk_are_adjoints.
    - exact factor_η.
    - exact factor_ε.
    - split.
      + intro X.
        use subtypeEquality.
        { intro ; apply isapropunit. }
        apply adj.
      + intro X.
        use subtypeEquality.
        { intro ; apply isapropunit. }
        apply adj.
  Defined.
End FactorFunctorAdjunction.