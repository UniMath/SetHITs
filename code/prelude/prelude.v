(**
Here we collect some basic facts and definitions.
 *)
Require Import prelude.imports.

Open Scope cat.

(**
Sum of two maps.
 *)
Definition coprod_maps
           {C : precategory}
           (BC : BinCoproducts C)
           {X₁ X₂ Y₁ Y₂ : C}
           (f₁ : X₁ --> Y₁)
           (f₂ : X₂ --> Y₂)
  : bincoproduct_functor BC (X₁ ,, X₂) --> bincoproduct_functor BC (Y₁ ,, Y₂).
Proof.
  refine (#(bincoproduct_functor BC) (_ ,, _)).
  - exact f₁.
  - exact f₂.
Defined.

(**
If two maps are invertible, then so is their sum
 *)
Definition coprod_maps_inverse
           {C : precategory}
           (BC : BinCoproducts C)
           {X₁ X₂ Y₁ Y₂ : C}
           {f₁ : X₁ --> Y₁} {g₁ : Y₁ --> X₁}
           {f₂ : X₂ --> Y₂} {g₂ : Y₂ --> X₂}
           (H₁ : is_inverse_in_precat f₁ g₁)
           (H₂ : is_inverse_in_precat f₂ g₂)
  : is_inverse_in_precat (coprod_maps BC f₁ f₂) (coprod_maps BC g₁ g₂).
Proof.
  split.
  - cbn.
    rewrite BinCoproductOfArrows_comp.
    rewrite (pr1 H₁), (pr1 H₂).
    unfold BinCoproductOfArrows.
    refine (_ @ !(BinCoproductArrowEta _ _ _ _ _ _)).
    rewrite !id_left, !id_right.
    reflexivity.
  - cbn.
    rewrite BinCoproductOfArrows_comp.
    rewrite (pr2 H₁), (pr2 H₂).
    unfold BinCoproductOfArrows.
    refine (_ @ !(BinCoproductArrowEta _ _ _ _ _ _)).
    rewrite !id_left, !id_right.
    reflexivity.
Qed.

(**
Product of two maps.
 *)
Definition prod_maps
           {C : precategory}
           (BC : BinProducts C)
           {X₁ X₂ Y₁ Y₂ : C}
           (f₁ : X₁ --> Y₁)
           (f₂ : X₂ --> Y₂)
  : binproduct_functor BC (X₁ ,, X₂) --> binproduct_functor BC (Y₁ ,, Y₂).
Proof.
  refine (#(binproduct_functor BC) (_ ,, _)).
  - exact f₁.
  - exact f₂.
Defined.

(**
If two maps are invertible, then so is their product.
 *)
Definition prod_maps_inverse
           {C : precategory}
           (BC : BinProducts C)
           {X₁ X₂ Y₁ Y₂ : C}
           {f₁ : X₁ --> Y₁} {g₁ : Y₁ --> X₁}
           {f₂ : X₂ --> Y₂} {g₂ : Y₂ --> X₂}
           (H₁ : is_inverse_in_precat f₁ g₁)
           (H₂ : is_inverse_in_precat f₂ g₂)
  : is_inverse_in_precat (prod_maps BC f₁ f₂) (prod_maps BC g₁ g₂).
Proof.
  split.
  - cbn.
    rewrite BinProductOfArrows_comp.
    rewrite (pr1 H₁), (pr1 H₂).
    unfold BinProductOfArrows.
    refine (_ @ !(BinProductArrowEta _ _ _ _ _ _)).
    rewrite !id_left, !id_right.
    reflexivity.
  - cbn.
    rewrite BinProductOfArrows_comp.
    rewrite (pr2 H₁), (pr2 H₂).
    unfold BinProductOfArrows.
    refine (_ @ !(BinProductArrowEta _ _ _ _ _ _)).
    rewrite !id_left, !id_right.
    reflexivity.
Qed.

(**
This is a particular way to construct the inverse of a natural transformation.
The coordinates of the inverse is given by `θ`.
 *)
Section InvNatTrans.
  Context {C D : precategory}
          {F G : C ⟶ D}.
  Variable (η : F ⟹ G)
           (θ : ∏ (X : C), G X --> F X)
           (ηθ : ∏ (X : C), is_inverse_in_precat (η X) (θ X)).

  Local Definition θ_is_nat_trans
    : is_nat_trans G F θ.
  Proof.
    intros X Y f.
    refine (!(id_left _) @ _).
    refine (assoc _ _ _ @ _ @ _).
    {
      do 2 apply maponpaths_2.
      exact (!(pr2 (ηθ X))).
    }
    rewrite <- !assoc.
    apply maponpaths.
    refine (assoc _ _ _ @ _ @ _).
    {
      apply maponpaths_2.
      exact (!(pr2 η _ _ f)).
    }
    refine (!(assoc _ _ _) @ _).
    refine (maponpaths (λ z, # F f · z) (pr1 (ηθ Y)) @ _).
    apply id_right.
  Qed.

  Definition inv_nat_trans
    : G ⟹ F.
  Proof.
    use mk_nat_trans.
    - exact θ.
    - exact θ_is_nat_trans.
  Defined.
End InvNatTrans.

(**
Left adjoints preserve initial objects.
 *)
Definition adj_initial
           {C D : category}
           {L : C ⟶ D}
           {R : D ⟶ C}
           (adj : are_adjoints L R)
           (X : C)
           (X_initial : isInitial _ X)
  : isInitial D (L X).
Proof.
  use mk_isInitial.
  intros Y.
  apply (iscontrweqf (invweq (pr1 (nathomweq_from_adj adj) X Y))).
  apply X_initial.
Defined.

(**
Pairing of natural transfomations.
 *)
Section PairNatTrans.
  Context {C₁ C₂ C₃ : precategory}
          {F : C₁ ⟶ C₂}
          {G₁ G₂ G₃ : C₂ ⟶ C₃}.
  Variable (H : BinProducts C₃)
           (η₁ : F ∙ G₁ ⟹ F ∙ G₂)
           (η₂ : F ∙ G₁ ⟹ F ∙ G₃).

  Local Definition pair_nat_trans_data
    : nat_trans_data (F ∙ G₁) (F ∙ BinProduct_of_functors C₂ C₃ H G₂ G₃).
  Proof.
    intros x.
    apply (BinProductArrow).
    - exact (η₁ x).
    - exact (η₂ x).
  Defined.

  Definition pair_nat_trans_is_nat_trans
    : is_nat_trans
        (F ∙ G₁)
        (F ∙ BinProduct_of_functors C₂ C₃ H G₂ G₃)
        pair_nat_trans_data.
  Proof.
    intros x y f ; cbn.
    refine (precompWithBinProductArrow _ _ _ _ _ @ _).
    pose (pr2 η₁ x y f) as p.
    pose (pr2 η₂ x y f) as q.
    cbn in p, q.
    refine (_ @ _).
    {
      apply maponpaths.
      exact q.
    }
    refine (_ @ _).
    {
      apply maponpaths_2.
      exact p.
    }
    unfold BinProduct_of_functors_mor, BinProductOfArrows, BinProductPr1, BinProductPr2.
    exact (!(postcompWithBinProductArrow _ _ _ _ _ _ _)).
  Qed.

  Definition pair_nat_trans
    : F ∙ G₁ ⟹ F ∙ (BinProduct_of_functors _ _ H G₂ G₃).
  Proof.
    use mk_nat_trans.
    - exact pair_nat_trans_data.
    - exact pair_nat_trans_is_nat_trans.
  Defined.
End PairNatTrans.

(**
Initial objects are isomorphic
 *)
Definition initial_iso
           {C : precategory}
           {X Y : C}
           (IX : isInitial _ X)
           (IY : isInitial _ Y)
  : iso X Y.
Proof.
  use mk_iso.
  - apply IX.
  - use is_iso_qinv.
    + apply IY.
    + split ; simpl.
      * exact (pr2 (IX X) _ @ !(pr2 (IX X) _)).
      * exact (pr2 (IY Y) _ @ !(pr2 (IY Y) _)).
Defined.

(**
Transport lemmata
 *)
Definition sum_hset_fam
           {A B : UU}
           (Y₁ : A → hSet)
           (Y₂ : B → hSet)
  : A ⨿ B → hSet.
Proof.
  intros x.
  induction x as [x | x].
  - exact (Y₁ x).
  - exact (Y₂ x).
Defined.

Definition transport_inl
           {A B : UU}
           (Y₁ : A → hSet)
           (Y₂ : B → hSet)
           {a₁ a₂ : A}
           (p : a₁ = a₂)
           (y : Y₁ a₁)
  : transportf (sum_hset_fam Y₁ Y₂) (maponpaths inl p) y = transportf Y₁ p y.
Proof.
  induction p ; simpl.
  reflexivity.
Qed.

Definition transport_inr
           {A B : UU}
           (Y₁ : A → hSet)
           (Y₂ : B → hSet)
           {b₁ b₂ : B}
           (p : b₁ = b₂)
           (y : Y₂ b₁)
  : transportf (sum_hset_fam Y₁ Y₂) (maponpaths inr p) y = transportf Y₂ p y.
Proof.
  induction p ; simpl.
  reflexivity.
Qed.

Definition prod_hset_fam
           {A B : UU}
           (Y₁ : A → hSet)
           (Y₂ : B → hSet)
  : A × B → hSet
  := (λ x, Y₁ (pr1 x) × Y₂ (pr2 x))%set.

Definition transport_pr1
           {A B : UU}
           (Y₁ : A → hSet)
           (Y₂ : B → hSet)
           {x₁ x₂ : A × B}
           (p : x₁ = x₂)
           (y : Y₁ (pr1 x₁) × Y₂ (pr2 x₁))
  : pr1 (transportf (prod_hset_fam Y₁ Y₂) p y) = transportf Y₁ (maponpaths pr1 p) (pr1 y).
Proof.
  induction p ; simpl.
  reflexivity.
Qed.

Definition transport_pr2
           {A B : UU}
           (Y₁ : A → hSet)
           (Y₂ : B → hSet)
           {x₁ x₂ : A × B}
           (p : x₁ = x₂)
           (y : Y₁ (pr1 x₁) × Y₂ (pr2 x₁))
  : pr2 (transportf (prod_hset_fam Y₁ Y₂) p y) = transportf Y₂ (maponpaths dirprod_pr2 p) (pr2 y).
Proof.
  induction p ; simpl.
  reflexivity.
Qed.