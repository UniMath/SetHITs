(**
Here we define the adjunction between set and setoid algebras.
We first construct an adjunction between the prealgebras and then we factor it through the full subcategory.
 *)
Require Import prelude.all.

Require Import syntax.hit_signature.
Require Import algebras.set_algebra.
Require Import algebras.setoid_algebra.
Require Import algebras.univalent_algebra.

Require Import setoids.base.
Require Import setoids.setoid_category.

Open Scope cat.

(**
Step 0: we show that the path setoid functor commuets with products and coproducts.
 *)
Definition path_setoid_sum
           (X Y : HSET)
  : (path_setoid (setcoprod X Y))
      -->
      (sum_setoid (path_setoid X) (path_setoid Y)).
Proof.
  use mk_setoid_morphism.
  - exact (idfun _).
  - intros x y p.
    induction p.
    induction x as [x | x] ; reflexivity.
Defined.

Definition sum_path_setoid
           (X Y : HSET)
  : (sum_setoid (path_setoid X) (path_setoid Y))
      -->
      path_setoid (setcoprod X Y).
Proof.
  use mk_setoid_morphism.
  - exact (idfun _).
  - intros x y p.
    induction x as [x | x], y as [y | y].
    + cbn in * ; unfold idfun.
      induction p.
      reflexivity.
    + exact (fromempty p).
    + exact (fromempty p).
    + cbn in * ; unfold idfun.
      induction p.
      reflexivity.
Defined.

Definition path_setoid_sum_is_inverse
           (X Y : HSET)
  : is_inverse_in_precat (sum_path_setoid X Y) (path_setoid_sum X Y).
Proof.
  split.
  - use setoid_morphism_eq.
    intro x.
    reflexivity.
  - use setoid_morphism_eq.
    intro x.
    reflexivity.
Qed.

Definition path_setoid_prod
           (X Y : HSET)
  : (path_setoid (X × Y)%set)
      -->
      (prod_setoid (path_setoid X) (path_setoid Y)).
Proof.
  use mk_setoid_morphism.
  - exact (idfun _).
  - intros x y p.
    induction p.
    split ; reflexivity.
Defined.

Definition prod_path_setoid
           (X Y : HSET)
  : (prod_setoid (path_setoid X) (path_setoid Y))
      -->
      path_setoid (X × Y)%set.
Proof.
  use mk_setoid_morphism.
  - exact (idfun _).
  - intros x y p.
    unfold idfun ; simpl in *.
    apply pathsdirprod.
    + exact (pr1 p).
    + exact (pr2 p).
Defined.

Definition path_setoid_prod_is_inverse
           (X Y : HSET)
  : is_inverse_in_precat (prod_path_setoid X Y) (path_setoid_prod X Y).
Proof.
  split.
  - use setoid_morphism_eq.
    intro x.
    reflexivity.
  - use setoid_morphism_eq.
    intro x.
    reflexivity.
Qed.

(**
Step 1: the path setoid functor lifts to a functor on prealgebras.
For this we construct the commutativity natural transformation.
 *)
Definition path_setoid_commute_comp
           (P : poly_code)
  : nat_trans_data (path_setoid ∙ ⟨ P ⟩) (⦃ P ⦄ ∙ path_setoid).
Proof.
  intro X.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply identity.
  - apply identity.
  - exact (coprod_maps setoid_cat_bincoproducts IHP₁ IHP₂ · sum_path_setoid _ _).
  - exact (prod_maps setoid_cat_binproducts IHP₁ IHP₂ · prod_path_setoid _ _).
Defined.

Definition path_setoid_commute_is_nat_trans
           (P : poly_code)
  : is_nat_trans _ _ (path_setoid_commute_comp P).
Proof.
  intros X Y f.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - use setoid_morphism_eq.
    reflexivity.
  - use setoid_morphism_eq.
    reflexivity.
  - use setoid_morphism_eq.
    intros x.
    induction x as [x | x].
    + exact (maponpaths inl (eqtohomot (maponpaths pr1 IHP₁) x)).
    + exact (maponpaths inr (eqtohomot (maponpaths pr1 IHP₂) x)).
  - use setoid_morphism_eq.
    intros x.
    use dirprod_paths.
    + exact (eqtohomot (maponpaths pr1 IHP₁) (pr1 x)).
    + exact (eqtohomot (maponpaths pr1 IHP₂) (pr2 x)).
Qed.

Definition path_setoid_commute
           (P : poly_code)
  : path_setoid ∙ ⟨ P ⟩ ⟹ ⦃ P ⦄ ∙ path_setoid.
Proof.
  use mk_nat_trans.
  - exact (path_setoid_commute_comp P).
  - exact (path_setoid_commute_is_nat_trans P).
Defined.

Definition path_setoid_commute_inv_comp
           (P : poly_code)
  : nat_trans_data (⦃ P ⦄ ∙ path_setoid) (path_setoid ∙ ⟨ P ⟩).
Proof.
  intro X.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - apply identity.
  - apply identity.
  - exact (path_setoid_sum _ _ · coprod_maps setoid_cat_bincoproducts IHP₁ IHP₂).
  - exact (path_setoid_prod _ _ · prod_maps setoid_cat_binproducts IHP₁ IHP₂).
Defined.

Definition path_setoid_commute_is_inverse
           (P : poly_code)
           (X : HSET)
  : is_inverse_in_precat
      ((path_setoid_commute P) X)
      (path_setoid_commute_inv_comp P X).
Proof.
  simpl.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (is_inverse_in_precat_identity (path_setoid T)).
  - exact (is_inverse_in_precat_identity (path_setoid X)).
  - exact (is_inverse_in_precat_comp
             (coprod_maps_inverse setoid_cat_bincoproducts IHP₁ IHP₂)
             (path_setoid_sum_is_inverse (⦃ P₁ ⦄ X) (⦃ P₂ ⦄ X))).
  - exact (is_inverse_in_precat_comp
             (prod_maps_inverse setoid_cat_binproducts IHP₁ IHP₂)
             (path_setoid_prod_is_inverse (⦃ P₁ ⦄ X) (⦃ P₂ ⦄ X))).
Qed.

Definition path_setoid_commute_inv
           (P : poly_code)
  : ⦃ P ⦄ ∙ path_setoid ⟹ path_setoid ∙ ⟨ P ⟩.
Proof.
  use inv_nat_trans.
  - exact (path_setoid_commute P).
  - exact (path_setoid_commute_inv_comp P).
  - exact (path_setoid_commute_is_inverse P).
Defined.

(**
Step 2: the quotient lifts to a functor on the prealgebras.
For that we construct the commutativity natural transformation.
Note: we construct it as an inverse.

We first show quotients commute with taking sums.
 *)
Definition quotient_sum
           (A B : setoid)
  : (quotient (sum_setoid A B))
      -->
      BinCoproductObject HSET (BinCoproductsHSET (quotient A) (quotient B)).
Proof.
  use setquotuniv.
  - intros x.
    induction x as [x | x].
    + exact (inl (setquotpr _ x)).
    + exact (inr (setquotpr _ x)).
  - intros x y r.
    induction x as [x | x], y as [y | y] ; simpl.
    + exact (maponpaths inl (iscompsetquotpr _ x y r)).
    + exact (fromempty r).
    + exact (fromempty r).
    + exact (maponpaths inr (iscompsetquotpr _ x y r)).
Defined.

Definition sum_quotient
           (A B : setoid)
  : (BinCoproductObject HSET (BinCoproductsHSET (quotient A) (quotient B)))
      -->
      quotient (sum_setoid A B).
Proof.
  intros x.
  induction x as [x | x] ; revert x.
  - use setquotuniv.
    + exact (λ a, setquotpr _ (inl a)).
    + intros a₁ a₂ r.
      apply iscompsetquotpr.
      exact r.
  - use setquotuniv.
    + exact (λ b, setquotpr _ (inr b)).
    + intros a₁ a₂ r.
      apply iscompsetquotpr.
      exact r.
Defined.

Definition quotient_sum_are_inverses
           (A B : setoid)
  : is_inverse_in_precat (quotient_sum A B) (sum_quotient A B).
Proof.
  split.
  - use funextsec.
    use (setquotunivprop' (λ z , _)).
    { intro. apply isasetsetquot. }
    intros x.
    induction x as [x | x] ; reflexivity.
  - use funextsec.
    intro x.
    induction x as [x | x] ; revert x.
    + use (setquotunivprop' (λ z , _)).
       { intro. apply setcoprod. }
       reflexivity.
    + use (setquotunivprop' (λ z , _)).
      { intro. apply setcoprod. }
      reflexivity.
Qed.

Definition quotient_sum_iso
           (A B : setoid)
  : iso (quotient (sum_setoid A B)) (setcoprod (quotient A) (quotient B)).
Proof.
  use mk_iso.
  - exact (quotient_sum A B).
  - use is_iso_qinv.
    + exact (sum_quotient A B).
    + exact (quotient_sum_are_inverses A B).
Defined.

(**
Next we show taking quotients commutes with products.
 *)
Definition quotient_prod
           (A B : setoid)
  : quotient (prod_setoid A B) --> (quotient A × quotient B)%set.
Proof.
  use setquotuniv.
  - exact (λ x, (setquotpr _ (pr1 x) ,, setquotpr _ (pr2 x))).
  - intros x y r ; simpl.
    apply dirprod_paths.
    + apply iscompsetquotpr.
      exact (pr1 r).
    + apply iscompsetquotpr.
      exact (pr2 r).
Defined.

Definition prod_quotient
           (A B : setoid)
  : ((quotient A × quotient B)%set : HSET) --> quotient (prod_setoid A B).
Proof.
  intros x.
  induction x as [x y].
  revert y.
  use setquotuniv.
  - intros b.
    revert x.
    use setquotuniv.
    + intros a.
      exact (setquotpr _ (a ,, b)).
    + intros a₁ a₂ r.
      apply iscompsetquotpr.
      split.
      * exact r.
      * exact (id _)%setoid.
  - intros b₁ b₂ r.
    revert x.
    use (setquotunivprop' (λ z , _)).
    { intro ; apply isasetsetquot. }
    intros a.
    apply iscompsetquotpr.
    split.
    + exact (id _)%setoid.
    + exact r.
Defined.

Definition quotient_prod_are_inverses
           (A B : setoid)
  : is_inverse_in_precat (quotient_prod A B) (prod_quotient A B).
Proof.
  split.
  - apply funextsec.
    use (setquotunivprop' (λ z , _)).
    { intro ; apply isasetsetquot. }
    reflexivity.
  - apply funextsec.
    intros x.
    induction x as [x y].
    revert y.
    use (setquotunivprop' (λ z , _)).
    { intro ; apply dirprod_hSet. }
    intro b.
    revert x.
    use (setquotunivprop' (λ z , _)).
    { intro ; apply dirprod_hSet. }
    intro a.
    reflexivity.
Qed.

Definition quotient_prod_iso
           (A B : setoid)
  : iso (quotient (prod_setoid A B)) (quotient A × quotient B)%set.
Proof.
  use mk_iso.
  - exact (quotient_prod A B).
  - use is_iso_qinv.
    + exact (prod_quotient A B).
    + exact (quotient_prod_are_inverses A B).
Defined.

(**
Now we define the natural tansformation of which we take the inverse.
 *)
Definition quotient_commute_comp
           (P : poly_code)
  : nat_trans_data (⟨ P ⟩ ∙ quotient) (quotient ∙ ⦃ P ⦄).
Proof.
  intro X.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (quotient_counit T).
  - exact (idfun (setquot (carrier_eq X))).
  - exact ((quotient_sum _ _) · coprod_maps BinCoproductsHSET IHP₁ IHP₂).
  - exact ((quotient_prod _ _) · prod_maps BinProductsHSET IHP₁ IHP₂).
Defined.

Definition quotient_commute_is_nat_trans
           (P : poly_code)
  : is_nat_trans _ _ (quotient_commute_comp P).
Proof.
  intros X Y f.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - use funextsec.
    use (setquotunivprop' (λ z , _)).
    + intro.
      apply T.
    + reflexivity.
  - cbn ; unfold idfun.
    apply maponpaths.
    use setoid_morphism_eq.
    intro.
    reflexivity.
  - use funextsec.
    use (setquotunivprop' (λ z , _)).
    + intro.
      apply setcoprod.
    + intro x.
      induction x as [x | x].
      * exact (maponpaths inl (eqtohomot IHP₁ (setquotpr _ x))).
      * exact (maponpaths inr (eqtohomot IHP₂ (setquotpr _ x))).
  - use funextsec.
    use (setquotunivprop' (λ z , _)).
    + intro.
      apply dirprod_hSet.
    + intros x.
      apply dirprod_paths.
      * exact (eqtohomot IHP₁ (setquotpr _ (pr1 x))).
      * exact (eqtohomot IHP₂ (setquotpr _ (pr2 x))).      
Qed.

Definition quotient_commute
           (P : poly_code)
  : ⟨ P ⟩ ∙ quotient ⟹ quotient ∙ ⦃ P ⦄.
Proof.
  use mk_nat_trans.
  - exact (quotient_commute_comp P).
  - exact (quotient_commute_is_nat_trans P).
Defined.

Definition quotient_commute_inv_comp
           (P : poly_code)
           (X : setoid_cat)
  : (⦃ P ⦄) (quotient X) --> quotient (⟨ P ⟩ X).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (setquotpr _).
  - exact (identity _).
  - exact ((@coprod_maps SET BinCoproductsHSET _ _ _ _ IHP₁ IHP₂)
             · sum_quotient _ _).
  - exact ((@prod_maps SET BinProductsHSET _ _ _ _ IHP₁ IHP₂)
             · prod_quotient _ _).
Defined.

Definition quotient_commute_is_inverse
           (P : poly_code)
           (X : setoid_cat)
  : is_inverse_in_precat ((quotient_commute P) X) (quotient_commute_inv_comp P X).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (quotient_counit_is_inverse T).
  - exact (@is_inverse_in_precat_identity HSET (setquotinset (carrier_eq X))).
  - exact (is_inverse_in_precat_comp
             (quotient_sum_are_inverses (⟨ P₁ ⟩ X) (⟨ P₂ ⟩ X))
             (coprod_maps_inverse BinCoproductsHSET IHP₁ IHP₂)).
  - exact (is_inverse_in_precat_comp
             (quotient_prod_are_inverses (⟨ P₁ ⟩ X) (⟨ P₂ ⟩ X))
             (prod_maps_inverse BinProductsHSET IHP₁ IHP₂)).
Qed.

Definition quotient_commute_inv
           (P : poly_code)
  : quotient ∙ ⦃ P ⦄ ⟹ ⟨ P ⟩ ∙ quotient.
Proof.
  use inv_nat_trans.
  - exact (quotient_commute P).
  - exact (quotient_commute_inv_comp P).
  - exact (quotient_commute_is_inverse P).
Defined.

(**
Now we got both required natural transformations.
Let us add some notation for the lifted functors.
 *)
Definition path_setoid_prealgebras
           (P : poly_code)
  : set_prealgebras P ⟶ setoid_prealgebras P.
Proof.
  use algebra_functor.
  - exact path_setoid.
  - exact (path_setoid_commute P).
Defined.

Definition quotient_prealgebras
           (P : poly_code)
  : setoid_prealgebras P ⟶ set_prealgebras P.
Proof.
  use algebra_functor.
  - exact quotient.
  - exact (quotient_commute_inv P).
Defined.

(**
Step 3: we conclude these two functors are adjoints.
 *)
Definition quotient_prealgebras_unit_help_point
           (P : poly_code)
           (X : setoid_cat)
           (x : pr1 (⟨ P ⟩ X))
  : setquotpr (carrier_eq (⟨ P ⟩ X)) x
    =
    quotient_commute_inv_comp
      P X
      (pr1 (path_setoid_commute_comp P _)
           (pr1 (#⟨ P ⟩ (quotient_unit X)) x)).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - reflexivity.
  - reflexivity.
  - induction x as [x | x].
    + simpl.
      unfold coprod_maps, compose.
      simpl.
      refine (!(_ @ _)).
      {
        apply maponpaths.
        exact (!(IHP₁ x)).
      }
      reflexivity.
    + simpl.
      unfold coprod_maps, compose.
      simpl.
      refine (!(_ @ _)).
      {
        apply maponpaths.
        exact (!(IHP₂ x)).
      }
      reflexivity.
  - simpl.
    unfold prod_maps, compose.
    simpl.
    unfold BinProductOfArrows, BinProductArrow ; simpl.
    unfold compose ; simpl.
    unfold prodtofuntoprod ; simpl.
    unfold BinProductPr1, BinProductPr2 ; simpl.
    refine (!(_ @ _)).
    {
      apply maponpaths.
      exact (pathsdirprod (!(IHP₁ (pr1 x))) (!(IHP₂ (pr2 x)))).
    }
    reflexivity.
Qed.

Definition quotient_prealgebras_unit_help
           (P : poly_code)
           (X : setoid_cat)
  : quotient_unit (⟨ P ⟩ X)
    =
    # ⟨ P ⟩ (quotient_unit X)
     · path_setoid_commute_comp P (quotient X)
     · functor_on_morphisms path_setoid (quotient_commute_inv P X).
Proof.
  use setoid_morphism_eq.
  apply quotient_prealgebras_unit_help_point.
Qed.

(**
Some lemmata we need.
 *)
Definition inl_quotient_counit
           (P Q : poly_code)
           (X : HSET)
  : ∏ x,
    quotient_counit
      (⦃ P + Q ⦄ X)
      (functor_on_morphisms
         quotient
         (functor_on_morphisms path_setoid (inl : ⦃ P ⦄ X → ⦃ P + Q ⦄ X)) x)
    =
    inl (quotient_counit
           (⦃ P ⦄ X)
           x)
  := eqtohomot (pr2 quotient_counit (⦃ P ⦄ X) (⦃ P + Q ⦄ X) inl).

Definition inr_quotient_counit
           (P Q : poly_code)
           (X : HSET)
  : ∏ x,
    quotient_counit
      (⦃ P + Q ⦄ X)
      (functor_on_morphisms
         quotient
         (functor_on_morphisms
            path_setoid
            (inr : ⦃ Q ⦄ X → ⦃ P + Q ⦄ X)) x)
    =
    inr (quotient_counit
           (⦃ Q ⦄ X)
           x)
  := eqtohomot (pr2 quotient_counit (⦃ Q ⦄ X) (⦃ P + Q ⦄ X) inr).

Definition dirprod_quotient_counit
           (P Q : poly_code)
           (X : HSET)
  : ∏ (z : dirprod _ _),
     quotient_counit
       (⦃ P * Q ⦄ X)
       (((prod_quotient (path_setoid (⦃ P ⦄ X)) (path_setoid (⦃ Q ⦄ X)))
           · functor_on_morphisms quotient (prod_path_setoid _ _)) z)
     =
     dirprodpair
       (quotient_counit (⦃ P ⦄ X) (pr1 z))
       (quotient_counit (⦃ Q ⦄ X) (pr2 z)).
Proof.
  intros z.
  induction z as [z₁ z₂].
  revert z₂.
  use (setquotunivprop' (λ z , _)).
  {
    intro.
    apply setdirprod.
  }
  intro x₂.
  revert z₁.
  use (setquotunivprop' (λ z , _)).
  {
    intro.
    apply setdirprod.
  }
  intro x₁.
  reflexivity.
Qed.

(**
Lemmata how `path_setoid_commute_comp` interacts with `inl` and `inr`
 *)
Definition path_setoid_commute_comp_inl
           (P Q : poly_code)
           (X : HSET)
  : (path_setoid_commute_comp P X)
      · functor_on_morphisms path_setoid (inl : ⦃ P ⦄ X → ⦃ P + Q ⦄ X)
    =
    (setoid_inl (⟨ P ⟩ (path_setoid X)) (⟨ Q ⟩ (path_setoid X)))
      · path_setoid_commute_comp (P + Q) X
  := idpath _.

Definition path_setoid_commute_comp_inr
           (P Q : poly_code)
           (X : HSET)
  : (path_setoid_commute_comp Q X)
      · functor_on_morphisms path_setoid (inr : ⦃ Q ⦄ X → ⦃ P + Q ⦄ X)
    =
    (setoid_inr (⟨ P ⟩ (path_setoid X)) (⟨ Q ⟩ (path_setoid X)))
      · path_setoid_commute_comp (P + Q) X
  := idpath _.

(**
Needed for `inl`
 *)
Definition quotient_prealgebras_counit_help_inl
           (P Q : poly_code)
           (X : HSET)
           (x : ⦃ P ⦄ (quotient (path_setoid X)))
  : quotient_counit
      (⦃ P + Q ⦄ X)
      (functor_on_morphisms quotient (path_setoid_commute_comp (P + Q) X)
         ((quotient_commute_inv (P + Q)) (path_setoid X) (inl x)))
    =
    inl (quotient_counit
           (⦃ P ⦄ X)
           (functor_on_morphisms quotient
              (path_setoid_commute_comp P X)
              ((quotient_commute_inv P) (path_setoid X) x))).
Proof.
  refine (_ @ inl_quotient_counit P Q X _).
  apply maponpaths.
  refine (_ @ eqtohomot (functor_comp quotient _ _) _).
  refine (!(_ @ _)).
  {
    apply maponpaths_2.
    exact (path_setoid_commute_comp_inl P Q X).
  }
  rewrite functor_comp.
  reflexivity.
Qed.

Definition quotient_prealgebras_counit_help_inr
           (P Q : poly_code)
           (X : HSET)
           (x : ⦃ Q ⦄ (quotient (path_setoid X)))
  : quotient_counit
      (⦃ P + Q ⦄ X)
      (functor_on_morphisms quotient (path_setoid_commute_comp (P + Q) X)
         ((quotient_commute_inv (P + Q)) (path_setoid X) (inr x)))
    =
    inr (quotient_counit
           (⦃ Q ⦄ X)
           (functor_on_morphisms quotient
              (path_setoid_commute_comp Q X)
              ((quotient_commute_inv Q) (path_setoid X) x))).
Proof.
  refine (_ @ inr_quotient_counit P Q X _).
  apply maponpaths.
  refine (_ @ eqtohomot (functor_comp quotient _ _) _).
  refine (!(_ @ _)).
  {
    apply maponpaths_2.
    exact (path_setoid_commute_comp_inr P Q X).
  }
  rewrite functor_comp.
  reflexivity.
Qed.

Definition prod_quotient_help
           (P₁ P₂ : poly_code)
           (X : HSET)
           (z₁ : quotient ((path_setoid ∙ ⟨ P₁ ⟩) X) : hSet)
           (z₂ : quotient ((path_setoid ∙ ⟨ P₂ ⟩) X) : hSet)
  : prod_quotient
      (path_setoid (⦃ P₁ ⦄ X))
      (path_setoid (⦃ P₂ ⦄ X))
      (functor_on_morphisms quotient (path_setoid_commute_comp P₁ X) z₁
        ,,
        functor_on_morphisms quotient (path_setoid_commute_comp P₂ X) z₂)
    =
    functor_on_morphisms quotient
     (prod_maps setoid_cat_binproducts
                (path_setoid_commute_comp P₁ X)
                (path_setoid_commute_comp P₂ X))
     (prod_quotient ((path_setoid ∙ ⟨ P₁ ⟩) X) ((path_setoid ∙ ⟨ P₂ ⟩) X) (z₁ ,, z₂)).
Proof.
  revert z₂.
  use (setquotunivprop' (λ z , _)).
  {
    intro.
    apply isasetsetquot.
  }
  intro x₂.
  revert z₁.
  use (setquotunivprop' (λ z , _)).
  {
    intro.
    apply isasetsetquot.
  }
  intro x₁.
  reflexivity.
Qed.

Definition quotient_prealgebras_counit_help_point
           (P : poly_code)
           (X : HSET)
           (x : ⦃ P ⦄ (quotient(path_setoid X)))
  : quotient_counit
      (⦃ P ⦄ X)
      (functor_on_morphisms quotient
        (path_setoid_commute_comp P X)
        (quotient_commute_inv
           P (path_setoid X) x))
    =
    #⦃ P ⦄ (quotient_counit X) x.
Proof.
  simpl. cbn.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - reflexivity.
  - revert x.
    use (@setquotunivprop' (X : hSet) (path_rel X)).
    {
      intro ; apply X.
    }
    reflexivity.
  - induction x as [x | x].
    + specialize (IHP₁ x) ; clear IHP₂.
      refine (_ @ maponpaths inl IHP₁).
      exact (quotient_prealgebras_counit_help_inl P₁ P₂ X x).
    + specialize (IHP₂ x) ; clear IHP₁.
      refine (_ @ maponpaths inr IHP₂).
      exact (quotient_prealgebras_counit_help_inr P₁ P₂ X x).
  - induction x as [x₁ x₂].
    specialize (IHP₁ x₁) ; specialize (IHP₂ x₂).
    refine (_ @ pathsdirprod IHP₁ IHP₂).
    pose (z₁ := (functor_on_morphisms quotient (path_setoid_commute_comp P₁ X)
                   ((quotient_commute_inv P₁) (path_setoid X) x₁))).
    pose (z₂ := (functor_on_morphisms quotient (path_setoid_commute_comp P₂ X)
                   ((quotient_commute_inv P₂) (path_setoid X) x₂))).
    simple refine (_ @ dirprod_quotient_counit P₁ P₂ X (z₁ ,, z₂)).
    apply maponpaths.
    refine (eqtohomot
              (functor_comp
                 quotient
                 (prod_maps setoid_cat_binproducts
                            (path_setoid_commute P₁ X)
                            (path_setoid_commute P₂ X))
                 (prod_path_setoid _ _))
              _
              @ _).
    unfold compose ; simpl.
    apply maponpaths.
    unfold compose ; simpl.
    refine (_ @ !(prod_quotient_help P₁ P₂ X _ _)).
    reflexivity.
Qed.

Definition quotient_prealgebras_counit_help
           (P : poly_code)
           (X : HSET)
  : (quotient_commute_inv P (path_setoid X))
      · functor_on_morphisms quotient (path_setoid_commute_comp P X)
      · quotient_counit (⦃ P ⦄ X)
    =
    #⦃ P ⦄ (quotient_counit X).
Proof.
  use funextsec.
  exact (quotient_prealgebras_counit_help_point P X).
Qed.

Definition quotient_prealgebas_adjunction
           (P : poly_code)
  : are_adjoints (quotient_prealgebras P) (path_setoid_prealgebras P).
Proof.
  use prealgebra_adjunction.
  - exact quotient_adjunction.
  - intros X.
    exact (quotient_prealgebras_counit_help P X).
  - intros X.
    exact (quotient_prealgebras_unit_help P X).
Defined.

(**
Step 4: we factor these functors through the full subcategory of algebras.
We start with some lemmata on how the action of functors on endpoints.
 *)
Definition path_setoid_endpoint
           {A P Q : poly_code}
           (e : endpoint A P Q)
           (X : set_prealgebras A)
  : (path_setoid_commute P _)
      · functor_on_morphisms path_setoid (set_endpoint e X)
    =
    (setoid_endpoint e (path_setoid_prealgebras A X))
                    · path_setoid_commute Q (pr1 X).
Proof.
  use setoid_morphism_eq.
  intro x.
  induction e ; try reflexivity.
  - simpl.
    unfold compose ; simpl.
    refine (_ @ _).
    {
      apply maponpaths.
      exact (IHe1 x).
    }
    apply IHe2.
  - apply dirprod_paths.
    + exact (IHe1 x).
    + exact (IHe2 x).
Qed.

Definition path_setoid_hit_endpoint
           {A P : poly_code}
           (e : endpoint A P I)
           (X : set_prealgebras A)
           x
  : pr1 ((path_setoid_commute P _)
           · functor_on_morphisms path_setoid (set_endpoint e X)) x
    =
    pr1 (setoid_endpoint e (path_setoid_prealgebras A X)) x.
Proof.
  rewrite (path_setoid_endpoint e X).
  reflexivity.
Qed.

Definition set_algebra_is_setoid_algebra
           (Σ : hit_signature)
           (X : set_prealgebras (point_arg Σ))
  : is_set_algebra Σ X
    →
    is_setoid_algebra Σ ((path_setoid_prealgebras (point_arg Σ)) X).
Proof.
  intros HX j x.
  simpl in x.
  specialize (HX j).
  simpl in *.
  refine (!(path_setoid_hit_endpoint (path_lhs Σ j) X) x @ _).
  refine (_ @ path_setoid_hit_endpoint (path_rhs Σ j) X x).
  apply maponpaths_2.
  do 2 apply maponpaths.
  use funextsec.
  exact HX.
Qed.

Definition path_setoid_algebra
           (Σ : hit_signature)
  : set_algebra Σ ⟶ setoid_algebra Σ.
Proof.
  use factor_functor.
  - exact (path_setoid_prealgebras _).
  - exact (set_algebra_is_setoid_algebra Σ).
Defined.

Definition quotient_endpoint
           {A P Q : poly_code}
           (e : endpoint A P Q)
           (X : setoid_prealgebras A)
  : functor_on_morphisms quotient (setoid_endpoint e X)
     · quotient_commute_comp Q (prealgebra_setoid A X)
    =
    (quotient_commute_comp P (prealgebra_setoid A X))
      · set_endpoint e (quotient_prealgebras A X).
Proof.
  use funextsec.
  intro x. revert x.
  use (setquotunivprop' (λ z , _)).
  {
    intro.
    apply setproperty.
  }
  intro x.
  simpl. cbn.
  induction e ; try (apply idpath).
  - specialize (IHe1 x).
    specialize (IHe2 (pr1 (setoid_endpoint e1 X) x)).
    exact (IHe2 @ maponpaths _ IHe1).
  - apply dirprod_paths.
    + apply IHe1.
    + apply IHe2.
  - cbn.
    pose (eqtohomot (pr1 (quotient_commute_is_inverse A (pr1 X)))) as p.
    cbn in p.
    rewrite p.
    reflexivity.
Qed.

Definition quotient_hit_endpoint_help
           {A P : poly_code}
           (e : endpoint A P I)
           (X : setoid_prealgebras A)
  : functor_on_morphisms quotient (setoid_endpoint e X)
    =
    (quotient_commute_comp P (prealgebra_setoid A X))
      · set_endpoint e (quotient_prealgebras A X)
  := quotient_endpoint e X.

Definition quotient_hit_endpoint
           {A P : poly_code}
           (e : endpoint A P I)
           (X : setoid_prealgebras A)
  : (quotient_commute_inv P (prealgebra_setoid A X))
      · functor_on_morphisms quotient (setoid_endpoint e X)
    =
    set_endpoint e (quotient_prealgebras A X).
Proof.
  rewrite (quotient_hit_endpoint_help e X).
  rewrite assoc.
  refine (_ @ _).
  {
    apply maponpaths_2.
    exact (pr2 (quotient_commute_is_inverse P (pr1 X))).
  }
  rewrite id_left.
  reflexivity.
Qed.

Definition setoid_algebra_is_set_algebra
           (Σ : hit_signature)
           (X : setoid_prealgebras (point_arg Σ))
  : is_setoid_algebra Σ X
    →
    is_set_algebra Σ ((quotient_prealgebras (point_arg Σ)) X).
Proof.
  intros HX j x.
  specialize (HX j).
  simpl in x.
  simpl in HX.
  simpl.
  refine (eqtohomot (!(quotient_hit_endpoint (path_lhs Σ j) X)) _ @ _).
  refine (_ @ eqtohomot (quotient_hit_endpoint (path_rhs Σ j) X) x).
  apply maponpaths_2.
  use funextsec.
  intro y ; revert y.
  use setquotunivprop'.
  { intro. apply isasetsetquot. }
  intros z.
  specialize (HX z).
  simpl.
  apply iscompsetquotpr.
  exact HX.
Qed.

Definition quotient_algebra
           (Σ : hit_signature)
  : setoid_algebra Σ ⟶ set_algebra Σ.
Proof.
  use factor_functor.
  - exact (quotient_prealgebras _).
  - exact (setoid_algebra_is_set_algebra Σ).
Defined.

Definition quotient_algebra_adjunction
           (Σ : hit_signature)
  : are_adjoints (quotient_algebra Σ) (path_setoid_algebra Σ).
Proof.
  use factor_adjoints.
  exact (quotient_prealgebas_adjunction _).
Defined.