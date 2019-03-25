(**
Here we define the category of setoids.
The objects are setoids and the morphisms are setoid mophisms.
We also show it has sums, products, and exponentials.
We end by showing that the quotient from setoids to set is a left adjoint.
 *)
Require Import setoids.base.
Require Import prelude.all.

Open Scope cat.

(** The category of setoids *)
Definition setoid_cat_ob_mor
  : precategory_ob_mor.
Proof.
  use precategory_ob_mor_pair.
  - exact setoid.
  - exact setoid_morphism.
Defined.

Definition id_setoid_morphism (X : setoid)
  : setoid_morphism X X.
Proof.
  use mk_setoid_morphism.
  - exact (idfun X).
  - exact (λ x y, idfun (x ≡ y)).
Defined.

Definition comp_setoid_morphism
           {X₁ X₂ X₃ : setoid}
           (f₁ : setoid_morphism X₁ X₂)
           (f₂ : setoid_morphism X₂ X₃)
  : setoid_morphism X₁ X₃.
Proof.
  use mk_setoid_morphism.
  - exact (λ z, f₂(f₁ z)).
  - exact (λ x y p, map_eq f₂(map_eq f₁ p)).
Defined.

Definition setoid_cat_data
  : precategory_data.
Proof.
  use precategory_data_pair.
  - exact setoid_cat_ob_mor.
  - exact id_setoid_morphism.
  - exact @comp_setoid_morphism.
Defined.

Definition setoid_precat
  : precategory.
Proof.
  use mk_precategory.
  - exact setoid_cat_data.
  - repeat (use tpair) ; cbn.
    + reflexivity.
    + reflexivity.
    + reflexivity.
    + reflexivity.
Defined.

Definition setoid_cat
  : category.
Proof.
  use category_pair.
  - exact setoid_precat.
  - intros X₁ X₂ ; cbn.
    apply isaset_setoid_morphism.
Defined.

(** Sums in the category of setoids *)
Definition sum_rel
           {X Y : hSet}
           (R₁ : eqrel X)
           (R₂ : eqrel Y)
  : eqrel (setcoprod X Y)%set.
Proof.
  use mk_eq_rel.
  - intros s₁ s₂.
    destruct s₁ as [x₁ | y₁], s₂ as [x₂ | y₂].
    + exact (R₁ x₁ x₂).
    + exact hfalse.
    + exact hfalse.
    + exact (R₂ y₁ y₂).
  - intros s.
    destruct s as [x | y].
    + exact (id x)%setoid.
    + exact (id y)%setoid.
  - intros s₁ s₂.
    destruct s₁ as [x₁ | y₁], s₂ as [x₂ | y₂].
    + exact (λ p , ! p)%setoid.
    + exact (idfun _).
    + exact (idfun _).
    + exact (λ p , ! p)%setoid.
  - intros s₁ s₂ s₃.
    destruct s₁ as [x₁ | y₁], s₂ as [x₂ | y₂].
    + destruct s₃ as [x₃ | y₃].
      * exact (λ p q , p @ q)%setoid.
      * exact (λ _, fromempty).
    + exact fromempty.
    + exact fromempty.
    + destruct s₃ as [x₃ | y₃].
      * exact (λ _, fromempty).
      * exact (λ p q , p @ q)%setoid.
Defined.

Definition sum_setoid (X Y : setoid_cat)
  : setoid_cat
  := mk_setoid (sum_rel (carrier_eq X) (carrier_eq Y)).

Definition setoid_inl
           (X₁ X₂ : setoid_cat)
  : X₁ --> sum_setoid X₁ X₂.
Proof.
  use mk_setoid_morphism.
  - exact (λ x, inl x).
  - exact (λ _ _ p, p).
Defined.

Definition setoid_inr
           (X₁ X₂ : setoid_cat)
  : X₂ --> sum_setoid X₁ X₂.
Proof.
  use mk_setoid_morphism.
  - exact (λ x, inr x).
  - exact (λ _ _ p, p).
Defined.

Definition setoid_plus
           {X₁ X₂ Y : setoid_cat}
           (f : X₁ --> Y)
           (g : X₂ --> Y)
  : sum_setoid X₁ X₂ --> Y.
Proof.
  unshelve esplit.
  - intro z.
    destruct z as [x | x] ; cbn in *.
    + exact (f x).
    + exact (g x).
  - intros z₁ z₂ p.
    destruct z₁ as [x₁ | x₁ ], z₂ as [x₂ | x₂].
    + exact (map_eq f p).
    + exact (fromempty p).
    + exact (fromempty p).
    + exact (map_eq g p).
Defined.

Definition sum_setoid_is_bicoproduct
           (X₁ X₂ : setoid_cat)
  : isBinCoproduct
      setoid_cat X₁ X₂
      (sum_setoid X₁ X₂) (setoid_inl X₁ X₂) (setoid_inr X₁ X₂).
Proof.
  intros Y f g ; cbn.
  use tpair.
  - use tpair.
    + exact (setoid_plus f g).
    + split ; reflexivity.
  - intros h.
    use subtypeEquality.
    + intro.
      apply isapropdirprod ; apply setoid_cat.
    + use setoid_morphism_eq ; cbn.
      intro z.
      destruct z as [x | x].
      * induction (pr12 h).
        reflexivity.
      * induction (pr22 h).
        reflexivity.
Defined.

Definition setoid_cat_bicoproducts
  : BinCoproducts setoid_cat.
Proof.
  intros X₁ X₂.
  use tpair.
  - exact (sum_setoid X₁ X₂ ,, setoid_inl X₁ X₂ ,, setoid_inr X₁ X₂).
  - exact (sum_setoid_is_bicoproduct X₁ X₂).
Defined.

(** The category of setoids has binary products *)
Definition prod_rel
           {X Y : hSet}
           (R₁ : eqrel X)
           (R₂ : eqrel Y)
  : eqrel (X × Y)%set.
Proof.
  use mk_eq_rel.
  - exact (λ z₁ z₂, (hconj (R₁ (pr1 z₁) (pr1 z₂)) (R₂ (pr2 z₁) (pr2 z₂)))).
  - exact (λ z, (id (pr1 z) ,, id (pr2 z)))%setoid.
  - exact (λ _ _ p, (! (pr1 p) ,, ! (pr2 p)))%setoid.
  - exact (λ _ _ _ p q, ((pr1 p @ pr1 q) ,, (pr2 p @ pr2 q)))%setoid.
Defined.

Definition prod_setoid (X Y : setoid_cat)
  : setoid_cat
  := mk_setoid (prod_rel (carrier_eq X) (carrier_eq Y)).

Definition setoid_pr1
           (X₁ X₂ : setoid_cat)
  : prod_setoid X₁ X₂ --> X₁.
Proof.
  use mk_setoid_morphism.
  - exact (λ z ,  pr1 z).
  - exact (λ _ _, pr1).
Defined.

Definition setoid_pr2
           (X₁ X₂ : setoid_cat)
  : prod_setoid X₁ X₂ --> X₂.
Proof.
  use mk_setoid_morphism.
  - exact (λ z ,  pr2 z).
  - exact (λ _ _, pr2).
Defined.

Definition setoid_pair
           {X₁ X₂ Y : setoid_cat}
           (f : Y --> X₁)
           (g : Y --> X₂)
  : Y --> prod_setoid X₁ X₂.
Proof.
  use mk_setoid_morphism ; cbn in *.
  - exact (λ y, (f y ,, g y)).
  - exact (λ _ _ p, (map_eq f p ,, map_eq g p)).
Defined.

Definition prod_setoid_is_biproduct
           (X₁ X₂ : setoid_cat)
  : isBinProduct
      setoid_cat X₁ X₂
      (prod_setoid X₁ X₂) (setoid_pr1 X₁ X₂) (setoid_pr2 X₁ X₂).
Proof.
  intros Y f g ; cbn.
  use tpair.
  - use tpair.
    + exact (setoid_pair f g).
    + split ; reflexivity.
  - intros h.
    use subtypeEquality.
    + intro.
      apply isapropdirprod ; apply setoid_cat.
    + use setoid_morphism_eq ; cbn.
      intro z.
      use dirprod_paths.
      * induction (pr12 h).
        reflexivity.
      * induction (pr22 h).
        reflexivity.
Defined.

Definition setoid_cat_biproducts
  : BinProducts setoid_cat.
Proof.
  intros X₁ X₂.
  use tpair.
  - exact (prod_setoid X₁ X₂ ,, setoid_pr1 X₁ X₂ ,, setoid_pr2 X₁ X₂).
  - exact (prod_setoid_is_biproduct X₁ X₂).
Defined.

(** Exponentials of setoids *)
Definition setoid_morphism_hSet (X₁ X₂ : setoid)
  : hSet.
Proof.
  use hSetpair.
  - exact (setoid_morphism X₁ X₂).
  - apply isaset_setoid_morphism.
Defined.

Definition fun_rel
           (X₁ X₂ : setoid)
  : eqrel (setoid_morphism_hSet X₁ X₂).
Proof.
  use mk_eq_rel.
  - intros f g ; cbn in *.
    exact (∀ (x : X₁), f x ≡ g x).
  - exact (λ f x, id _ _)%setoid.
  - exact (λ f g p x, ! (p x))%setoid.
  - exact (λ f g h p₁ p₂ x, p₁ x @ p₂ x)%setoid.
Defined.

Definition setoid_exp
           (X₁ X₂ : setoid_cat)
  : setoid_cat
  := mk_setoid (fun_rel X₁ X₂).

Definition setoid_exp_functor_datat
           (X : setoid)
  : functor_data setoid_cat setoid_cat.
Proof.
  use mk_functor_data.
  - exact (setoid_exp X).
  - intros Y₁ Y₂ f ; cbn in *.
    use mk_setoid_morphism ; cbn.
    + exact (λ g, comp_setoid_morphism g f).
    + exact (λ g₁ g₂ p x, map_eq f (p x)).
Defined.

Definition setoid_exp_functor
           (X : setoid)
  : setoid_cat ⟶ setoid_cat.
Proof.
  use mk_functor.
  - exact (setoid_exp_functor_datat X).
  - split.
    + intros Y.
      use setoid_morphism_eq.
      reflexivity.
    + intros Y₁ Y₂ Y₃ f₁ f₂.
      use setoid_morphism_eq.
      reflexivity.
Defined.

Definition setoid_exp_unit
           (X : setoid)
  : (functor_identity setoid_precat)
      ⟹
      constprod_functor1 setoid_cat_biproducts X ∙ setoid_exp_functor X.
Proof.
  use mk_nat_trans.
  - intros Y.
    use mk_setoid_morphism.
    + intros y.
      use mk_setoid_morphism.
      * exact (λ x, x ,, y).
      * exact (λ x₁ x₂ p , p ,, id _ _)%setoid.
    + exact (λ y₁ y₂ p x , id _ _ ,, p)%setoid.
  - intros Y₁ Y₂ f.
    abstract (
        use setoid_morphism_eq ;
        intro y ;
        use setoid_morphism_eq ;
        reflexivity).
Defined.

Definition setoid_exp_counit
           (X : setoid)
  : (setoid_exp_functor X ∙ constprod_functor1 setoid_cat_biproducts X)
      ⟹
      functor_identity setoid_precat.
Proof.
  use mk_nat_trans.
  - intros Y.
    use mk_setoid_morphism.
    + intro z ; cbn in *.
      exact (pr2 z (pr1 z)).
    + intros z₁ z₂ p ; cbn in *.
      exact (map_eq (pr2 z₁) (pr1 p) @ pr2 p (pr1 z₂))%setoid.
  - intros Y₁ Y₂ f.
    use setoid_morphism_eq.
    reflexivity.
Defined.

Definition setoid_cat_has_exponentials
  : Exponentials setoid_cat_biproducts.
Proof.
  intro X.
  use tpair.
  - exact (setoid_exp_functor X).
  - use mk_are_adjoints.
    + exact (setoid_exp_unit X).
    + exact (setoid_exp_counit X).
    + split.
      * abstract(
            intros Y ;
            use setoid_morphism_eq ;
            reflexivity).
      * abstract
          (intros Y ;
           use setoid_morphism_eq ;
           intro ;
           use setoid_morphism_eq ;
           reflexivity).
Defined.

(** Functor from set to setoid *)
Definition path_rel
           (X : hSet)
  : eqrel X
  := mk_eq_rel
       (λ x y, eqset x y)
       idpath
       (λ _ _ p, ! p)
       (λ _ _ _ p q, p @ q).

Definition path_setoid_data : functor_data SET setoid_cat.
Proof.
  use mk_functor_data.
  - exact (λ X, mk_setoid (path_rel X)).
  - intros X Y f.
    use mk_setoid_morphism.
    + exact f.
    + exact (λ x y p, maponpaths f p).
Defined.
      
Definition path_setoid : SET ⟶ setoid_cat.
Proof.
  use mk_functor.
  - exact path_setoid_data.
  - split.
    + intros X ; cbn.
      use setoid_morphism_eq.
      reflexivity.
    + intros X Y Z f g ; cbn.
      use setoid_morphism_eq.
      reflexivity.
Defined.

(** Functor fom setoid to set *)
Definition quotient_setoid_ob
           (X : setoid)
  : hSet.
Proof.
  use setquotinset.
  - exact X.
  - exact (carrier_eq X).
Defined.

Definition quotient_setoid_mor
           {X₁ X₂ : setoid}
           (f : setoid_morphism X₁ X₂)
  : quotient_setoid_ob X₁ → quotient_setoid_ob X₂.
Proof.
  use setquotuniv ; cbn.
  - exact (λ x, setquotpr _ (f x)).
  - exact (λ x y p, iscompsetquotpr _ (f x) (f y) (map_eq f p)).
Defined.

Definition quotient
  : setoid_cat ⟶ SET.
Proof.
  use mk_functor.
  - use mk_functor_data.
    + exact quotient_setoid_ob.
    + exact @quotient_setoid_mor.
  - split.
    + intros X ; cbn.
      use funextsec ; intro x.
      use (setquotunivprop' (λ z, _ z = z)).
      * intro.
        apply isasetsetquot.
      * intro y ; cbn.
        reflexivity.
    + intros X Y Z f g ; cbn.
      use funextsec ; intro x.
      use (setquotunivprop' (λ z, _ z = quotient_setoid_mor g (quotient_setoid_mor f z))).
      * intro.
        apply isasetsetquot.
      * intro y ; cbn.
        reflexivity.
Defined.

Definition quotient_unit
  : functor_identity setoid_cat ⟹ quotient ∙ path_setoid.
Proof.
  use mk_nat_trans.
  - intro X ; cbn.
    use mk_setoid_morphism.
    + exact (setquotpr _).
    + exact (iscompsetquotpr _).
  - abstract
      (intros X Y f ; cbn ;
       use setoid_morphism_eq ;
       intro x ;
       reflexivity).
Defined.

Definition quotient_counit
  : path_setoid ∙ quotient ⟹ functor_identity SET.
Proof.
  use mk_nat_trans.
  - intro X ; cbn.
    use setquotuniv.
    + exact (idfun _).
    + exact (λ x y p, p).
  - abstract
      (intros X Y f ;
       use funextsec ;
       intro x ;
       revert x ;
       use setquotunivprop' ;
       [ intro ; apply Y | reflexivity ]).
Defined.

Definition quotient_counit_is_inverse
           (X : SET)
  : is_inverse_in_precat (quotient_counit X) (setquotpr (carrier_eq (path_setoid X))).
Proof.
  split.
  - use funextsec.
    use setquotunivprop'.
    { intro. apply isasetsetquot. }
    reflexivity.
  - use funextsec.
    intro.
    reflexivity.
Qed.

Definition quotient_counit_is_nat_iso
  : is_nat_iso quotient_counit.
Proof.
  intros X.
  use is_iso_qinv.
  - exact (setquotpr _).
  - exact (quotient_counit_is_inverse X).
Defined.
  
Definition quotient_adjunction
  : are_adjoints quotient path_setoid.
Proof.
  use mk_are_adjoints.
  - exact quotient_unit.
  - exact quotient_counit.
  - split.
    + abstract
        (intro X ;
         use funextsec ;
         intro x ; revert x ; cbn ;
         use setquotunivprop' ;
         [ intro ; apply isasetsetquot | reflexivity ]).
    + abstract
        (intro X ;
         use setoid_morphism_eq ;
         intro x ; cbn in * ;
         reflexivity).
Defined.

(** We show the category of setoids is univalent *)
Definition factor_idtoiso_1
           (X Y : setoid)
  : X = Y ≃ X ╝ Y
  := total2_paths_equiv _ X Y.

Definition factor_idtoiso_2
           (X Y : setoid)
  : X ╝ Y ≃ ∑ (f : pr1 X ≃ pr1 Y), ∏ x y : X, x ≡ y ≃ f x ≡ f y.
Proof.
  use weqtotal2.
  - exact (hSet_univalence (pr1 X) (pr1 Y)).
  - intros p.
    induction X as [X RX], Y as [Y RY].
    simpl in *.
    induction p ; cbn ; unfold idfun.
    refine ((weqonsecfibers _ _ (λ x, weqonsecfibers _ _ (λ y, weqeqweqhProp _ _)))
              ∘ weqonsecfibers _ _ (λ x, weqtoforallpaths _ _ _)
              ∘ weqtoforallpaths _ RX RY
              ∘ path_sigma_hprop _ _ _ _)%weq.
    repeat (use isapropdirprod).
    + apply isaprop_istrans.
    + apply isaprop_isrefl.
    + do 3 (use impred ; intro).
      apply (pr1 RY).
Defined.

Definition factor_idtoiso_3_map
           (X Y : setoid)
  : (∑ (f : pr1 X ≃ pr1 Y), ∏ x y : X, x ≡ y ≃ f x ≡ f y) → @iso setoid_cat X Y.
Proof.
  intros f.
  use tpair.
  - use mk_setoid_morphism.
    + exact (pr1 f).
    + apply f.
  - use is_iso_qinv.
    + use mk_setoid_morphism.
      * apply (invweq (pr1 f)).
      * intros x y r ; simpl.
        apply (invweq (pr2 f (invmap (pr1 f) x) (invmap (pr1 f) y))).
        refine (_ @ r @ _)%setoid.
        ** apply setoid_path.
           apply homotweqinvweq.
        ** apply setoid_path.
           refine (!_).
           apply homotweqinvweq.
    + split.
      * use setoid_morphism_eq.
        intro x ; cbn.
        apply homotinvweqweq.
      * use setoid_morphism_eq.
        intro x ; cbn.
        apply homotweqinvweq.
Defined.

Definition factor_idtoiso_3_inv
           (X Y : setoid)
  : @iso setoid_cat X Y → (∑ (f : pr1 X ≃ pr1 Y), ∏ x y : X, x ≡ y ≃ f x ≡ f y).
Proof.
  intros f.
  use tpair.
  - use weqpair.
    + exact (pr11 f).
    + use gradth.
      * exact (pr1 (inv_from_iso f)).
      * exact (eqtohomot (maponpaths pr1 (iso_inv_after_iso f))).
      * exact (eqtohomot (maponpaths pr1 (iso_after_iso_inv f))).
  - intros x y ; simpl.
    use weqimplimpl.
    + exact (pr21 f x y).
    + intros r.
      refine (_ @ pr2 (inv_from_iso f) (pr11 f x) (pr11 f y) r @ _)%setoid.
      * exact (setoid_path (!(eqtohomot (maponpaths pr1 (iso_inv_after_iso f))) x)).
      * exact (setoid_path ((eqtohomot (maponpaths pr1 (iso_inv_after_iso f))) y)).
    + apply isaprop_setoid_eq.
    + apply isaprop_setoid_eq.
Defined.

Definition factor_idtoiso_3
           (X Y : setoid)
  : (∑ (f : pr1 X ≃ pr1 Y), ∏ x y : X, x ≡ y ≃ f x ≡ f y) ≃ @iso setoid_cat X Y.
Proof.
  use weqpair.
  - exact (factor_idtoiso_3_map X Y).
  - use gradth.
    + exact (factor_idtoiso_3_inv X Y).
    + intros f.
      use subtypeEquality.
      {
        intro.
        do 2 (use impred ; intro).
        apply isaproptotal2.
        * intro.
          apply isapropisweq.
        * intros.
          use funextsec ; intro.
          apply isaprop_setoid_eq.
      }
      use subtypeEquality.
      {
        intro.
        apply isapropisweq.
      }
      reflexivity.
    + intros f.
      use subtypeEquality.
      {
        intro.
        apply isaprop_is_iso.
      }
      use setoid_morphism_eq.
      reflexivity.
Defined.

Definition idtoiso_setoid_cat
           (X Y : setoid_cat)
  : X = Y ≃ iso X Y
  := (factor_idtoiso_3 X Y ∘ factor_idtoiso_2 X Y ∘ factor_idtoiso_1 X Y)%weq.
    
Definition setoid_cat_is_univalent
  : is_univalent setoid_cat.
Proof.
  split.
  - intros X Y.
    use weqhomot.
    + exact (idtoiso_setoid_cat X Y).
    + intros p.
      induction p.
      use subtypeEquality.
      {
        intro.
        apply isaprop_is_iso.
      }
      reflexivity.
  - apply setoid_cat.
Defined.