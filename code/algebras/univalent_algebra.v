(**
Here we show how to interpret the syntactic data in univalent categories.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.

Open Scope cat.

(**
We first show how to interpret all syntactic elements in precategories with a certain structure.
`F` is needed to interpret the constant polynomial, and `el` for the constant constructor term.
 *)
Section Semantics.
  Variable (C : category)
           (F : HSET ⟶ C)
           (prod_C : BinProducts C)
           (coprod_C : BinCoproducts C)
           (el : ∏ (T : hSet) (t : T) (G : C ⟶ C), G ⟹ constant_functor C C (F T)).
  
  Definition sem_poly
             (P : poly_code)
    : C ⟶ C.
  Proof.
    induction P as [T | | P IHP Q IHQ | P IHP Q IHQ].
    - exact (constant_functor _ _ (F T)).
    - exact (functor_identity C).
    - exact (BinCoproduct_of_functors _ _ coprod_C IHP IHQ).
    - exact (BinProduct_of_functors _ _ prod_C IHP IHQ).
  Defined.

  Local Notation "⟦ P ⟧" := (sem_poly P).

  Definition prealgebras
             (P : poly_code)
    : category
    := FunctorAlg (⟦ P ⟧).

  Definition prealgebra_carrier
             (P : poly_code)
    : prealgebras P ⟶ C
    := forget_algebras (⟦ P ⟧).

  Definition constr_nat_trans
             (P : poly_code)
    : prealgebra_carrier P ∙ (⟦ P ⟧) ⟹ prealgebra_carrier P ∙ (⟦ I ⟧).
  Proof.
    use make_nat_trans.
    - exact (alg_map _).
    - intros X Y f ; cbn in *.
      exact (!(pr2 f)).
  Defined.

  Definition sem_endpoint
             {A P Q : poly_code}
             (e : endpoint A P Q)
    : prealgebra_carrier A ∙ (⟦ P ⟧) ⟹ prealgebra_carrier A ∙ ⟦ Q ⟧.
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | X Y f | ].
    - exact (nat_trans_id _).
    - exact (nat_trans_comp _ _ _ IHe₁ IHe₂).
    - exact (pre_whisker _ (coproduct_nat_trans_in1 _ _ _ _ _)).
    - exact (pre_whisker _ (coproduct_nat_trans_in2 _ _ _ _ _)).
    - exact (pre_whisker _ (binproduct_nat_trans_pr1 _ _ _ _ _)).
    - exact (pre_whisker _ (binproduct_nat_trans_pr2 _ _ _ _ _)).
    - exact (pair_nat_trans _ IHe₁ IHe₂).
    - exact (pre_whisker _ (el _ t _)).
    - refine (pre_whisker _ _).
      use make_nat_trans.
      + exact (λ _, #F f).
      + intros Z₁ Z₂ g ; cbn.
        exact (id_left _ @ !(id_right _)).
    - exact (constr_nat_trans A).
  Defined.
End Semantics.

(**
We show this gives rise to a univalent category of prealgebras.
 *)
Definition univalent_prealgebras
           (C : univalent_category)
           (F : HSET ⟶ C)
           (prod_C : BinProducts C)
           (coprod_C : BinCoproducts C)
           (P : poly_code)
  : univalent_category.
Proof.
  use make_univalent_category.
  - use (prealgebras C) ; try assumption.
  - apply is_univalent_FunctorAlg.
    apply C.
Defined.

(**
Projections of prealgebras
 *)
Section PrealgebraProjections.
  Context {C : univalent_category}
          {F : HSET ⟶ C}
          {prod_C : BinProducts C}
          {coprod_C : BinCoproducts C}
          {P : poly_code}.
  Variable (X : univalent_prealgebras C F prod_C coprod_C P).

  Definition prealg_carrier
    : C
    := pr1 X.

  Definition prealg_operation
    : sem_poly C F prod_C coprod_C P (pr1 X) --> pr1 X
    := pr2 X.
End PrealgebraProjections.
