(**
Here we define the category of algebras.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.

Open Scope cat.

(**
We first show how to interpret all syntactic elements in precategories with a certain structure.
`F` is needed to interpret the constant polynomial, and `el` for the constant constructor term.
 *)
Section Semantics.
  Variable (C : precategory)
           (F : HSET ⟶ C)
           (prod_C : BinProducts C)
           (coprod_C : BinCoproducts C)
           (HC : has_homsets C)
           (el : ∏ (T : hSet) (t : T) (G : C ⟶ C), G ⟹ constant_functor C C (F T)).
  
  Definition sem_poly
             (P : poly_code)
    : C ⟶ C.
  Proof.
    induction P as [T | | P IHP Q IHQ | P IHP Q IHQ].
    - apply constant_functor.
      exact (F T).
    - exact (functor_identity C).
    - exact (BinCoproduct_of_functors _ _ coprod_C IHP IHQ).
    - exact (BinProduct_of_functors _ _ prod_C IHP IHQ).
  Defined.

  Local Notation "⟦ P ⟧" := (sem_poly P).

  Definition prealgebras
             (P : poly_code)
    : precategory.
  Proof.
    refine (FunctorAlg (⟦ P ⟧) _).
    apply HC.
  Defined.

  Definition prealgebra_carrier
             (P : poly_code)
    : prealgebras P ⟶ C
    := forget_algebras (⟦ P ⟧) _.

  Definition sem_endpoint
             {A P Q : poly_code}
             (e : endpoint A P Q)
    : prealgebra_carrier A ∙ (⟦ P ⟧) ⟹ prealgebra_carrier A ∙ ⟦ Q ⟧.
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | ].
    - exact (nat_trans_id _).
    - exact (nat_trans_comp _ _ _ IHe₁ IHe₂).
    - apply pre_whisker.
      apply coproduct_nat_trans_in1.
    - apply pre_whisker.
      apply coproduct_nat_trans_in2.
    - apply pre_whisker.
      apply binproduct_nat_trans_pr1.
    - apply pre_whisker.
      apply binproduct_nat_trans_pr2.
    - apply (pair_nat_trans _) ; assumption.
    - apply pre_whisker.
      apply el.
      exact t.
    - use mk_nat_trans.
      + intro X.
        exact (alg_map _ X).
      + intros X Y f ; cbn in *.
        exact (!(pr2 f)).
  Defined.
End Semantics.

(**
We show it is univalent.
 *)
Definition univalent_prealgebras
           (C : univalent_category)
           (F : HSET ⟶ C)
           (prod_C : BinProducts C)
           (coprod_C : BinCoproducts C)
           (P : poly_code)
  : univalent_category.
Proof.
  use mk_category.
  - use (prealgebras C) ; try assumption.
    apply C.
  - exact (is_univalent_FunctorAlg _ _).
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