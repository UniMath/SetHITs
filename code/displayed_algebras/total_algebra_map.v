Require Import prelude.all.

Require Import syntax.hit_signature.
Require Import algebras.set_algebra.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.total_algebra.

Definition test
           {P : poly_code}
           {A : hSet}
           (Y : A → hSet)
           (c : ⦃ P ⦄ A → A)
           (cY : ∏ (x : ⦃ P ⦄ A), poly_dact P Y x → Y (c x))
           {a₁ a₂ : ⦃ P ⦄ A}
           (p : a₁ = a₂)
           (y : poly_dact P Y a₁)
  : cY a₁ y
    =
    transportb Y (maponpaths c p) (cY a₂ (transportf (poly_dact P Y) p y)).
Proof.
  induction p ; simpl.
  reflexivity.
Qed.

Definition help
           {P : poly_code}
           {X : hSet}
           (x : ⦃ P ⦄ X)
           (f : X → X)
           (p : f = idfun X)
  : x = #⦃ P ⦄ f x.
Proof.
  rewrite p.
  rewrite (functor_id (⦃ P ⦄)).
  reflexivity.
Qed.

Definition transport_test
           {X : hSet}
           (Y : X → UU)
           {x₁ x₂ x₃ : X}
           (p₁ : x₁ = x₃)
           (p₂ : x₂ = x₃)
           {y₁ : Y x₁}
           {y₂ : Y x₂}
           (q : y₁ = transportf Y (p₂ @ ! p₁) y₂)
  : transportf Y p₁ y₁ = transportf Y p₂ y₂.
Proof.
  refine (!_).
  apply transportf_transpose.
  unfold transportb.
  rewrite transport_f_f.
  exact (!q).
Qed.

Definition transport_test2
           {X : hSet}
           (Y : X → UU)
           {x₁ x₂ : X}
           (p₁ p₂ : x₁ = x₂)
           {y₁ y₂ : Y x₁}
           (q : y₁ = y₂)
  : transportf Y p₁ y₁ = transportf Y p₂ y₂.
Proof.
  apply transport_test.
  refine (!_).
  refine (transportf_set _ _ _ _ @ !q).
  apply X.
Qed.

Definition fiber_paths_b
           {A : UU}
           {B : A → UU}
           {u v : ∑ (x : A), B x}
           (p : u = v)
  : pr2 u = transportb (λ x, B x) (base_paths u v p) (pr2 v).
Proof.
  apply transportf_transpose.
  unfold transportb.
  refine (_ @ fiber_paths p).
  apply transportf_paths.
  apply pathsinv0inv0.
Qed.

Definition test3
           (P : poly_code)
           {X : hSet}
           (Y : X → hSet)
           (f : X → total2_hSet Y)
           (x : ⦃ P ⦄ X)
           (p : (λ z, pr1(f z)) = idfun X)
  : poly_pr2 P Y (#⦃ P ⦄ f x)
    =
    transportf (poly_dact P Y)
               (eqtohomot (!(functor_id (⦃ P ⦄) X)) x
                          @ eqtohomot (maponpaths (#⦃ P ⦄) (!p)) x
                          @ eqtohomot (functor_comp (⦃ P ⦄) _ _) x)
               (poly_dmap P Y (λ z, transportf Y (eqtohomot p z) (pr2 (f z))) _).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - simpl.
    rewrite transportf_const.
    reflexivity.
  - simpl.
    rewrite transport_f_f.
    rewrite transportf_set.
    + reflexivity.
    + apply X.
  - induction x as [x | x].
    + refine (IHP₁ x @ _).
      refine (!(transport_inl (poly_dact P₁ Y) (poly_dact P₂ Y) _ _) @ _).
      apply (@transportf_paths
               _
               (sum_hset_fam (poly_dact P₁ Y) (poly_dact P₂ Y))
               (inl x)
               (inl (#⦃ P₁ ⦄ (pr1 : HSET ⟦ total2_hSet Y , X ⟧) (#⦃ P₁ ⦄ f x)))
            ).
      apply setcoprod.
    + refine (IHP₂ x @ _).
      refine (!(transport_inr (poly_dact P₁ Y) (poly_dact P₂ Y) _ _) @ _).
      apply (@transportf_paths
               _
               (sum_hset_fam (poly_dact P₁ Y) (poly_dact P₂ Y))
               (inr x)
               (inr (#⦃ P₂ ⦄ (pr1 : HSET ⟦ total2_hSet Y , X ⟧) (#⦃ P₂ ⦄ f x)))
            ).
      apply setcoprod.
  - induction x as [x₁ x₂].
    apply dirprod_paths.
    + refine (IHP₁ x₁ @ _).
      refine (_ @ !(@transport_pr1
                      _
                      _
                      (poly_dact P₁ Y)
                      (poly_dact P₂ Y)
                      (x₁ ,, x₂)
                      (#⦃ P₁ ⦄ (pr1 : HSET ⟦ total2_hSet Y , X ⟧) (#⦃ P₁ ⦄ f x₁)
                        ,,
                        #⦃ P₂ ⦄ (pr1 : HSET ⟦ total2_hSet Y , X ⟧) (#⦃ P₂ ⦄ f x₂))
                      _
                      _)).
      apply (transportf_paths (poly_dact P₁ Y)).
      apply (⦃ P₁ ⦄ X).
    + refine (IHP₂ x₂ @ _).
      refine (_ @ !(@transport_pr2
                      _
                      _
                      (poly_dact P₁ Y)
                      (poly_dact P₂ Y)
                      (x₁ ,, x₂)
                      (#⦃ P₁ ⦄ (pr1 : HSET ⟦ total2_hSet Y , X ⟧) (#⦃ P₁ ⦄ f x₁)
                        ,,
                        #⦃ P₂ ⦄ (pr1 : HSET ⟦ total2_hSet Y , X ⟧) (#⦃ P₂ ⦄ f x₂))
                      _
                      _)).
      apply (transportf_paths (poly_dact P₂ Y)).
      apply (⦃ P₂ ⦄ X).
Qed.

Section TotalAlgebraMap.
  Context {Σ : hit_signature}
          {X : set_algebra Σ}.
  Variable (Y : disp_algebra X)
           (f : X --> total_algebra Y)
           (p : f · projection Y = identity X).

  Definition test2
    : disp_algebra_map Y.
  Proof.
    use tpair.
    - exact (λ x, transportf
                    (pr1 Y)
                    (eqtohomot (maponpaths pr1 (maponpaths pr1 p)) x)
                    (pr2 (pr11 f x))).
    - intros x.
      refine (_ @ _).
      {
        apply maponpaths.
        exact (fiber_paths_b (eqtohomot (pr21 f) x)).
      }
      unfold transportb.
      rewrite transport_f_f.
      simpl ; cbn.
      refine (_ @ _).
      {
        apply maponpaths.
        refine (test (pr1 Y) _ (pr12 Y) _ _).
        refine (eqtohomot (!(functor_comp (⦃ point_arg Σ⦄) _ _)) x @ _).
        refine (_ @ _).
        {
          apply maponpaths_2.
          apply (maponpaths pr1 (maponpaths pr1 p)).
        }
        apply (eqtohomot (functor_id (⦃ point_arg Σ ⦄) _) x).
      }
      simpl.
      unfold transportb.
      rewrite transport_f_f.
      simple refine (_
                       @
                       !(test (pr1 Y) (pr21 X) (pr12 Y)
                              (help x (pr11 (f · projection Y)) (maponpaths pr1 (maponpaths pr1 p))) _)).
      unfold transportb.
      use transport_test.
      refine (!_).
      refine (_ @ _).
      {
        apply maponpaths.
        refine (test (pr1 Y) _ (pr12 Y) _ _).
        refine (_ @ _).
        {
          apply maponpaths_2.
          apply (maponpaths pr1 (maponpaths pr1 p)).
        }
        apply (eqtohomot (functor_id (⦃ point_arg Σ ⦄) _) x).
      }
      unfold transportb.
      rewrite !transport_f_f.
      refine (!_).
      refine (_ @ _).
      {
        do 2 apply maponpaths.
        refine (test3 _ _ _ _ _).
        exact (maponpaths pr1 (maponpaths pr1 p)).
      }
      simpl.
      rewrite transport_f_f.
      refine (!_).
      rewrite transportf_set.
      + apply maponpaths.
        simpl ; cbn.
        apply (transport_test2 (poly_dact (point_arg Σ) Y)).
        reflexivity.
      + apply (alg_carrier X).
  Qed.
End TotalAlgebraMap.