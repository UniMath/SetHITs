(**
Let `X` be an algebra and let `Y` be an displayed algebra over `X`.
Denote the total algebra of `Y` by `E`.
Note that we always have the projectio `p : E --> X`.
In this file, we map sections of `p` to displayed algebra maps from `X` to `Y`
 *)
Require Import prelude.all.

Require Import syntax.hit_signature.
Require Import algebras.set_algebra.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.total_algebra.

(** We first show operations of displayed algebras commute with transports *)
Definition transportb_disp_alg_operator
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
  induction p.
  reflexivity.
Qed.

(** Next we compute `poly_pr2` composed with the action of the functor *)
Definition poly_pr2_fmap
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
               (poly_dmap P Y (λ z, transportf Y (eqtohomot p z) (pr2 (f z))) x).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; simpl.
  - rewrite transportf_const.
    reflexivity.
  - rewrite transport_f_f.
    rewrite transportf_set.
    + reflexivity.
    + apply X.
  - induction x as [x | x].
    + refine (IHP₁ x @ _).
      refine (!(transportf_inl (poly_dact P₁ Y) (poly_dact P₂ Y) _ _) @ _).
      apply (transportf_paths (sum_hset_fam (poly_dact P₁ Y) (poly_dact P₂ Y))).
      apply setcoprod.
    + refine (IHP₂ x @ _).
      refine (!(transportf_inr (poly_dact P₁ Y) (poly_dact P₂ Y) _ _) @ _).
      apply (transportf_paths (sum_hset_fam (poly_dact P₁ Y) (poly_dact P₂ Y))).
      apply setcoprod.
  - induction x as [x₁ x₂].
    apply dirprod_paths.
    + refine (IHP₁ x₁ @ _).
      refine (_ @ !(transportf_pr1 _ (#⦃ P₁ ⦄ _ _ ,, #⦃ P₂ ⦄ _ _) _ _)).
      apply (transportf_paths (poly_dact P₁ Y)).
      apply setproperty.
    + refine (IHP₂ x₂ @ _).
      refine (_ @ !(transportf_pr2 _ (#⦃ P₁ ⦄ _ _ ,, #⦃ P₂ ⦄ _ _) _ _)).
      apply (transportf_paths (poly_dact P₂ Y)).
      apply setproperty.
Qed.

(** Lemma *)
Definition functor_fid
           {P : poly_code}
           {X : hSet}
           {x : ⦃ P ⦄ X}
           {f : X → X}
           (p : f = idfun X)
  : x = #⦃ P ⦄ f x.
Proof.
  rewrite p.
  rewrite (functor_id (⦃ P ⦄)).
  reflexivity.
Qed.

(** Now we show that a section of the projection gives rise to a dependent map to `Y` *)
Definition section_to_disp_alg_map
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : disp_algebra X)
           (f : X --> total_algebra Y)
           (p : f · projection Y = identity X)
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
      refine (transportb_disp_alg_operator (pr1 Y) _ (pr12 Y) _ _).
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
    simple refine (_ @ !(transportb_disp_alg_operator
                           _ _ _
                           (functor_fid (maponpaths pr1 (maponpaths pr1 p)))
                           _)).
    unfold transportb.
    use transportf_paths_2.
    refine (!_).
    refine (_ @ _).
    {
      apply maponpaths.
      refine (transportb_disp_alg_operator (pr1 Y) _ (pr12 Y) _ _).
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
      refine (poly_pr2_fmap _ _ _ _ _).
      exact (maponpaths pr1 (maponpaths pr1 p)).
    }
    simpl.
    rewrite transport_f_f.
    refine (!_).
    rewrite transportf_set.
    + apply maponpaths.
      apply (transportf_paths_3 (poly_dact (point_arg Σ) Y)).
      reflexivity.
    + apply setproperty.
Qed.
