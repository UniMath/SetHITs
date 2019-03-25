Require Import prelude.all.

Require Import syntax.hit_signature.
Require Import algebras.set_algebra.
Require Import displayed_algebras.displayed_algebra.

(**
Some operations needed for displayed algebras
 *)
Definition poly_dact_const
           (P : poly_code)
           {X Y : hSet}
           (x : ⦃ P ⦄ X)
  : poly_dact P (λ (z : X), Y) x → ⦃ P ⦄ Y.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (idfun _).
  - exact (idfun _).
  - induction x as [x | x].
    + exact (λ z, inl (IHP₁ x z)).
    + exact (λ z, inr (IHP₂ x z)).
  - exact (λ z, IHP₁ (pr1 x) (pr1 z) ,, IHP₂ (pr2 x) (pr2 z)).
Defined.

Definition poly_dmap_const
           (P : poly_code)
           {X Y : hSet}
           (x : ⦃ P ⦄ X)
           (f : X → Y)
  : poly_dact_const P x (poly_dmap P (λ (z : X), Y) f x)
    =
    #⦃ P ⦄ f x.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - reflexivity.
  - reflexivity.
  - induction x as [x | x].
    + simpl ; cbn.
      apply maponpaths.
      exact (IHP₁ x).
    + simpl ; cbn.
      apply maponpaths.
      exact (IHP₂ x).
  - apply pathsdirprod.
    + exact (IHP₁ (pr1 x)).
    + exact (IHP₂ (pr2 x)).
Qed.

Definition endpoint_dact_const
           {A : poly_code}
           (X Y : set_prealgebras A)
           {P Q : poly_code}
           (e : endpoint A P Q)
           {z : ⦃ P ⦄ (prealg_carrier X)}
           (y : poly_dact P (λ _ : prealg_carrier X, prealg_carrier Y) z)
  : poly_dact_const
      Q
      (set_endpoint e X z)
      (endpoint_dact X e
                     (λ x y, prealg_operation Y (poly_dact_const A x y))
                     y)
    =
    set_endpoint e Y (poly_dact_const P z y).
Proof.
  induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                  | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | ]
  ; try reflexivity.
  - simpl.
    exact (IHe₂ _ _ @ maponpaths _ (IHe₁ _ _)).
  - apply pathsdirprod.
    + apply IHe₁.
    + apply IHe₂.
Qed.  

Definition const_disp_algebra
           {Σ : hit_signature}
           (X Y : set_algebra Σ)
  : disp_algebra X.
Proof.
  use mk_disp_algebra.
  - intro.
    apply Y.
  - intros x z ; simpl in *.
    exact (alg_operation Y (poly_dact_const (point_arg Σ) x z)).
  - intros j x z ; simpl in *.
    rewrite transportf_const ; unfold idfun.
    exact ((endpoint_dact_const X Y (path_lhs Σ j) z)
             @ alg_paths Y j (poly_dact_const (path_arg Σ j) x z)
             @ !(endpoint_dact_const X Y (path_rhs Σ j) z)).
Defined.

Definition const_disp_alg_mor_to_alg_mor
           {Σ : hit_signature}
           (X Y : set_algebra Σ)
  : disp_algebra_map (const_disp_algebra X Y) → X --> Y.
Proof.
  intros f.
  use mk_algebra_map.
  - exact (pr1 f).
  - intros x ; simpl ; cbn.
    refine (pr2 f x @ _).
    cbn.
    apply maponpaths.
    apply poly_dmap_const.
Defined.