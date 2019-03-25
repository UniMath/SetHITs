Require Import prelude.all.

Require Import syntax.hit_signature.
Require Import algebras.set_algebra.

(**
Some operations needed for displayed algebras
 *)
Definition poly_dact
           (P : poly_code)
           {X : hSet}
           (Y : X → hSet)
  : ⦃ P ⦄ X → hSet.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (λ _, T).
  - exact Y.
  - intro x.
    induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (λ x, IHP₁ (pr1 x) × IHP₂ (pr2 x))%set.
Defined.

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

Definition poly_dmap
           (P : poly_code)
           {X : hSet}
           (Y : X → hSet)
           (f : ∏ (x : X), Y x)
  : ∏ (x : ⦃ P ⦄ X), poly_dact P Y x.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (idfun T).
  - exact f.
  - intros x.
    induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (λ x, IHP₁ (pr1 x) ,, IHP₂ (pr2 x)).
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

Definition poly_dmap_over
           (P : poly_code)
           {X : hSet}
           (Y : X → hSet)
           (g : X → X)
           (f : ∏ (x : X), Y (g x))
  : ∏ (x : ⦃ P ⦄ X), poly_dact P Y (#⦃ P ⦄ g x).
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - exact (idfun T).
  - exact f.
  - intros x.
    induction x as [x | x].
    + exact (IHP₁ x).
    + exact (IHP₂ x).
  - exact (λ x, IHP₁ (pr1 x) ,, IHP₂ (pr2 x)).
Defined.

Definition endpoint_dact
           {A : poly_code}
           (X : set_prealgebras A)
           {P Q : poly_code}
           (e : endpoint A P Q)
           {Y : prealg_carrier X → hSet}
           {z : ⦃ P ⦄ (prealg_carrier X)}
           (c : ∏ (x : ⦃ A ⦄ (prealg_carrier X)),
                   poly_dact A Y x → Y (prealg_operation X x))
  : poly_dact P Y z → poly_dact Q Y (set_endpoint e X z).
Proof.
  induction e as [ | P Q R e₁ IHe₁ e₂ IHe₂ | | | | | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | ].
  - exact (idfun _).
  - exact (λ x, IHe₂ (set_endpoint e₁ X z) (IHe₁ z x)).
  - exact (λ x, x).
  - exact (λ x, x).
  - exact pr1.
  - exact pr2.
  - exact (λ x, (IHe₁ z x ,, IHe₂ z x)).
  - exact (λ _, t).
  - exact (c z).
Defined.

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

(**
Definition of a displayed algebra
 *)
Definition displayed_algebra
           {Σ : hit_signature}
           (X : set_algebra Σ)
  : UU
  :=
    ∑ (Y : alg_carrier X → hSet)
      (c : ∏ (x : ⦃ point_arg Σ ⦄ (alg_carrier X)),
           poly_dact (point_arg Σ) Y x → Y (alg_operation X x)),
    ∏ (j : path_index Σ)
      (x : ⦃ path_arg Σ j ⦄ (alg_carrier X))
      (y : poly_dact (path_arg Σ j) Y x),
    transportf
      (poly_dact I Y)
      (alg_paths X j x)
      (endpoint_dact (alg_to_prealg X) (path_lhs Σ j) c y)
    =
    endpoint_dact (alg_to_prealg X) (path_rhs Σ j) c y.

(**
Projections
 *)
Definition disp_algebra_type_family
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : displayed_algebra X)
  : alg_carrier X → hSet
  := pr1 Y.

Coercion disp_algebra_type_family : displayed_algebra >-> Funclass.

Definition disp_alg_operator
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : displayed_algebra X)
  : ∏ (x : (⟦ point_arg Σ ⟧ (alg_carrier X)) : hSet),
    poly_dact (point_arg Σ) Y x → Y (alg_operator X x)
  := pr12 Y.

Definition const_disp_algebra
           {Σ : hit_signature}
           (X Y : set_algebra Σ)
  : displayed_algebra X.
Proof.
  use tpair.
  - intro.
    apply Y.
  - use tpair.
    + intros x z ; simpl in *.
      exact (alg_operator Y (poly_dact_const (point_arg Σ) x z)).
    + intros j x z ; simpl in *.
      rewrite transportf_const ; unfold idfun.
      exact ((endpoint_dact_const X Y (path_lhs Σ j) z)
              @ alg_paths Y j (poly_dact_const (path_arg Σ j) x z)
              @ !(endpoint_dact_const X Y (path_rhs Σ j) z)).
Defined.

Definition disp_algebra_map
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : displayed_algebra X)
  : UU
  := ∑ (f : ∏ (x : alg_carrier X), Y x),
     ∏ (x : (⟦ point_arg Σ ⟧ (alg_carrier X)) : hSet),
     f (alg_operator X x)
     =
     disp_alg_operator Y x (poly_dmap (point_arg Σ) Y f x).

Definition const_disp_alg_mor_to_alg_mor
           {Σ : hit_signature}
           (X Y : set_algebra Σ)
  : disp_algebra_map (const_disp_algebra X Y) → X --> Y.
Proof.
  intros f.
  use tpair.
  - use tpair.
    + exact (pr1 f).
    + use funextsec.
      intros x ; simpl ; cbn.
      refine (pr2 f x @ _).
      cbn.
      apply maponpaths.
      apply poly_dmap_const.
  - exact tt.
Defined.

(**
Definition of the total algebra. We first need two lemmata.
 *)
Definition poly_pr1
           (P : poly_code)
           {X : hSet}
           {Y : X → hSet}
  : (⟦ P ⟧ (total2_hSet Y) : hSet) → (⟦ P ⟧ X : hSet).
Proof.
  intro x.
  refine (#(⟦ P ⟧) _ x).
  exact pr1.
Defined.

Definition poly_pr1_I
           {X : hSet}
           {Y : X → hSet}
           (x : ⟦ I ⟧ (total2_hSet Y) : hSet)
  : poly_pr1 I x = pr1 x
  := idpath _.

Definition poly_pr2
           (P : poly_code)
           {X : hSet}
           (Y : X → hSet)
  : ∏ (x : ⟦ P ⟧ (total2_hSet Y) : hSet), poly_dact P Y (poly_pr1 P x).
Proof.
  intros x.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂] ; simpl in *.
  - exact x.
  - exact (pr2 x).
  - induction x as [x | x] ; simpl.
    + apply IHP₁.
    + apply IHP₂.
  - refine (_ ,, _).
    + apply IHP₁.
    + apply IHP₂.
Defined.

Definition transportf_is_transportb
           {X : UU}
           (Y : X → UU)
           {x₁ x₂ : X}
           (p : x₁ = x₂)
           (z : Y x₂)
  : transportb Y p z = transportf Y (!p) z
  := idpath _.

Definition endpoint_dact_transportf
           {P Q A : poly_code}
           (e : pt_endpoint A P Q)
           (X : HSET_prealgebras A)
           {Y : prealg_carrier X → hSet}
           (c : ∏ (x : (⟦ A ⟧ (prealg_carrier X)) : hSet),
                poly_dact A Y x → Y (prealg_operator X x))
           {z₁ z₂ : (⟦ P ⟧) (prealg_carrier X) : hSet}
           (p : z₁ = z₂)
           (x : poly_dact P Y z₁)
  : endpoint_dact X e c (transportf (poly_dact P Y) p x)
    =
    transportf
      (poly_dact Q Y)
      (maponpaths ((HSET_endpoint e) X) p)
      (endpoint_dact X e c x).
Proof.
  induction p.
  reflexivity.
Qed.

Section TotalAlgebra.
  Context {Σ : hit_signature}
          {X : set_algebra Σ}.
  Variable (Y : displayed_algebra X).

  Local Definition carrier
    : hSet
    := total2_hSet Y.

  Local Definition operation
    : ⟦ point_arg Σ ⟧ carrier --> carrier.
  Proof.
    intro x.
    simple refine (alg_operator X (#(⟦ point_arg Σ ⟧) _ x) ,, _).
    - exact pr1.
    - apply (pr12 Y (# (⟦ point_arg Σ ⟧) _ x)).
      apply poly_pr2.
  Defined.

  Local Definition total_prealgebra
    : HSET_prealgebras (point_arg Σ).
  Proof.
    use tpair.
    - exact carrier.
    - exact operation.
  Defined.

  Local Definition pr1_endpoint
        {P Q : poly_code}
        (e : pt_endpoint (point_arg Σ) P Q)
        (x : ⟦ P ⟧ carrier : hSet)
    : HSET_endpoint e _ (poly_pr1 P x) = poly_pr1 Q (HSET_endpoint e total_prealgebra x).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | ].
    - apply idpath.
    - exact (maponpaths _ (IHe₁ _) @ IHe₂ _).
    - apply idpath.
    - apply idpath.
    - apply idpath.
    - apply idpath.
    - exact (pathsdirprod (IHe₁ x) (IHe₂ x)).
    - apply idpath.
    - apply idpath.
  Defined.

  Local Definition pr2_endpoint
        {P Q : poly_code}
        (e : pt_endpoint (point_arg Σ) P Q)
        (x : ⟦ P ⟧ carrier : hSet)
    : endpoint_dact _ e (disp_alg_operator Y) (poly_pr2 P Y x)
      =
      transportf (poly_dact Q Y) (!(pr1_endpoint e _)) (poly_pr2 Q Y (HSET_endpoint e total_prealgebra x)).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | ]
    ; try apply idpath.
    - simpl.
      refine (_ @ _).
      {
        apply maponpaths.
        apply IHe₁.
      }
      refine (_ @ transportf_is_transportb (poly_dact R Y) (_ @ _) _).
      rewrite <- transport_b_b.
      unfold transportb.
      refine (!(_ @ _)).
      {
        apply maponpaths.
        exact (!(IHe₂ _)).
      }
      refine (!_).
      refine (_ @ transportf_is_transportb (poly_dact R Y) _ _).
      unfold transportb.
      refine (endpoint_dact_transportf _ _ _ _ _ @ _).
      apply (transportf_paths (poly_dact R Y)).
      exact (maponpathsinv0 ((HSET_endpoint e₂) (alg_to_prealg X)) (pr1_endpoint e₁ x)).
    - use total2_paths_f.
      + refine (IHe₁ x @ _).
        admit.
      + admit.
  Admitted.

  Local Definition pr2_endpoint'
        {P Q : poly_code}
        (e : pt_endpoint (point_arg Σ) P Q)
        (x : ⟦ P ⟧ carrier : hSet)
    : transportf (poly_dact Q Y) (pr1_endpoint e _) (endpoint_dact _ e (disp_alg_operator Y) (poly_pr2 P Y x))
      =
      poly_pr2 Q Y (HSET_endpoint e total_prealgebra x).
  Proof.
    refine (!_).
    apply (@transportf_transpose _ (poly_dact Q Y)).
    refine (!_).    
    apply pr2_endpoint.
  Qed.
  
  Local Definition paths
        (j : path_index Σ)
        (x : ⟦ path_arg Σ j ⟧ carrier : hSet)
    : (HSET_endpoint (path_lhs Σ j)) total_prealgebra x
      =
      (HSET_endpoint (path_rhs Σ j)) total_prealgebra x.
  Proof.
    use total2_paths_f.
    - refine (!(pr1_endpoint (path_lhs Σ j) x) @ _ @ pr1_endpoint (path_rhs Σ j) x).
      exact (alg_paths X j (poly_pr1 (path_arg Σ j) x)).
    - rewrite <- transport_f_f.
      rewrite <- transport_f_f.
      refine (_ @ _).
      {
        do 2 apply maponpaths.
        exact (!(pr2_endpoint (path_lhs Σ j) x)).
      }
      refine (_ @ _).
      {
        apply maponpaths.
        apply (pr22 Y j (poly_pr1 (path_arg Σ j) x)).
      }
      apply (pr2_endpoint' (path_rhs Σ j)).
  Qed.

  Definition total_algebra
    : set_algebra Σ.
  Proof.
    use tpair.
    - use tpair.
      + exact carrier.
      + exact operation.
    - exact paths.
  Defined.
End TotalAlgebra.

Section Projection.
  Context {Σ : hit_signature}
          {X : set_algebra Σ}.
  Variable (Y : displayed_algebra X).

  Definition projection
    : total_algebra Y --> X.
  Proof.
    use tpair.
    - use tpair.
      + exact pr1.
      + reflexivity.
    - exact tt.
  Defined.
End Projection.

Definition project_map
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : displayed_algebra X)
           (f : X --> total_algebra Y)
  : X --> X
  := f · projection Y.

Definition test
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : displayed_algebra X)
           (f : X --> total_algebra Y)
           (x : alg_carrier X)
  : Y (pr11 (project_map Y f) x)
  := pr2 (pr11 f x).
(*
Definition disp_algebra_map_over
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : displayed_algebra X)
           (g : X --> X)
  : UU
  := ∑ (f : ∏ (x : alg_carrier X), Y (pr11 g x)),
     ∏ (x : (⟦ point_arg Σ ⟧ (alg_carrier X)) : hSet),
     f (alg_operator X x)
     =
     transportb (pr1 Y)
                (eqtohomot (pr21 g) x)
                (disp_alg_operator Y
                                   (#(⟦ point_arg Σ ⟧)
                                     (pr11 g) x)
                                   (poly_dmap_over (point_arg Σ) Y (pr11 g) f x)).

Definition disp_algebra_map_over
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : displayed_algebra X)
           (g : X --> X)
  : UU.
Proof.
  refine (∑ (f : ∏ (x : alg_carrier X), Y (pr11 g x)),
     ∏ (x : (⟦ point_arg Σ ⟧ (alg_carrier X)) : hSet),
     f (alg_operator X x)
     =
     _).
  Check (disp_alg_operator Y).


Definition test2
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : displayed_algebra X)
  : disp_algebra_map_over Y (identity _)
    →
    disp_algebra_map Y.
Proof.
  intros f.
  use tpair.
  - exact (pr1 f).
  - intros x.
    refine (pr2 f x @ _).
    assert UU.
    {
      refine (eqtohomot pr21 (identity X) x = _).
      cbn.
      exact (idpath _).
      simpl.
    Search transportf isaset.
 *)