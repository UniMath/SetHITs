(**
For the induction principle of HITs, we use the notion of displayed algebras.
 *)
Require Import prelude.all.

Require Import syntax.hit_signature.
Require Import algebras.set_algebra.

(**
Some operations needed to define displayed algebras
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

Definition endpoint_dact
           {A : poly_code}
           (X : set_prealgebras A)
           {P Q : poly_code}
           (e : endpoint A P Q)
           {Y : prealg_carrier X → hSet}
           (c : ∏ (x : ⦃ A ⦄ (prealg_carrier X)),
                   poly_dact A Y x → Y (prealg_operation X x))
  : ∏ {z : ⦃ P ⦄ (prealg_carrier X)}, poly_dact P Y z → poly_dact Q Y (set_endpoint e X z).
Proof.
  induction e as [ | P Q R e₁ IHe₁ e₂ IHe₂ | | | | | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | ].
  - exact (λ z, idfun _).
  - exact (λ z x, IHe₂ (set_endpoint e₁ X z) (IHe₁ z x)).
  - exact (λ z, idfun _).
  - exact (λ z, idfun _).
  - exact (λ z, pr1).
  - exact (λ z, pr2).
  - exact (λ z x, (IHe₁ z x ,, IHe₂ z x)).
  - exact (λ _ _, t).
  - exact c.
Defined.

(**
Definition of a displayed algebra
 *)
Definition disp_algebra
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
           (Y : disp_algebra X)
  : alg_carrier X → hSet
  := pr1 Y.

Coercion disp_algebra_type_family : disp_algebra >-> Funclass.

Section DispAlgebraProjections.
  Context {Σ : hit_signature}
          {X : set_algebra Σ}.
  Variable (Y : disp_algebra X).

  Definition disp_alg_operation
    : ∏ (x : ⦃ point_arg Σ ⦄ (alg_carrier X)),
      poly_dact (point_arg Σ) Y x → Y (alg_operation X x)
    := pr12 Y.

  Definition disp_alg_paths
    : ∏ (j : path_index Σ)
        (x : ⦃ path_arg Σ j ⦄ (alg_carrier X))
        (y : poly_dact (path_arg Σ j) Y x),
      transportf
        (poly_dact I Y)
        (alg_paths X j x)
        (endpoint_dact (alg_to_prealg X) (path_lhs Σ j) disp_alg_operation y)
      =
      endpoint_dact (alg_to_prealg X) (path_rhs Σ j) disp_alg_operation y
  := pr22 Y.
End DispAlgebraProjections.

(**
Builder
 *)
Definition mk_disp_algebra
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : alg_carrier X → hSet)
           (c : ∏ (x : ⦃ point_arg Σ ⦄ (alg_carrier X)),
                poly_dact (point_arg Σ) Y x → Y (alg_operation X x))
           (p : ∏ (j : path_index Σ)
                  (x : ⦃ path_arg Σ j ⦄ (alg_carrier X))
                  (y : poly_dact (path_arg Σ j) Y x),
                transportf
                  (poly_dact I Y)
                  (alg_paths X j x)
                  (endpoint_dact (alg_to_prealg X) (path_lhs Σ j) c y)
                =
                endpoint_dact (alg_to_prealg X) (path_rhs Σ j) c y)
  : disp_algebra X
  := (Y ,, (c ,, p)).

(**
Operation necessary to define sections
 *)
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

(**
Maps to a displayed algebra (sections of the display map)
 *)
Definition disp_algebra_map
           {Σ : hit_signature}
           {X : set_algebra Σ}
           (Y : disp_algebra X)
  : UU
  := ∑ (f : ∏ (x : alg_carrier X), Y x),
     ∏ (x : ⦃ point_arg Σ ⦄ (alg_carrier X)),
     f (alg_operation X x)
     =
     disp_alg_operation Y x (poly_dmap (point_arg Σ) Y f x).