(**
Here we define the total algebra of a displayed algebra.
The object of this algebra are dependent pairs.
 *)
Require Import prelude.all.

Require Import syntax.hit_signature.
Require Import algebras.set_algebra.
Require Import displayed_algebras.displayed_algebra.

(**
We first look at the first and second projection of a polynomial applied to a total type
 *)
Definition poly_pr1
           (P : poly_code)
           {X : hSet}
           {Y : X → hSet}
  : ⦃ P ⦄ (total2_hSet Y) → ⦃ P ⦄ X
  := #⦃ P ⦄ (pr1 : HSET⟦ total2_hSet Y , X ⟧).

Definition poly_pr1_I
           {X : hSet}
           {Y : X → hSet}
           (x : ⦃ I ⦄ (total2_hSet Y))
  : poly_pr1 I x = pr1 x
  := idpath _.

Definition poly_pr2
           (P : poly_code)
           {X : hSet}
           (Y : X → hSet)
  : ∏ (x : ⦃ P ⦄ (total2_hSet Y)), poly_dact P Y (poly_pr1 P x).
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

Definition endpoint_dact_transportf
           {P Q A : poly_code}
           (e : endpoint A P Q)
           (X : set_prealgebras A)
           {Y : prealg_carrier X → hSet}
           (c : ∏ (x : ⦃ A ⦄ (prealg_carrier X)),
                poly_dact A Y x → Y (prealg_operation X x))
           {z₁ z₂ : ⦃ P ⦄ (prealg_carrier X)}
           (p : z₁ = z₂)
           (x : poly_dact P Y z₁)
  : endpoint_dact X e c (transportf (poly_dact P Y) p x)
    =
    transportf
      (poly_dact Q Y)
      (maponpaths ((set_endpoint e) X) p)
      (endpoint_dact X e c x).
Proof.
  induction p.
  reflexivity.
Qed.

(**
Now we define the total algebra
 *)
Section TotalAlgebra.
  Context {Σ : hit_signature}
          {X : set_algebra Σ}.
  Variable (Y : disp_algebra X).

  Local Definition carrier
    : hSet
    := total2_hSet Y.

  Local Definition operation
    : ⦃ point_arg Σ ⦄ carrier → carrier.
  Proof.
    intro x.
    simple refine (alg_operation X (#⦃ point_arg Σ ⦄ _ x) ,, _).
    - exact pr1.
    - apply (disp_alg_operation Y (#⦃ point_arg Σ ⦄ _ x)).
      apply poly_pr2.
  Defined.

  Local Definition total_prealgebra
    : set_prealgebras (point_arg Σ).
  Proof.
    use tpair.
    - exact carrier.
    - exact operation.
  Defined.

  (** For the paths, we first need to look at the first and second projections of endpoints *)
  Local Definition pr1_endpoint
        {P Q : poly_code}
        (e : endpoint (point_arg Σ) P Q)
        (x : ⦃ P ⦄ carrier)
    : set_endpoint e _ (poly_pr1 P x)
      =
      poly_pr1 Q (set_endpoint e total_prealgebra x).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | ]
    ; try (apply idpath).
    - exact (maponpaths _ (IHe₁ _) @ IHe₂ _).
    - exact (pathsdirprod (IHe₁ x) (IHe₂ x)).
  Defined.

  Local Definition pr2_endpoint
        {P Q : poly_code}
        (e : endpoint (point_arg Σ) P Q)
        (x : ⦃ P ⦄ carrier)
    : endpoint_dact _ e (disp_alg_operation Y) (poly_pr2 P Y x)
      =
      transportf
        (poly_dact Q Y)
        (!(pr1_endpoint e _))
        (poly_pr2 Q Y (set_endpoint e total_prealgebra x)).
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | ]
    ; try (apply idpath).
    - simpl.
      refine (_ @ _).
      {
        apply maponpaths.
        apply IHe₁.
      }
      refine (_ @ transportf_is_transportb (poly_dact R Y) (_ @ _) _).
      rewrite <- transport_b_b.
      refine (!(_ @ _)).
      {
        apply maponpaths.
        exact (!(IHe₂ _)).
      }
      refine (!_).
      refine (endpoint_dact_transportf _ _ _ _ _ @ _).
      apply (transportf_paths (poly_dact R Y)).
      exact (maponpathsinv0 ((set_endpoint e₂) (alg_to_prealg X)) (pr1_endpoint e₁ x)).
    - use dirprod_paths.
      + refine (IHe₁ x @ _).
        pose (@transportf_pr1
                _
                _
                (poly_dact Q Y) (poly_dact R Y)
                (#⦃ Q ⦄ (pr1 : HSET ⟦ carrier , _ ⟧) ((set_endpoint e₁) total_prealgebra x)
                  ,,
                  #⦃ R ⦄ (pr1 : HSET ⟦ carrier , _ ⟧) ((set_endpoint e₂) total_prealgebra x))
                ((set_endpoint e₁ (alg_to_prealg X) (# (⦃ P ⦄) (pr1 : HSET ⟦ carrier , _ ⟧) x))
                   ,,
                   set_endpoint e₂ (alg_to_prealg X) (# (⦃ P ⦄) (pr1 : HSET ⟦ carrier , _ ⟧) x))
             ) as q.
        refine (_ @ !(q _ _)).
        apply (transportf_paths (poly_dact Q Y)).
        apply (⦃ Q ⦄ _).
      + refine (IHe₂ x @ _).
        pose (@transportf_pr2
                _
                _
                (poly_dact Q Y) (poly_dact R Y)
                (#⦃ Q ⦄ (pr1 : HSET ⟦ carrier , _ ⟧) ((set_endpoint e₁) total_prealgebra x)
                  ,,
                  #⦃ R ⦄ (pr1 : HSET ⟦ carrier , _ ⟧) ((set_endpoint e₂) total_prealgebra x))
                ((set_endpoint e₁ (alg_to_prealg X) (# (⦃ P ⦄) (pr1 : HSET ⟦ carrier , _ ⟧) x))
                   ,,
                   set_endpoint e₂ (alg_to_prealg X) (# (⦃ P ⦄) (pr1 : HSET ⟦ carrier , _ ⟧) x))
             ) as q.
        refine (_ @ !(q _ _)).
        apply (transportf_paths (poly_dact R Y)).
        apply (⦃ R ⦄ _).
  Qed.

  Local Definition pr2_endpoint'
        {P Q : poly_code}
        (e : endpoint (point_arg Σ) P Q)
        (x : ⦃ P ⦄ carrier)
    : transportf
        (poly_dact Q Y)
        (pr1_endpoint e _)
        (endpoint_dact _ e (disp_alg_operation Y) (poly_pr2 P Y x))
      =
      poly_pr2 Q Y (set_endpoint e total_prealgebra x).
  Proof.
    refine (!_).
    apply (@transportf_transpose _ (poly_dact Q Y)).
    refine (!_).    
    apply pr2_endpoint.
  Qed.
  
  Local Definition paths
        (j : path_index Σ)
        (x : ⦃ path_arg Σ j ⦄ carrier)
    : set_endpoint (path_lhs Σ j) total_prealgebra x
      =
      set_endpoint (path_rhs Σ j) total_prealgebra x.
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
    use mk_algebra.
    - exact carrier.
    - exact operation.
    - exact paths.
  Defined.
End TotalAlgebra.

(**
We can project the total algebra on `X`.
 *)
Section Projection.
  Context {Σ : hit_signature}
          {X : set_algebra Σ}.
  Variable (Y : disp_algebra X).

  Definition projection
    : total_algebra Y --> X.
  Proof.
    use mk_algebra_map.
    - exact pr1.
    - reflexivity.
  Defined.
End Projection.