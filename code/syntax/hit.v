Require Import prelude.all.

Require Import syntax.hit_signature.
Require Import algebras.set_algebra.
Require Import displayed_algebras.displayed_algebra.

Open Scope cat.

Definition is_a_HIT
           {Σ : hit_signature}
           (X : set_algebra Σ)
  : UU
  := ∏ (Y : disp_algebra X), disp_algebra_map Y.

Definition HIT
           (Σ : hit_signature)
  : UU
  := ∑ (X : set_algebra Σ), is_a_HIT X.

Coercion HIT_carrier
         {Σ : hit_signature}
         (H : HIT Σ)
  : set_algebra Σ
  := pr1 H.

Section HITInd.
  Context {Σ : hit_signature}.
  Variable (H : HIT Σ)
           (Yfam : alg_carrier H → UU)
           (Yset : ∏ (x : alg_carrier H), isaset (Yfam x)).

  Local Definition Y : alg_carrier H → hSet
    := λ X, hSetpair (Yfam X) (Yset X).

  Variable (c : ∏ (x : ⦃ point_arg Σ ⦄ (alg_carrier H)),
                poly_dact (point_arg Σ) Y x → Y (alg_operation H x))
           (p : ∏ (j : path_index Σ)
                  (x : ⦃ path_arg Σ j ⦄ (alg_carrier H))
                  (y : poly_dact (path_arg Σ j) Y x),
                transportf
                  (poly_dact I Y)
                  (alg_paths H j x)
                  (endpoint_dact (alg_to_prealg H) (path_lhs Σ j) c y)
                =
                endpoint_dact (alg_to_prealg H) (path_rhs Σ j) c y).
  
  Definition hit_ind
    : ∏ (x : alg_carrier H), Y x
    := pr1 (pr2 H (Y ,, (c ,, p))).
End HITInd.