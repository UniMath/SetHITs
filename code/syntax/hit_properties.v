(**
Some properties of higher inductive types
 *)
Require Import prelude.all.

Require Import syntax.hit_signature.
Require Import algebras.set_algebra.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.constant_display.
Require Import syntax.hit.

Open Scope cat.

(**
HIT induction on families of propositions
 *)
Section HITIndProp.
  Context {Σ : hit_signature}.
  Variable (H : HIT Σ)
           (Yfam : alg_carrier H → UU)
           (Yprop : ∏ (x : alg_carrier H), isaprop (Yfam x)).

  Local Definition Y : alg_carrier H → hSet
    := λ X, hSetpair (Yfam X) (isasetaprop (Yprop X)).

  Variable (c : ∏ (x : ⦃ point_arg Σ ⦄ (alg_carrier H)),
                poly_dact (point_arg Σ) Y x → Y (alg_operation H x)).

  Definition hit_ind_prop
    : ∏ (x : alg_carrier H), Y x.
  Proof.
    use hit_ind.
    - exact c.
    - intros.
      apply Yprop.
  Defined.    
End HITIndProp.

(**
HIT recursion.
 *)
Section HITRec.
  Context {Σ : hit_signature}.
  Variable (H : HIT Σ)
           (Y : set_algebra Σ).

  Definition hit_rec
    : H --> Y
    := const_disp_alg_mor_to_alg_mor H Y (pr2 H _).
End HITRec.

(**
Lemma to obtain the uniqueness of maps
 *)
Definition poly_dact_eq
           {P : poly_code}
           {X Y : hSet}
           {f g : X → Y}
           (x : ⦃ P ⦄ X)
           (p : poly_dact P (λ z, hProp_to_hSet (eqset (f z) (g z))) x)
  : #⦃ P ⦄ f x = #⦃ P ⦄ g x.
Proof.
  induction P as [T | | P₁ IHP₁ P₂ IHP₂ | P₁ IHP₁ P₂ IHP₂].
  - reflexivity.
  - exact p.
  - induction x as [x | x].
    + exact (maponpaths inl (IHP₁ x p)).
    + exact (maponpaths inr (IHP₂ x p)).
  - apply pathsdirprod.
    + exact (IHP₁ (pr1 x) (pr1 p)).
    + exact (IHP₂ (pr2 x) (pr2 p)).
Qed.

(**
Algebra homorphisms on HITs are unique
 *)
Section HITUnique.
  Context {Σ : hit_signature}.
  Variable (H : HIT Σ)
           (Y : set_algebra Σ)
           (f₁ f₂ : H --> Y).

  Definition hit_eq
    : f₁ = f₂.
  Proof.
    use subtypeEquality.
    { intro ; apply isapropunit. }
    use subtypeEquality.
    { intro ; apply isaset_set_fun_space. }
    simpl.
    use funextsec.
    intro x ; revert x.
    use hit_ind_prop.
    {
      intro.
      apply (pr11 Y).
    }
    intros x p ; simpl.
    refine (eqtohomot (pr21 f₁) x @ _ @ !(eqtohomot (pr21 f₂) x)).
    cbn.
    apply maponpaths.
    apply poly_dact_eq.
    apply p.
  Qed.
End HITUnique.

(**
HITs are initial objects
 *)
Definition HIT_is_initial
           {Σ : hit_signature}
           (H : HIT Σ)
  : isInitial _ H.
Proof.
  intros X.
  use tpair.
  - exact (const_disp_alg_mor_to_alg_mor H X (pr2 H _)).
  - intro.
    apply hit_eq.
Qed.

(**
HITs are unique
 *)
Definition hit_unique
           {Σ : hit_signature}
           (H₁ H₂ : HIT Σ)
  : HIT_carrier H₁ = HIT_carrier H₂.
Proof.
  apply isotoid.
  {
    apply set_algebra.
  }
  apply initial_iso ; apply HIT_is_initial.
Defined.






(*
Definition is_initial_is_a_HIT
           {Σ : hit_signature}
           (H : set_algebra Σ)
  : isInitial _ H → is_a_HIT H.
Proof.
  admit.
Admitted.

Definition initial_to_HIT
           {Σ : hit_signature}
           (H : Initial (set_algebra Σ))
  : HIT Σ.
Proof.
  use tpair.
  - apply H.
  - apply is_initial_is_a_HIT.
    apply H.
Defined.

(**
Projections
 *)

(**
Note that HITs can be constructed from quotients if we have an initial setoid algebra.
 *)
Lemma HIT_existence_from_quotient
      (Σ : hit_signature)
      (X : Initial (setoid_algebra Σ))
  : HIT Σ.
Proof.
  apply initial_to_HIT.
  use tpair.
  - exact (quotient_algebra Σ (InitialObject X)).
  - exact (adj_initial (quotient_algebra_adjunction Σ) (InitialObject X) (pr2 X)).
Defined.
*)