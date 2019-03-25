(**
Here we define the category of groups using the mechanism of algebras.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import syntax.hit.
Require Import syntax.hit_properties.
Require Import algebras.univalent_algebra.
Require Import algebras.set_algebra.
Require Import existence.hit_existence.

Definition TODO {A : UU} : A.
Admitted.

(**
Construction of the free algebra
 *)
Section FreeAlgebra.
  Variable (Σ : hit_signature).

  Local Notation P := (point_arg Σ).
  Local Notation J := (path_index Σ).
  Local Notation Q j := (path_arg Σ j).
  Local Notation l j := (path_lhs Σ j).
  Local Notation r j := (path_rhs Σ j).

  (** The signature *)  
  Definition free_point_arg
             (A : hSet)
    : poly_code
    := C A + P.

  Definition free_endpoint
             {R₁ R₂ : poly_code}
             (e : endpoint P R₁ R₂)
             (A : hSet)
    : endpoint (free_point_arg A) R₁ R₂.
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | ].
    - exact (id_e _ P).
    - exact (comp IHe₁ IHe₂).
    - exact (ι₁ P Q).
    - exact (ι₂ P Q).
    - exact (π₁ P Q).
    - exact (π₂ P Q).
    - exact (pair IHe₁ IHe₂).
    - exact (c P t).
    - exact (comp (ι₂ (C A) P) constr).
  Defined.

  Definition free_signature (A : hSet)
    : hit_signature.
  Proof.
    use tpair.
    - exact (free_point_arg A).
    - use tpair.
      + apply Σ.
      + use tpair.
        * exact (λ j, Q j).
        * split.
          ** exact (λ j, free_endpoint (l j) A).
          ** exact (λ j, free_endpoint (r j) A).
  Defined.

  (** Projections *)
  Definition free_alg_to_alg_carrier
             {A : hSet}
             (X : set_algebra (free_signature A))
    : hSet
    := alg_carrier X.

  Definition free_alg_to_alg_operation
             {A : hSet}
             (X : set_algebra (free_signature A))
    : ⦃ point_arg Σ ⦄ (free_alg_to_alg_carrier X) → free_alg_to_alg_carrier X
    := λ x, alg_operation X (inr x).

  Definition free_alg_to_alg_prealg
             {A : hSet}
             (X : set_algebra (free_signature A))
    : set_prealgebras (point_arg Σ).
  Proof.
    use tpair.
    - exact (free_alg_to_alg_carrier X).
    - exact (free_alg_to_alg_operation X).
  Defined.

  (** Lemma to get underlying `Σ`-algebra *)
  Definition free_alg_to_alg_endpoint
             {A : hSet}
             (X : set_algebra (free_signature A))
             {R₁ R₂ : poly_code}
             (e : endpoint (point_arg Σ) R₁ R₂)
             (x : ⦃ R₁ ⦄ (free_alg_to_alg_carrier X))
    : set_endpoint e (free_alg_to_alg_prealg X) x
      =
      set_endpoint (free_endpoint e A) (alg_to_prealg X) x.
  Proof.
    induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                    | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | ]
    ; try reflexivity ; simpl ; cbn.
    - exact (maponpaths _ (IHe₁ x) @ IHe₂ _).
    - apply pathsdirprod.
      + apply IHe₁.
      + apply IHe₂.
  Qed.

  Definition free_alg_to_alg
             {A : hSet}
             (X : set_algebra (free_signature A))
    : set_algebra Σ.
  Proof.
    use mk_algebra.
    - exact (free_alg_to_alg_carrier X).
    - exact (free_alg_to_alg_operation X).
    - intros j x ; simpl.
      exact ((free_alg_to_alg_endpoint X (l j) x)
               @ alg_paths X j x
               @ !(free_alg_to_alg_endpoint X (r j) x)).
  Defined.

  (** Next we show this gives rise to a functor *)
  Definition free_algebra_help
             (A : hSet)
    : set_algebra (free_signature A)
    := HIT_exists (free_signature A).

  Definition free_algebra
             (A : hSet)
    : set_algebra Σ
    := free_alg_to_alg (free_algebra_help A).

  (** Projections of maps on the free signature *)
  Definition free_signature_map
             (A : hSet)
             {X Y : set_algebra (free_signature A)}
             (f : X --> Y)
    : free_alg_to_alg X --> free_alg_to_alg Y.
  Proof.
    use mk_algebra_map.
    - apply f.
    - intros x ; simpl in *.
      exact (eqtohomot (pr21 f) (inr x)).
  Defined.

  (** Action of free algebra functo on maps. *)
  Section FreeAlgebraMap.
    Context {A B : hSet}.
    Variable (f : A → B).

    (** The map is defined by recursion. *)
    Section LiftAlgebra.
      Variable (X : set_algebra (free_signature B)).

      Definition free_algebra_map_lift_carrier
        : hSet
        := alg_carrier X.

      Definition free_algebra_map_lift_operation
        : ⦃ free_point_arg A ⦄ free_algebra_map_lift_carrier → free_algebra_map_lift_carrier.
      Proof.
        intros x.
        apply (alg_operation X).
        induction x as [x | x].
        + exact (inl (f x)).
        + exact (inr x).
      Defined.

      Definition free_algebra_map_lift_prealg
        : set_prealgebras (free_point_arg A).
      Proof.
        use tpair.
        - exact free_algebra_map_lift_carrier.
        - exact (free_algebra_map_lift_operation).
      Defined.

      Definition lift_endpoint
                 {P Q : poly_code}
                 (e : endpoint (point_arg Σ) P Q)
                 (x : ⦃ P ⦄ free_algebra_map_lift_carrier)
        : set_endpoint (free_endpoint e A) free_algebra_map_lift_prealg x
          =
          set_endpoint (free_endpoint e B) (alg_to_prealg X) x.
      Proof.
        induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                        | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | ]
        ; try reflexivity.
      Admitted.

      Definition free_algebra_map_help
        : set_algebra (free_signature A).
      Proof.
        use mk_algebra.
        - exact free_algebra_map_lift_carrier.
        - exact free_algebra_map_lift_operation.
        - intros j x ; simpl.
          exact ((lift_endpoint (path_lhs Σ j) x)
                    @ alg_paths X j x
                    @ !(lift_endpoint (path_rhs Σ j) x)).
      Defined.
    End LiftAlgebra.

    Definition free_algebra_map
      : free_algebra A --> free_algebra B.
    Proof.
      exact (free_signature_map _ (hit_rec (HIT_exists (free_signature A)) (free_algebra_map_help (free_algebra_help B)))).
    Defined.
  End FreeAlgebraMap.

  Local Definition free_algebra_functor_id_help
        (A : HSET)
    : (HIT_exists (free_signature A))
        -->
        free_algebra_map_help (identity A) (free_algebra_help A).
  Proof.
    use mk_algebra_map.
    - exact (idfun _).
    - intros x.
      induction x as [x | x].
      + reflexivity.
      + unfold idfun ; simpl ; cbn.
        unfold free_algebra_help.
        exact (maponpaths _ (maponpaths _ (eqtohomot (!(functor_id (⦃ P ⦄) _)) _))).
  Defined.

  Definition free_algebra_functor
    : HSET ⟶ set_algebra Σ.
  Proof.
    use mk_functor.
    - use mk_functor_data.
      + exact free_algebra.
      + exact @free_algebra_map.
    - split.
      + intros A.
        pose (hit_eq
                (HIT_exists (free_signature A))
                (free_algebra_map_help (identity A) (free_algebra_help A))
                (hit_rec
                   (HIT_exists (free_signature A))
                   (free_algebra_map_help (identity A) (free_algebra_help A)))
                (free_algebra_functor_id_help A)) as p.
        simpl.
        unfold free_algebra_map.
        refine (maponpaths (free_signature_map A) p @ _).
        use subtypeEquality.
        { intro ; apply isapropunit. }
        use subtypeEquality.
        { intro ; apply TODO. }
        use funextsec.
        intro z ; revert z.
        reflexivity.
      + apply TODO.
  Defined.

  Definition forgetful
    : set_algebra Σ ⟶ HSET.
  Proof.
    use mk_functor.
    - use mk_functor_data.
      + intros X.
        apply X.
      + intros X Y f.
        apply f.
    - apply TODO.
  Defined.

  Definition unit
    : functor_identity HSET ⟹ free_algebra_functor ∙ forgetful.
  Proof.
    use mk_nat_trans.
    - intros X ; simpl.
      intro x.
      exact (alg_operation (free_algebra_help X) (inl x)).
    - intros x y f ; simpl ; cbn.
      use funextsec.
      intro z.
      apply TODO.
  Defined.

  Definition counit_help
             (X : set_algebra Σ)
    : set_algebra (free_signature (alg_carrier X)).
  Proof.
    use mk_algebra.
    - exact (alg_carrier X).
    - intros x ; simpl in x.
      induction x as [x | x].
      + exact x.
      + exact (alg_operation X x).
    - apply TODO.
  Defined.

  Definition counit
    : forgetful ∙ free_algebra_functor ⟹ functor_identity (set_algebra Σ).
  Proof.
    use mk_nat_trans.
    - intros X.
      exact (free_signature_map _ (hit_rec (HIT_exists (free_signature (pr11 X))) (counit_help X))).
    - apply TODO.
  Defined.

  Definition test
    : are_adjoints free_algebra_functor forgetful.
  Proof.
    use tpair.
    - split.
      + apply unit.
      + apply counit.
    - split.
      + intros X ; simpl.
        use subtypeEquality.
        { intro ; apply isapropunit. }
        apply subtypeEquality.
        { intro. apply TODO. }
        use funextsec.
        intro z.
        simpl. cbn.
        simpl in z.
        admit.
      + intros X.
        use funextsec.
        intro z.
        simpl ; cbn in *.
        admit.
  Admitted.
End FreeAlgebra.