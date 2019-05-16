(**
Here we define the category of groups using the mechanism of algebras.
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import syntax.hit.
Require Import syntax.hit_properties.
Require Import algebras.univalent_algebra.
Require Import algebras.set_algebra.
Require Import displayed_algebras.displayed_algebra.
Require Import displayed_algebras.constant_display.
Require Import existence.hit_existence.

Opaque hit_rec.
Opaque HIT_exists.

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
  Section Signature.
    Variable (A : hSet).
    
    Definition free_point_arg
    : poly_code
      := C A + P.

    Definition free_endpoint
               {R₁ R₂ : poly_code}
               (e : endpoint P R₁ R₂)
      : endpoint free_point_arg R₁ R₂.
    Proof.
      induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                      | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ f |  ].
      - exact (id_e _ P).
      - exact (comp IHe₁ IHe₂).
      - exact (ι₁ P Q).
      - exact (ι₂ P Q).
      - exact (π₁ P Q).
      - exact (π₂ P Q).
      - exact (pair IHe₁ IHe₂).
      - exact (c P t).
      - exact (fmap f).
      - exact (comp (ι₂ (C A) P) constr).
    Defined.

    Definition free_signature
      : hit_signature.
    Proof.
      use tpair.
      - exact free_point_arg.
      - use tpair.
        + apply Σ.
        + use tpair.
          * exact (λ j, Q j).
          * split.
            ** exact (λ j, free_endpoint (l j)).
            ** exact (λ j, free_endpoint (r j)).
    Defined.
  End Signature.
  
  (** Projections *)
  Section Projections.
    Context {A : hSet}.
    Variable (X : set_algebra (free_signature A)).

    Definition free_alg_to_alg_carrier
      : hSet
      := alg_carrier X.

    Definition free_alg_to_alg_operation
      : ⦃ point_arg Σ ⦄ free_alg_to_alg_carrier → free_alg_to_alg_carrier
      := λ x, alg_operation X (inr x).

    Definition free_alg_to_alg_prealg
      : set_prealgebras P.
    Proof.
      use tpair.
      - exact free_alg_to_alg_carrier.
      - exact free_alg_to_alg_operation.
    Defined.

    (** Lemma to get underlying `Σ`-algebra *)
    Definition free_alg_to_alg_endpoint
               {R₁ R₂ : poly_code}
               (e : endpoint (point_arg Σ) R₁ R₂)
               (x : ⦃ R₁ ⦄ free_alg_to_alg_carrier)
      : set_endpoint e free_alg_to_alg_prealg x
        =
        set_endpoint (free_endpoint A e) (alg_to_prealg X) x.
    Proof.
      induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                      | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ f | ]
      ; try reflexivity ; simpl ; cbn.
      - exact (maponpaths _ (IHe₁ x) @ IHe₂ _).
      - apply pathsdirprod.
        + apply IHe₁.
        + apply IHe₂.
    Qed.
  
    Definition free_alg_to_alg
      : set_algebra Σ.
    Proof.
      use make_algebra.
      - exact free_alg_to_alg_carrier.
      - exact free_alg_to_alg_operation.
      - intros j x ; simpl.
        exact ((free_alg_to_alg_endpoint (l j) x)
                 @ alg_paths X j x
                 @ !(free_alg_to_alg_endpoint (r j) x)).
    Defined.
  End Projections.
  
  (** Builder *)
  Section Builder.
    Context {A : SET}
            {X : set_algebra Σ}.
    Variable (f : A --> alg_carrier X).

    Definition alg_to_free_prealg
      : set_prealgebras (free_point_arg A).
    Proof.
      use tpair.
      - exact (alg_carrier X).
      - intros z.
        induction z as [a | z].
        + exact (f a).
        + exact (alg_operation X z).
    Defined.

    Definition alg_to_free_alg_endpoint
               {R₁ R₂ : poly_code}
               (e : endpoint P R₁ R₂)
               (x : ⦃ R₁ ⦄ (alg_carrier X))
      : set_endpoint (free_endpoint A e) alg_to_free_prealg x
        =
        set_endpoint e (alg_to_prealg X) x.
    Proof.
      induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                      | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ]
      ; try reflexivity ; simpl ; cbn.
      - exact (maponpaths _ (IHe₁ x) @ IHe₂ _).
      - apply pathsdirprod.
        + apply IHe₁.
        + apply IHe₂.
    Qed.

    Definition mk_free_alg
      : set_algebra (free_signature A).
    Proof.
      use tpair.
      - exact alg_to_free_prealg.
      - intros j x ; simpl.
        exact ((alg_to_free_alg_endpoint (l j) x)
                  @ alg_paths X j x
                  @ !(alg_to_free_alg_endpoint (r j) x)).
    Defined.
  End Builder.
    
  (** Next we show this gives rise to a functor *)
  Definition free_algebra_help
             (A : hSet)
    : set_algebra (free_signature A)
    := HIT_exists (free_signature A).

  Definition free_algebra
             (A : hSet)
    : set_algebra Σ
    := free_alg_to_alg (free_algebra_help A).

  Definition free_algebra_inc
             (A : SET)
    : A --> alg_carrier (free_algebra A)
    := λ a, @alg_operation (free_signature A) _ (inl a).

  (** Projections of maps on the free signature *)
  Definition free_signature_map
             {A : hSet}
             {X Y : set_algebra (free_signature A)}
             (f : X --> Y)
    : free_alg_to_alg X --> free_alg_to_alg Y.
  Proof.
    use make_algebra_map.
    - apply f.
    - intros x ; simpl in *.
      exact (eqtohomot (pr21 f) (inr x)).
  Defined.

  (** Properties of `free_signature_map` *)
  Definition free_signature_map_id
             (A : hSet)
             {X : set_algebra (free_signature A)}
    : free_signature_map (identity X) = identity (free_alg_to_alg X).
  Proof.
    use algebra_map_eq.
    reflexivity.
  Qed.

  (** Action of free algebra functor on maps. *)
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
        : ⦃ free_point_arg A ⦄ free_algebra_map_lift_carrier
          →
          free_algebra_map_lift_carrier.
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
        : set_endpoint (free_endpoint A e) free_algebra_map_lift_prealg x
          =
          set_endpoint (free_endpoint B e) (alg_to_prealg X) x.
      Proof.
        induction e as [P | P Q R e₁ IHe₁ e₂ IHe₂
                        | P Q | P Q | P Q | P Q | P Q R e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ g | ]
        ; try reflexivity.
        - simpl ; unfold compose ; simpl.
          refine (_ @ _).
          + apply maponpaths.
            apply IHe₁.
          + apply IHe₂.
        - apply pathsdirprod.
          + apply IHe₁.
          + apply IHe₂.
      Qed.

      Definition free_algebra_map_help
        : set_algebra (free_signature A).
      Proof.
        use make_algebra.
        - exact free_algebra_map_lift_carrier.
        - exact free_algebra_map_lift_operation.
        - intros j x ; simpl.
          exact ((lift_endpoint (path_lhs Σ j) x)
                    @ alg_paths X j x
                    @ !(lift_endpoint (path_rhs Σ j) x)).
      Defined.
    End LiftAlgebra.

    Definition free_algebra_map
      : free_algebra A --> free_algebra B
      := free_signature_map
           (hit_rec (HIT_exists (free_signature A))
                    (free_algebra_map_help (free_algebra_help B))).
  End FreeAlgebraMap.

  Definition free_algebra_functor_id
             (A : SET)
    : free_algebra_map (identity A) = identity (free_algebra A).
  Proof.
    apply (@algebra_map_eq _ _ _ (free_algebra_map (identity A))).
    use hit_ind_prop.
    {
      intro x.
      apply (alg_carrier _).
    }
    intros z Hz.
    cbn.
    pose (hit_rec (HIT_exists (free_signature A))
                  (free_algebra_map_help (λ x, x) (free_algebra_help A))) as g.
    pose (eqtohomot (pr21 g) z) as p.
    refine (p @ _).
    apply (maponpaths (alg_operation _)).
    induction z as [a | z].
    + apply idpath.
    + pose (poly_dact_eq _ Hz) as q.
      refine (q @ _).
      simpl.
      apply (maponpaths inr).
      apply (eqtohomot (functor_id (⦃ P ⦄) _) z).
  Qed.

  Definition free_algebra_functor_comp
             (A B C : SET)
             (f : A --> B)
             (g : B --> C)
    : free_algebra_map (f · g) = free_algebra_map f · free_algebra_map g.
  Proof.
    apply (@algebra_map_eq _ _ _ (free_algebra_map (f · g))).
    use hit_ind_prop.
    {
      intro x.
      apply (alg_carrier _).
    }
    intros z Hz.
    cbn.
    pose (hit_rec (HIT_exists (free_signature A))
                  (free_algebra_map_help f (free_algebra_help B))) as h₁.
    pose (hit_rec (HIT_exists (free_signature B))
                  (free_algebra_map_help g (free_algebra_help C))) as h₂.
    pose (hit_rec (HIT_exists (free_signature A))
                  (free_algebra_map_help (λ x, g(f x)) (free_algebra_help C))) as h₃.
    pose (eqtohomot (pr21 h₃) z) as p.
    simpl in p ; unfold compose, free_algebra_map_lift_operation in p ; simpl in p.
    refine (p @ _) ; unfold h₃ ; simpl ; clear p h₃.
    refine (!(_ @ _)).
    {
      apply maponpaths.
      pose (eqtohomot (pr21 h₁) z) as p.
      simpl in p ; unfold compose, free_algebra_map_lift_operation in p ; simpl in p.
      exact p.
    }
    unfold h₁ ; clear h₁.
    refine (eqtohomot (pr21 h₂) _ @ _).
    unfold h₂ ; clear h₂.
    apply (maponpaths (alg_operation _)).
    induction z as [a | z] ; simpl.
    - apply idpath.
    - refine (_ @ !_).
      {
        apply maponpaths.
        apply (eqtohomot (!(functor_comp (⦃ P ⦄) _ _)) _).
      }
      apply maponpaths.
      pose (poly_dact_eq _ Hz) as q.
      pose (ii2_injectivity _ _ q) as q'.
      apply q'.
  Qed.

  Definition free_algebra_functor
    : HSET ⟶ set_algebra Σ.
  Proof.
    use make_functor.
    - use make_functor_data.
      + exact free_algebra.
      + exact @free_algebra_map.
    - split.
      + exact free_algebra_functor_id.
      + exact free_algebra_functor_comp.
  Defined.

  (** Free algebra adjunction *)
  Definition free_algebra_hom_l
             (A : HSET)
             (B : set_algebra Σ)
    : set_algebra Σ ⟦ free_algebra_functor A, B ⟧ → HSET ⟦ A, (forgetful Σ) B ⟧
    := λ f, free_algebra_inc A · pr11 f.

  Definition free_algebra_hom_r
             (A : HSET)
             (B : set_algebra Σ)
    :  HSET ⟦ A, (forgetful Σ) B ⟧ → set_algebra Σ ⟦ free_algebra_functor A, B ⟧
    := λ f, free_signature_map
              (hit_rec (HIT_exists (free_signature A))
                       (mk_free_alg f)).

  Definition free_algebra_hom_left_inv
             (A : HSET)
             (B : set_algebra Σ)
             (f : set_algebra Σ ⟦ free_algebra_functor A, B ⟧)
    : free_algebra_hom_r A B (free_algebra_hom_l A B f) = f.
  Proof.
    apply (@algebra_map_eq Σ _ _ _ f).
    intros z ; cbn.
    revert z.
    use hit_ind_prop.
    {
      intro x.
      apply (alg_carrier _).
    }
    intros z Hz.
    cbn.
    pose (hit_rec (HIT_exists (free_signature A))
                  (mk_free_alg (λ x, (pr11 f) (free_algebra_inc A x)))) as g.
    pose (eqtohomot (pr21 g) z) as p.
    refine (p @ _).
    induction z as [a | z].
    - apply idpath.
    - refine (_ @ !(eqtohomot (pr21 f) z)).
      simpl ; unfold compose ; simpl.
      pose (poly_dact_eq _ Hz) as q.
      apply (maponpaths (alg_operation B)).
      exact (ii2_injectivity _ _ q).
  Qed.

  Definition free_algebra_hom_right_inv
             (A : HSET)
             (B : set_algebra Σ)
             (f : HSET ⟦ A, (forgetful Σ) B ⟧)
    : free_algebra_hom_l A B (free_algebra_hom_r A B f) = f.
  Proof.
    use funextsec.
    intro z.
    unfold free_algebra_inc.
    cbn.
    pose (hit_rec (HIT_exists (free_signature A)) (mk_free_alg f)) as g.
    exact (eqtohomot (pr21 g) (inl z)).
  Qed.

  Definition free_algebra_hom_equiv
             (A : HSET)
             (B : set_algebra Σ)
    : (set_algebra Σ ⟦ free_algebra_functor A, B ⟧)
        ≃
        HSET ⟦ A, (forgetful Σ) B ⟧.
  Proof.
    use make_weq.
    - exact (free_algebra_hom_l A B).
    - use gradth.
      + exact (free_algebra_hom_r A B).
      + exact (free_algebra_hom_left_inv A B).
      + exact (free_algebra_hom_right_inv A B).
  Defined.

  Definition free_algebra_adjoint
    : are_adjoints free_algebra_functor (forgetful Σ).
  Proof.
    apply adj_from_nathomweq.
    use tpair.
    - exact free_algebra_hom_equiv.
    - split.
      + intros A B f X h.
        use funextsec.
        cbn -[free_algebra_inc free_algebra_functor].
        intro z.
        apply maponpaths.
        pose ((hit_rec (HIT_exists (free_signature X))
                       (free_algebra_map_help h (free_algebra_help A)))) as g.
        pose (eqtohomot (pr21 g)) as p.
        exact (p (inl z)).
      + intros A B f Y k.
        use funextsec.
        cbn -[free_algebra_inc free_algebra_functor].
        intro z.
        reflexivity.
  Defined.
End FreeAlgebra.
