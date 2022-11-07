(**
We define the polynomials as a HIT
 *)
Require Import prelude.all.
Require Import syntax.hit_signature.
Require Import syntax.hit.
Require Import syntax.hit_properties.
Require Import algebras.set_algebra.
Require Import existence.hit_existence.
Require Import examples.rings.
Require Import displayed_algebras.displayed_algebra.

Open Scope cat.

Opaque HIT_exists hit_ind hit_ind_prop hit_rec.

Section PolynomialRing.
  Variable (R : ring_cat)
           (A : hSet).
  
  (** We first define the signature. *)

  (** Operations *)
  Definition polynomial_operations
    : poly_code
    := C (alg_carrier R) + C A + ring_operations.

  (** Labels of polynomial axioms *)
  Inductive polynomial_ax_help :=
  | R_plus : polynomial_ax_help
  | R_times : polynomial_ax_help
  | R_one : polynomial_ax_help.

  Definition polynomial_ax
    := (polynomial_ax_help + ring_ax)%type.

  Definition ring_ax_to_polynomial_ax
    : ring_ax → polynomial_ax
    := Datatypes.inr.

  Definition polynomial_ax_help_to_polynomial_ax
    : polynomial_ax_help → polynomial_ax
    := Datatypes.inl.

  (** Arguments for each label *)
  Definition polynomial_arg_help
    : polynomial_ax_help → poly_code
    := fun j =>
         match j with
         | R_plus => C(alg_carrier R × alg_carrier R)%set
         | R_times => C(alg_carrier R × alg_carrier R)%set
         | R_one => C unitset
         end.
  
  Definition polynomial_arg
    : polynomial_ax → poly_code.
  Proof.
    intro j.
    induction j as [j | j].
    - exact (polynomial_arg_help j).
    - exact (ring_arg j).
  Defined.

  (** Some convenient notation for the constructor terms. These represent the operations *)
  Definition const
    : endpoint polynomial_operations (C (alg_carrier R)) I.
  Proof.
    refine (comp _ constr).
    refine (comp _ (ι₁ _ _)).
    exact (ι₁ _ _).
  Defined.
                                         
  Definition var
             (P : poly_code)
             (a : A)
    : endpoint polynomial_operations P I.
  Proof.
    refine (comp _ constr).
    refine (comp _ (ι₁ _ _)).
    refine (comp _ (ι₂ _ _)).
    exact (c _ a).
  Defined.

  Definition ring_endpoint_to_poly_endpoint
             {P Q : poly_code}
             (e : endpoint ring_operations P Q)
    : endpoint polynomial_operations P Q.
  Proof.
    induction e as [P | P₁ P₂ P₃ e₁ IHe₁ e₂ IHe₂ | P Q | P Q | P Q
                    | P Q | P₁ P₂ P₃ e₁ IHe₁ e₂ IHe₂ | P T t | Z₁ Z₂ f |  ].
    - exact (id_e _ P).
    - exact (comp IHe₁ IHe₂).
    - exact (ι₁ _ _).
    - exact (ι₂ _ _).
    - exact (π₁ _ _).
    - exact (π₂ _ _).
    - exact (pair IHe₁ IHe₂).
    - exact (c _ t).
    - exact (fmap f).
    - exact (comp (ι₂ _ _) constr).
  Defined.
  
  Definition plus_P
             {P : poly_code}
             (e₁ e₂ : endpoint polynomial_operations P I)
    : endpoint polynomial_operations P I.
  Proof.
    refine (comp _ constr).
    refine (comp _ (ι₂ _ _)).
    refine (comp _ (ι₁ _ _)).
    refine (comp _ (ι₁ _ _)).
    refine (comp _ (ι₁ _ _)).
    refine (comp _ (ι₁ _ _)).
    exact (pair e₁ e₂).
  Defined.

  Definition mult_P
             {P : poly_code}
             (e₁ e₂ : endpoint polynomial_operations P I)
    : endpoint polynomial_operations P I.
  Proof.
    refine (comp _ constr).
    refine (comp _ (ι₂ _ _)).
    refine (comp _ (ι₁ _ _)).
    refine (comp _ (ι₁ _ _)).
    refine (comp _ (ι₁ _ _)).
    refine (comp _ (ι₂ _ _)).  
    exact (pair e₁ e₂).
  Defined.

  Definition one_el_P
             {P : poly_code}
    : endpoint polynomial_operations P I.
  Proof.
    refine (comp _ constr).
    refine (comp _ (ι₂ _ _)).    
    refine (comp _ (ι₂ _ _)).
    apply c.
    exact tt.
  Defined.

  Definition polynomial_lhs_help
    : ∏ (j : polynomial_ax_help),
      endpoint polynomial_operations (polynomial_arg_help j) I.
  Proof.
    intro j.
    induction j.
    - refine (plus_P _ _). (* R_plus *)
      + refine (comp (fmap _) const).
        exact dirprod_pr1.
      + refine (comp (fmap _) const).
        exact dirprod_pr2.
    - refine (mult_P _ _). (* R_mult *)
      + refine (comp (fmap _) const).
        exact dirprod_pr1.
      + refine (comp (fmap _) const).
        exact dirprod_pr2.
    - exact one_el_P.
  Defined.

  Definition polynomial_lhs
    : ∏ (j : polynomial_ax), endpoint polynomial_operations (polynomial_arg j) I.
  Proof.
    intro j.
    induction j as [j | j].
    - exact (polynomial_lhs_help j).
    - apply ring_endpoint_to_poly_endpoint.
      exact (ring_lhs j).
  Defined.

  Definition polynomial_rhs_help
    : ∏ (j : polynomial_ax_help),
      endpoint polynomial_operations (polynomial_arg_help j) I.
  Proof.
    intro j.
    induction j.
    - refine (comp (fmap _) const).
      exact (λ x, ring_plus R (pr1 x) (pr2 x)).
    - refine (comp (fmap _) const).
      exact (λ x, ring_mult R (pr1 x) (pr2 x)).
    - refine (comp (fmap _) const).
      exact (λ _, ring_one R).
  Defined.

  Definition polynomial_rhs
    : ∏ (j : polynomial_ax), endpoint polynomial_operations (polynomial_arg j) I.
  Proof.
    intro j.
    induction j as [j | j].
    - exact (polynomial_rhs_help j).
    - apply ring_endpoint_to_poly_endpoint.
      exact (ring_rhs j).
  Defined.


  (** The signature of polynomials as a HIT signature *)
  Definition polynomial_signature
    : hit_signature.
  Proof.
    use tpair.
    - exact polynomial_operations.
    - use tpair.
      + exact polynomial_ax.
      + use tpair.
        * exact polynomial_arg.
        * split.
          ** exact polynomial_lhs.
          ** exact polynomial_rhs.
  Defined.

  (** Polynomial ring *)
  Definition polynomial_ring_HIT
    : HIT polynomial_signature
    := HIT_exists polynomial_signature.

  Definition polynomial_ring_set
    : hSet
    := pr111 polynomial_ring_HIT.

  Definition polynomial_ring_plus
    : polynomial_ring_set → polynomial_ring_set → polynomial_ring_set
    := λ x y, alg_operation polynomial_ring_HIT (inr(inl(inl(inl(inl(x ,, y)))))).

  Definition polynomial_ring_mult
    : polynomial_ring_set → polynomial_ring_set → polynomial_ring_set
    := λ x y, alg_operation polynomial_ring_HIT (inr(inl(inl(inl(inr(x ,, y)))))).

  Definition polynomial_ring_minus
    : polynomial_ring_set → polynomial_ring_set
    := λ x, alg_operation polynomial_ring_HIT (inr(inl(inl(inr x)))).

  Definition polynomial_ring_zero
    : polynomial_ring_set
    := alg_operation polynomial_ring_HIT (inr(inl(inr tt))).

  Definition polynomial_ring_one
    : polynomial_ring_set
    := alg_operation polynomial_ring_HIT (inr(inr tt)).

  Definition polynomial_ring
    : ring_cat.
  Proof.
    use mk_ring.
    - exact polynomial_ring_set.
    - exact polynomial_ring_plus.
    - exact polynomial_ring_mult.
    - exact polynomial_ring_minus.
    - exact polynomial_ring_zero.
    - exact polynomial_ring_one.
    - exact (λ x₁ x₂ x₃, alg_paths polynomial_ring_HIT
                                   (ring_ax_to_polynomial_ax p_assoc)
                                   ((x₁ ,, x₂) ,, x₃)).
    - exact (λ x, alg_paths polynomial_ring_HIT
                            (ring_ax_to_polynomial_ax p_unit)
                            x).
    - exact (λ x, alg_paths polynomial_ring_HIT
                            (ring_ax_to_polynomial_ax p_inv)
                            x).
    - exact (λ x y, alg_paths polynomial_ring_HIT
                              (ring_ax_to_polynomial_ax p_com)
                              (x ,, y)).
    - exact (λ x₁ x₂ x₃, alg_paths polynomial_ring_HIT
                                   (ring_ax_to_polynomial_ax m_assoc)
                                   ((x₁ ,, x₂) ,, x₃)).
    - exact (λ x, alg_paths polynomial_ring_HIT
                            (ring_ax_to_polynomial_ax m_unit)
                            x).
    - exact (λ x y, alg_paths polynomial_ring_HIT
                              (ring_ax_to_polynomial_ax m_com)
                              (x ,, y)).
    - exact (λ x₁ x₂ x₃, alg_paths polynomial_ring_HIT
                                   (ring_ax_to_polynomial_ax distr)
                                   ((x₁ ,, x₂) ,, x₃)).
  Defined.

  (** Inclusion map of `R` *)
  Definition polynomial_inclusion_map
    : alg_carrier R → alg_carrier polynomial_ring
    := λ r, alg_operation polynomial_ring_HIT (inl(inl r)).

  Definition polynomial_inclusion
    : R --> polynomial_ring.
  Proof.
    use mk_ring_map.
    - exact polynomial_inclusion_map.
    - exact (λ x₁ x₂, !(alg_paths polynomial_ring_HIT
                                 (polynomial_ax_help_to_polynomial_ax R_plus)
                                 (x₁ ,, x₂))).
    - exact (λ x₁ x₂, !(alg_paths polynomial_ring_HIT
                                  (polynomial_ax_help_to_polynomial_ax R_times)
                                  (x₁ ,, x₂))).
    - exact (!(alg_paths polynomial_ring_HIT
                         (polynomial_ax_help_to_polynomial_ax R_one)
                         tt)).
  Defined.

  (** The variables *)
  Definition variable
    : A → alg_carrier polynomial_ring
    := λ a, alg_operation polynomial_ring_HIT (inl(inr a)).

  (** Universal property of the polynomial ring *)
  Section PolynomialRingUMP.
    Context {S : ring_cat}.
    Variable (h : R --> S)
             (f : A → alg_carrier S).

    (** Existence *)
    Local Definition polynomial_ump_algebra
      : set_algebra polynomial_signature.
    Proof.
      use make_algebra.
      - exact (alg_carrier S).
      - intro x.
        induction x as [x | x] ; cbn in x.
        + induction x as [r | a].
          * exact (alg_map_carrier h r).
          * exact (f a).
        + induction x as [x | x].
          * induction x as [x | x].
            ** induction x as [x | x].
               *** induction x as [x | x].
                   **** exact (ring_plus S (pr1 x) (pr2 x)).
                   **** exact (ring_mult S (pr1 x) (pr2 x)).
               *** exact (ring_minus S x).
            ** exact (ring_zero S).
          * exact (ring_one S).
      - intros j x.
        induction j as [j | j] ; simpl in j.
        + induction j.
          * exact (!(ring_map_plus h (pr1 x) (pr2 x))).
          * exact (!(ring_map_mult h (pr1 x) (pr2 x))).
          * exact (!(ring_map_one h)).
        + induction j.
          * exact (ring_plus_assoc S (pr11 x) (pr21 x) (pr2 x)).
          * exact (ring_zero_plus S x).
          * exact (ring_min_plus S x).
          * exact (ring_plus_com S (pr1 x) (pr2 x)).
          * exact (ring_mult_assoc S (pr11 x) (pr21 x) (pr2 x)).
          * exact (ring_one_mult S x).
          * exact (ring_mult_com S (pr1 x) (pr2 x)).
          * exact (ring_left_distr S (pr11 x) (pr21 x) (pr2 x)).
    Defined.

    Local Definition polynomial_ump_HIT_map
      : polynomial_ring_HIT --> polynomial_ump_algebra
      := hit_rec polynomial_ring_HIT polynomial_ump_algebra.

    Definition polynomial_ump
      : polynomial_ring --> S.
    Proof.
      use mk_ring_map.
      - exact (alg_map_carrier polynomial_ump_HIT_map).
      - intros x₁ x₂.
        exact (eqtohomot (pr21 polynomial_ump_HIT_map) _).
      - intros x₁ x₂.
        exact (eqtohomot (pr21 polynomial_ump_HIT_map) _).
      - exact (eqtohomot (pr21 polynomial_ump_HIT_map) (inr(inr _))).
    Defined.

    Definition polynomial_ump_var
      : ∏ (a : A), alg_map_carrier polynomial_ump (variable a) = f a.
    Proof.
      intro a.
      apply (eqtohomot (pr21 polynomial_ump_HIT_map)).
    Qed.

    Definition polynomial_ump_ring
      : ∏ (r : alg_carrier R),
        alg_map_carrier polynomial_ump
                        (alg_map_carrier polynomial_inclusion r)
        =
        alg_map_carrier h r.
    Proof.
      intro r.
      apply (eqtohomot (pr21 polynomial_ump_HIT_map)).
    Qed.

    (** Uniqueness *)
    Definition ring_map_to_poly_map
               {g : polynomial_ring --> S}
               (p : ∏ (a : A), alg_map_carrier g (variable a) = f a)
               (q : ∏ (r : alg_carrier R),
                     alg_map_carrier g
                                     (alg_map_carrier polynomial_inclusion r)
                     =
                     alg_map_carrier h r)

      : polynomial_ring_HIT --> polynomial_ump_algebra.
    Proof.
      use make_algebra_map.
      - exact (alg_map_carrier g).
      - intros x.
        induction x as [x | x].
        + induction x as [x | x].
          * exact (q x).
          * exact (p x).
        + induction x as [x | x].
          * induction x as [x | x].
            ** induction x as [x | x].
               *** induction x as [x | x].
                   **** exact (ring_map_plus g (pr1 x) (pr2 x)).
                   **** exact (ring_map_mult g (pr1 x) (pr2 x)).
               *** exact (ring_map_minus g x).
            ** induction x.
               exact (ring_map_zero g).
          * induction x.
            exact (ring_map_one g).
    Defined.

    Definition polynomial_ump_unique
               {g₁ g₂ : polynomial_ring --> S}
               (p₁ : ∏ (a : A), alg_map_carrier g₁ (variable a) = f a)
               (q₁ : ∏ (r : alg_carrier R),
                     alg_map_carrier g₁
                                     (alg_map_carrier polynomial_inclusion r)
                     =
                     alg_map_carrier h r)
               (p₂ : ∏ (a : A), alg_map_carrier g₂ (variable a) = f a)
               (q₂ : ∏ (r : alg_carrier R),
                     alg_map_carrier g₂
                                     (alg_map_carrier polynomial_inclusion r)
                     =
                     alg_map_carrier h r)

      : g₁ = g₂.
    Proof.
      use algebra_map_eq.
      pose (ring_map_to_poly_map p₁ q₁) as z₁.
      pose (ring_map_to_poly_map p₂ q₂) as z₂.
      intro z.
      pose (hit_map_eq polynomial_ring_HIT _ z₁ z₂) as r.
      exact (eqtohomot (maponpaths alg_map_carrier r) z).
    Qed.
  End PolynomialRingUMP.
End PolynomialRing.
