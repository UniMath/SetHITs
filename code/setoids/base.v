(**
Here we define the basic notions of setoids.
 *)
Require Import prelude.all.

(**
Projections and builder functions of equivalence relations.
*)
Definition make_eq_rel
           {X : hSet}
           (rel : hrel X)
           (isrefl_rel : isrefl rel)
           (issymm_rel : issymm rel)
           (istrans_rel : istrans rel)
  : eqrel X
  := rel ,, ((istrans_rel ,, isrefl_rel) ,, issymm_rel).

Declare Scope setoid_scope.
Delimit Scope setoid_scope with setoid.
Notation "'id' g" := (eqrelrefl _ g) (at level 30) : setoid_scope.
Notation "! p" := (eqrelsymm _ _ _ p) : setoid_scope.
Notation "p @ q" := (eqreltrans _ _ _ _ p q) : setoid_scope.

(**
A setoid is just a pair of a set and an equivalence relation.
 *)
Definition setoid :=
  ∑ (X : hSet), eqrel X.

(**
Projections and builder functions of setoids.
 *)
Definition make_setoid
           {X : hSet}
           (R : eqrel X)
  : setoid
  := X ,, R.

Coercion carrier (X : setoid) : hSet := pr1 X.

Definition carrier_eq
           (X : setoid)
  : eqrel X
  := pr2 X.

Notation "x ≡ y" := (carrier_eq _ x y) (at level 70).

Definition isaprop_setoid_eq
           {X : setoid}
           (x y : X)
  : isaprop (x ≡ y).
Proof.
  apply (pr1 (carrier_eq X)).
Defined.

Definition setoid_path
           {X : setoid}
           {x y : X}
           (p : x = y)
  : x ≡ y.
Proof.
  induction p.
  apply (id _)%setoid.
Defined.

(**
Lastly, we define setoid morphisms.
 *)
Definition setoid_morphism (X₁ X₂ : setoid)
  := ∑ (f : X₁ → X₂), ∏ (x y : X₁), x ≡ y → f x ≡ f y.

(**
Projections and builder functions for setoid morphisms.
 *)
Definition make_setoid_morphism
           {X₁ X₂ : setoid}
           (f : X₁ → X₂)
           (Rf : ∏ (x y : X₁), x ≡ y → f x ≡ f y)
  : setoid_morphism X₁ X₂
  := f ,, Rf.

Definition map_carrier
           {X₁ X₂ : setoid}
           (f : setoid_morphism X₁ X₂)
  : X₁ → X₂
  := pr1 f.

Coercion map_carrier : setoid_morphism >-> Funclass.

Definition map_eq
           {X₁ X₂ : setoid}
           (f : setoid_morphism X₁ X₂)
           {x y : X₁}
  : x ≡ y → f x ≡ f y
  := pr2 f x y.

(**
Equality principle for setoid morphisms.
 *)
Definition setoid_morphism_eq
           {X₁ X₂ : setoid}
           (f g : setoid_morphism X₁ X₂)
           (e : ∏ (x : X₁), f x = g x)
  : f = g.
Proof.
  use subtypePath.
  - intro.    
    do 3 (apply impred ; intro).
    apply isaprop_setoid_eq.
  - apply funextsec.
    exact e.
Defined.

Definition isaset_setoid_morphism (X₁ X₂ : setoid)
  : isaset(setoid_morphism X₁ X₂).
Proof.
  use isaset_total2.
  - apply isaset_set_fun_space.
  - intros f ; cbn.
    apply isasetaprop.
    repeat (apply impred ; intro).
    apply isaprop_setoid_eq.
Defined.
