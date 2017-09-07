/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of set-quotients, i.e. quotient of a mere relation which is then set-truncated.
-/

import function algebra.relation types.trunc types.eq hit.quotient

open eq is_trunc trunc quotient equiv is_equiv

namespace set_quotient
section
  parameters {A : Type _} (R : A → A → Prop)
  -- set-quotients are just set-truncations of (type) quotients
  @[hott] def set_quotient : Type _ := trunc 0 (quotient R)

  parameter {R}
  @[hott] def class_of (a : A) : set_quotient :=
  tr (class_of _ a)

  @[hott] def eq_of_rel {a a' : A} (H : R a a') : class_of a = class_of a' :=
  ap tr (eq_of_rel _ H)

  @[hott] theorem is_set_set_quotient [instance] : is_set set_quotient :=
  begin unfold set_quotient, exact _ end

  protected @[hott] def rec {P : set_quotient → Type _} [Pt : Πaa, is_set (P aa)]
    (Pc : Π(a : A), P (class_of a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel H] Pc a')
    (x : set_quotient) : P x :=
  begin
    apply (@trunc.rec_on _ _ P x),
    { intro x', apply Pt},
    { intro y, induction y,
      { apply Pc},
      { exact pathover_of_pathover_ap P tr (Pp H)}}
  end

  protected @[hott] def rec_on [reducible] {P : set_quotient → Type _} (x : set_quotient)
    [Pt : Πaa, is_set (P aa)] (Pc : Π(a : A), P (class_of a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel H] Pc a') : P x :=
  rec Pc Pp x

  @[hott] theorem rec_eq_of_rel {P : set_quotient → Type _} [Pt : Πaa, is_set (P aa)]
    (Pc : Π(a : A), P (class_of a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[eq_of_rel H] Pc a')
    {a a' : A} (H : R a a') : apd (rec Pc Pp) (eq_of_rel H) = Pp H :=
  !is_set.elimo

  protected @[hott] def elim {P : Type _} [Pt : is_set P] (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (x : set_quotient) : P :=
  rec Pc (λa a' H, pathover_of_eq _ (Pp H)) x

  protected @[hott] def elim_on [reducible] {P : Type _} (x : set_quotient) [Pt : is_set P]
    (Pc : A → P) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a')  : P :=
  elim Pc Pp x

  @[hott] theorem elim_eq_of_rel {P : Type _} [Pt : is_set P] (Pc : A → P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') {a a' : A} (H : R a a')
    : ap (elim Pc Pp) (eq_of_rel H) = Pp H :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (eq_of_rel H)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim,rec_eq_of_rel],
  end

  protected @[hott] def rec_prop {P : set_quotient → Type _} [Pt : Πaa, is_prop (P aa)]
    (Pc : Π(a : A), P (class_of a)) (x : set_quotient) : P x :=
  rec Pc (λa a' H, !is_prop.elimo) x

  protected @[hott] def elim_prop {P : Type _} [Pt : is_prop P] (Pc : A → P) (x : set_quotient)
    : P :=
  elim Pc (λa a' H, !is_prop.elim) x

end
end set_quotient

attribute set_quotient.class_of
attribute set_quotient.rec set_quotient.elim [recursor 7]
attribute set_quotient.rec_on set_quotient.elim_on

open sigma relation function

namespace set_quotient
  variables {A B C : Type _} (R : A → A → Prop) (S : B → B → Prop) (T : C → C → Prop)

  @[hott] def is_surjective_class_of : is_surjective (class_of : A → set_quotient R) :=
  λx, set_quotient.rec_on x (λa, tr (fiber.mk a idp)) (λa a' r, !is_prop.elimo)

  @[hott] def is_prop_set_quotient {A : Type _} (R : A → A → Prop) [is_prop A] :
    is_prop (set_quotient R) :=
  begin
    apply is_prop.mk, intros x y,
    induction x using set_quotient.rec_prop, induction y using set_quotient.rec_prop,
    exact ap class_of !is_prop.elim
  end

  local attribute is_prop_set_quotient [instance]
  @[hott] def is_trunc_set_quotient [instance] (n : ℕ₋₂) {A : Type _} (R : A → A → Prop) [is_trunc n A] :
    is_trunc n (set_quotient R) :=
  begin
    cases n with n, { apply is_contr_of_inhabited_prop, exact class_of !center },
    cases n with n, { apply _ },
    apply is_trunc_succ_succ_of_is_set
  end

  @[hott] def is_equiv_class_of {A : Type _} [is_set A] (R : A → A → Prop)
    (p : Π⦃a b⦄, R a b → a = b) : is_equiv (@class_of A R) :=
  begin
    fapply adjointify,
    { intro x, induction x, exact a, exact p H },
    { intro x, induction x using set_quotient.rec_prop, reflexivity },
    { intro a, reflexivity }
  end

  @[hott] def equiv_set_quotient {A : Type _} [is_set A] (R : A → A → Prop)
    (p : Π⦃a b⦄, R a b → a = b) : A ≃ set_quotient R :=
  equiv.mk _ (is_equiv_class_of R p)

  /- non-dependent universal property -/

  @[hott] def set_quotient_arrow_equiv (B : Type _) [H : is_set B] :
    (set_quotient R → B) ≃ (Σ(f : A → B), Π(a a' : A), R a a' → f a = f a') :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨λa, f (class_of a), λa a' r, ap f (eq_of_rel r)⟩},
    { intros v x, induction v with f p, exact set_quotient.elim_on x f p},
    { intro v, induction v with f p, esimp, apply ap (sigma.mk f),
      apply eq_of_homotopy3, intros a a' r, apply elim_eq_of_rel},
    { intro f, apply eq_of_homotopy, intro x, refine set_quotient.rec_on x _ _: esimp,
        intro a, reflexivity,
        intros a a' r, apply eq_pathover, apply hdeg_square, apply elim_eq_of_rel}
  end

  protected @[hott] def code (a : A) (x : set_quotient R) [H : is_equivalence R]
    : Prop :=
  set_quotient.elim_on x (R a)
    begin
      intros a' a'' H1,
      refine to_inv !trunctype_eq_equiv _, esimp,
      apply ua,
      apply equiv_of_is_prop,
      { intro H2, exact is_transitive.trans R H2 H1},
      { intro H2, apply is_transitive.trans R H2, exact is_symmetric.symm R H1}
    end

  protected @[hott] def encode {a : A} {x : set_quotient R} (p : class_of a = x)
    [H : is_equivalence R] : set_quotient.code R a x :=
  begin
    induction p, esimp, apply is_reflexive.refl R
  end

  @[hott] def rel_of_eq {a a' : A} (p : class_of a = class_of a' :> set_quotient R)
    [H : is_equivalence R] : R a a' :=
  set_quotient.encode R p

  variables {R S T}
  @[hott] def quotient_unary_map (f : A → B) (H : Π{a a'} (r : R a a'), S (f a) (f a')) :
    set_quotient R → set_quotient S :=
  set_quotient.elim (class_of ∘ f) (λa a' r, eq_of_rel (H r))

  @[hott] def quotient_binary_map (f : A → B → C)
    (H : Π{a a'} (r : R a a') {b b'} (s : S b b'), T (f a b) (f a' b'))
    [HR : is_reflexive R] [HS : is_reflexive S] :
    set_quotient R → set_quotient S → set_quotient T :=
  begin
    refine set_quotient.elim _ _,
    { intro a, refine set_quotient.elim _ _,
      { intro b, exact class_of (f a b)},
      { intros b b' s, apply eq_of_rel, apply H, apply is_reflexive.refl R, exact s}},
    { intros a a' r, apply eq_of_homotopy, refine set_quotient.rec _ _,
      { intro b, esimp, apply eq_of_rel, apply H, exact r, apply is_reflexive.refl S},
      { intros b b' s, apply eq_pathover, esimp, apply is_set.elims}}
  end

end set_quotient
