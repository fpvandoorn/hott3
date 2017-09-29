/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

n-truncation of types.

Ported from Coq HoTT
-/

/- The hit n-truncation is primitive, declared in init.hit. -/

import types.sigma types.pointed

open is_trunc eq equiv is_equiv function prod sum sigma

namespace trunc

  @[hott] protected def elim {n : trunc_index} {A : Type _} {P : Type _}
    [Pt : is_trunc n P] (H : A → P) : trunc n A → P :=
  trunc.rec H

  @[hott] protected def elim_on {n : trunc_index} {A : Type _} {P : Type _} (aa : trunc n A)
    [Pt : is_trunc n P] (H : A → P) : P :=
  trunc.elim H aa

end trunc

attribute trunc.elim_on
attribute trunc.rec [recursor 6]
attribute trunc.elim [recursor 6]

namespace trunc

  variables {X Y Z : Type _} {P : X → Type _} (n : trunc_index) (A B : Type _)

  local attribute is_trunc_eq [instance]

  variables {A n}
  @[hott] def untrunc_of_is_trunc [reducible] [H : is_trunc n A] : trunc n A → A :=
  trunc.rec id

  variables (A n)
  @[hott] def is_equiv_tr [instance] [H : is_trunc n A] : is_equiv (@tr n A) :=
  adjointify _
             (untrunc_of_is_trunc)
             (λaa, trunc.rec_on aa (λa, idp))
             (λa, idp)

  @[hott] def trunc_equiv [H : is_trunc n A] : trunc n A ≃ A :=
  (equiv.mk tr _)⁻¹ᵉ

  @[hott] def is_trunc_of_is_equiv_tr [H : is_equiv (@tr n A)] : is_trunc n A :=
  is_trunc_is_equiv_closed n (@tr n _)⁻¹

  /- Functoriality -/
  @[hott] def trunc_functor (f : X → Y) : trunc n X → trunc n Y :=
  λxx, trunc.rec_on xx (λx, tr (f x))

  @[hott] def trunc_functor_compose (f : X → Y) (g : Y → Z)
    : trunc_functor n (g ∘ f) ~ trunc_functor n g ∘ trunc_functor n f :=
  λxx, trunc.rec_on xx (λx, idp)

  @[hott] def trunc_functor_id : trunc_functor n (@id A) ~ id :=
  λxx, trunc.rec_on xx (λx, idp)

  @[hott] def trunc_functor_cast {X Y : Type _} (n : ℕ₋₂) (p : X = Y) :
    trunc_functor n (cast p) ~ cast (ap (trunc n) p) :=
  begin
    intro x, induction x with x, esimp,
    exact fn_tr_eq_tr_fn p (λy, tr) x ⬝ !tr_compose
  end

  @[hott] def is_equiv_trunc_functor (f : X → Y) [H : is_equiv f]
    : is_equiv (trunc_functor n f) :=
  adjointify _
             (trunc_functor n f⁻¹)
             (λyy, trunc.rec_on yy (λy, ap tr !right_inv))
             (λxx, trunc.rec_on xx (λx, ap tr !left_inv))

  @[hott] def trunc_homotopy {f g : X → Y} (p : f ~ g) : trunc_functor n f ~ trunc_functor n g :=
  λxx, trunc.rec_on xx (λx, ap tr (p x))

  section
    @[hott] def trunc_equiv_trunc (f : X ≃ Y) : trunc n X ≃ trunc n Y :=
    equiv.mk _ (is_equiv_trunc_functor n f)
  end

  section
  open prod.ops
  @[hott] def trunc_prod_equiv : trunc n (X × Y) ≃ trunc n X × trunc n Y :=
  begin
    fapply equiv.MK,
      {exact (λpp, trunc.rec_on pp (λp, (tr p.1, tr p.2)))},
      {intro p, cases p with xx yy,
        apply (trunc.rec_on xx), intro x,
        apply (trunc.rec_on yy), intro y, exact (tr (x,y))},
      {intro p, cases p with xx yy,
        apply (trunc.rec_on xx), intro x,
        apply (trunc.rec_on yy), intro y, apply idp},
      {intro pp, apply (trunc.rec_on pp), intro p, cases p, apply idp}
  end
  end

  /- Propositional truncation -/

  @[hott] def ttrunc (n : ℕ₋₂) (X : Type _) : n-Type _ :=
  trunctype.mk (trunc n X) _

  -- should this live in Prop?
  @[hott] def merely [reducible] (A : Type _) : Prop := ttrunc -1 A

  notation `||`:max A `||`:0 := merely A
  notation `∥`:max A `∥`:0   := merely A

  @[hott] def Exists [reducible] (P : X → Type _) : Prop := ∥ sigma P ∥
  @[hott] def or [reducible] (A B : Type _) : Prop := ∥ A ⊎ B ∥

  notation `exists` binders `,` r:(scoped P, Exists P) := r
  notation `∃` binders `,` r:(scoped P, Exists P) := r
  notation A ` \/ ` B := or A B
  notation A ∨ B    := or A B

  @[hott] def merely.intro   [reducible] (a : A) : ∥ A ∥             := tr a
  @[hott] def exists.intro   [reducible] (x : X) (p : P x) : ∃x, P x := tr ⟨x, p⟩
  @[hott] def or.intro_left  [reducible] (x : X) : X ∨ Y             := tr (inl x)
  @[hott] def or.intro_right [reducible] (y : Y) : X ∨ Y             := tr (inr y)

  @[hott] def exists.elim {A : Type _} {p : A → Type _} {B : Type _} [is_prop B] (H : Exists p)
    (H' : ∀ (a : A), p a → B) : B :=
  trunc.elim (sigma.rec H') H

  @[hott] def is_contr_of_merely_prop [H : is_prop A] (aa : merely A) : is_contr A :=
  is_contr_of_inhabited_prop (trunc.rec_on aa id)

  section
  open sigma.ops
  @[hott] def trunc_sigma_equiv : trunc n (Σ x, P x) ≃ trunc n (Σ x, trunc n (P x)) :=
  equiv.MK (λpp, trunc.rec_on pp (λp, tr ⟨p.1, tr p.2⟩))
           (λpp, trunc.rec_on pp (λp, trunc.rec_on p.2 (λb, tr ⟨p.1, b⟩)))
           (λpp, trunc.rec_on pp (λp, sigma.rec_on p (λa bb, trunc.rec_on bb (λb, by esimp))))
           (λpp, trunc.rec_on pp (λp, sigma.rec_on p (λa b, by esimp)))

  @[hott] def trunc_sigma_equiv_of_is_trunc [H : is_trunc n X]
    : trunc n (Σ x, P x) ≃ Σ x, trunc n (P x) :=
  calc
    trunc n (Σ x, P x) ≃ trunc n (Σ x, trunc n (P x)) : trunc_sigma_equiv
      ... ≃ Σ x, trunc n (P x) : !trunc_equiv
  end

  /- the (non-dependent) universal property -/
  @[hott] def trunc_arrow_equiv [H : is_trunc n B] :
    (trunc n A → B) ≃ (A → B) :=
  begin
    fapply equiv.MK,
    { intros g a, exact g (tr a)},
    { intros f x, exact trunc.rec_on x f},
    { intro f, apply eq_of_homotopy, intro a, reflexivity},
    { intro g, apply eq_of_homotopy, intro x, exact trunc.rec_on x (λa, idp)},
  end

end trunc
