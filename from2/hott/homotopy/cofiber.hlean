/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

The Cofiber Type _
-/
import hit.pushout function .susp types.unit

open eq pushout unit pointed is_trunc is_equiv susp unit equiv

@[hott] def cofiber {A B : Type _} (f : A → B) := pushout f (λ (a : A), ⋆)

namespace cofiber
  section
  parameters {A B : Type _} (f : A → B)

  @[hott] def cod : B → cofiber f := inl
  @[hott] def base : cofiber f := inr ⋆

  parameter {f}
  @[hott] protected def glue (a : A) : cofiber.cod f (f a) = cofiber.base f :=
  pushout.glue a

  @[hott] protected def rec {P : cofiber f → Type _} (Pcod : Π (b : B), P (cod b)) (Pbase : P base)
    (Pglue : Π (a : A), pathover P (Pcod (f a)) (glue a) Pbase) :
    (Π y, P y) :=
  begin
    intro y, induction y, exact Pcod x, induction x, exact Pbase, exact Pglue x
  end

  @[hott] protected def rec_on {P : cofiber f → Type _} (y : cofiber f)
    (Pcod : Π (b : B), P (cod b)) (Pbase : P base)
    (Pglue : Π (a : A), pathover P (Pcod (f a)) (glue a) Pbase) : P y :=
  cofiber.rec Pcod Pbase Pglue y

  @[hott] protected theorem rec_glue {P : cofiber f → Type _} (Pcod : Π (b : B), P (cod b)) (Pbase : P base)
    (Pglue : Π (a : A), pathover P (Pcod (f a)) (glue a) Pbase) (a : A)
    : apd (cofiber.rec Pcod Pbase Pglue) (cofiber.glue a) = Pglue a :=
  !pushout.rec_glue

  @[hott] protected def elim {P : Type _} (Pcod : B → P) (Pbase : P)
    (Pglue : Π (x : A), Pcod (f x) = Pbase) (y : cofiber f) : P :=
  pushout.elim Pcod (λu, Pbase) Pglue y

  @[hott] protected def elim_on {P : Type _} (y : cofiber f) (Pcod : B → P) (Pbase : P)
    (Pglue : Π (x : A), Pcod (f x) = Pbase) : P :=
  cofiber.elim Pcod Pbase Pglue y

  @[hott] protected theorem elim_glue {P : Type _} (Pcod : B → P) (Pbase : P)
    (Pglue : Π (x : A), Pcod (f x) = Pbase) (a : A)
    : ap (cofiber.elim Pcod Pbase Pglue) (cofiber.glue a) = Pglue a :=
  !pushout.elim_glue

  end

end cofiber

attribute cofiber.base cofiber.cod
attribute cofiber.rec cofiber.elim [recursor 8]
attribute cofiber.rec_on cofiber.elim_on

-- pointed version

@[hott] def pcofiber {A B : Type*} (f : A →* B) : Type* :=
pointed.MK (cofiber f) !cofiber.base

notation `ℂ` := pcofiber

namespace cofiber

  variables {A B : Type*} (f : A →* B)

  @[hott] def is_contr_cofiber_of_equiv [H : is_equiv f] : is_contr (cofiber f) :=
  begin
    fapply is_contr.mk, exact cofiber.base f,
    intro a, induction a with b a,
    { exact !glue⁻¹ ⬝ ap inl (right_inv f b) },
    { reflexivity },
    { apply eq_pathover_constant_left_id_right, apply move_top_of_left,
      refine _ ⬝pv natural_square_tr cofiber.glue (left_inv f a) ⬝vp !ap_constant,
      refine ap02 inl _ ⬝ !ap_compose⁻¹, exact adj f a },
  end

  @[hott] def pcod (f : A →* B) : B →* pcofiber f :=
  pmap.mk (cofiber.cod f) (ap inl (respect_pt f)⁻¹ ⬝ cofiber.glue pt)

  @[hott] def pcod_pcompose (f : A →* B) : pcod f ∘* f ~* pconst A (ℂ f) :=
  begin
    fapply phomotopy.mk,
    { intro a, exact cofiber.glue a },
    { exact !con_inv_cancel_left⁻¹ ⬝ idp ◾ (!ap_inv⁻¹ ◾ idp) }
  end

  @[hott] def pcofiber_punit (A : Type*) : pcofiber (pconst A punit) ≃* susp A :=
  begin
    fapply pequiv_of_pmap,
    { fapply pmap.mk, intro x, induction x, exact north, exact south, exact merid x,
      exact (merid pt)⁻¹ },
    { esimp, fapply adjointify,
      { intro s, induction s, exact inl ⋆, exact inr ⋆, apply glue a },
      { intro s, induction s, do 2 reflexivity, esimp,
        apply eq_pathover, refine _ ⬝hp !ap_id⁻¹, apply hdeg_square,
        refine !(ap_compose (pushout.elim _ _ _)) ⬝ _,
        refine ap _ !elim_merid ⬝ _, apply elim_glue },
      { intro c, induction c with u, induction u, reflexivity,
        reflexivity, esimp, apply eq_pathover, apply hdeg_square,
        refine _ ⬝ !ap_id⁻¹, refine !(ap_compose (pushout.elim _ _ _)) ⬝ _,
        refine ap02 _ !elim_glue ⬝ _, apply elim_merid }},
  end

end cofiber
