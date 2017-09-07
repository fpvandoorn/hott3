/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of mapping cylinders
-/

import hit.quotient types.fiber

open quotient eq sum equiv fiber

namespace cylinder
section

  parameters {A B : Type _} (f : A → B)

  local abbreviation C := B + A
  inductive cylinder_rel : C → C → Type _ :=
  | Rmk : Π(a : A), cylinder_rel (inl (f a)) (inr a)
  open cylinder_rel
  local abbreviation R := cylinder_rel

  @[hott] def cylinder := quotient cylinder_rel -- TODO: define this in root namespace

  parameter {f}
  @[hott] def base (b : B) : cylinder :=
  class_of R (inl b)

  @[hott] def top (a : A) : cylinder :=
  class_of R (inr a)

  @[hott] def seg (a : A) : base (f a) = top a :=
  eq_of_rel cylinder_rel (Rmk f a)

  protected @[hott] def rec {P : cylinder → Type _}
    (Pbase : Π(b : B), P (base b)) (Ptop : Π(a : A), P (top a))
    (Pseg : Π(a : A), Pbase (f a) =[seg a] Ptop a) (x : cylinder) : P x :=
  begin
    induction x,
    { cases a,
        apply Pbase,
        apply Ptop},
    { cases H, apply Pseg}
  end

  protected @[hott] def rec_on [reducible] {P : cylinder → Type _} (x : cylinder)
    (Pbase : Π(b : B), P (base b)) (Ptop  : Π(a : A), P (top a))
    (Pseg  : Π(a : A), Pbase (f a) =[seg a] Ptop a) : P x :=
  rec Pbase Ptop Pseg x

  @[hott] theorem rec_seg {P : cylinder → Type _}
    (Pbase : Π(b : B), P (base b)) (Ptop : Π(a : A), P (top a))
    (Pseg : Π(a : A), Pbase (f a) =[seg a] Ptop a)
      (a : A) : apd (rec Pbase Ptop Pseg) (seg a) = Pseg a :=
  !rec_eq_of_rel

  protected @[hott] def elim {P : Type _} (Pbase : B → P) (Ptop : A → P)
    (Pseg : Π(a : A), Pbase (f a) = Ptop a) (x : cylinder) : P :=
  rec Pbase Ptop (λa, pathover_of_eq _ (Pseg a)) x

  protected @[hott] def elim_on [reducible] {P : Type _} (x : cylinder) (Pbase : B → P) (Ptop : A → P)
    (Pseg : Π(a : A), Pbase (f a) = Ptop a) : P :=
  elim Pbase Ptop Pseg x

  @[hott] theorem elim_seg {P : Type _} (Pbase : B → P) (Ptop : A → P)
    (Pseg : Π(a : A), Pbase (f a) = Ptop a)
    (a : A) : ap (elim Pbase Ptop Pseg) (seg a) = Pseg a :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (seg a)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim,rec_seg],
  end

  protected @[hott] def elim_type (Pbase : B → Type _) (Ptop : A → Type _)
    (Pseg : Π(a : A), Pbase (f a) ≃ Ptop a) (x : cylinder) : Type _ :=
  elim Pbase Ptop (λa, ua (Pseg a)) x

  protected @[hott] def elim_type_on [reducible] (x : cylinder) (Pbase : B → Type _) (Ptop : A → Type _)
    (Pseg : Π(a : A), Pbase (f a) ≃ Ptop a) : Type _ :=
  elim_type Pbase Ptop Pseg x

  @[hott] theorem elim_type_seg (Pbase : B → Type _) (Ptop : A → Type _)
    (Pseg : Π(a : A), Pbase (f a) ≃ Ptop a)
    (a : A) : transport (elim_type Pbase Ptop Pseg) (seg a) = Pseg a :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_seg];apply cast_ua_fn

end

end cylinder

attribute cylinder.base cylinder.top
attribute cylinder.rec cylinder.elim [recursor 8]
attribute cylinder.elim_type
attribute cylinder.rec_on cylinder.elim_on
attribute cylinder.elim_type_on

namespace cylinder
  open sigma sigma.ops
  variables {A B : Type _} (f : A → B)

  /- cylinder as a dependent family -/
  @[hott] def pr1 : cylinder f → B :=
  cylinder.elim id f (λa, idp)

  @[hott] def fcylinder : B → Type _ := fiber (pr1 f)

  @[hott] def cylinder_equiv_sigma_fcylinder : cylinder f ≃ Σb, fcylinder f b :=
  !sigma_fiber_equiv⁻¹ᵉ

  variable {f}
  @[hott] def fbase (b : B) : fcylinder f b :=
  fiber.mk (base b) idp

  @[hott] def ftop (a : A) : fcylinder f (f a) :=
  fiber.mk (top a) idp

  @[hott] def fseg (a : A) : fbase (f a) = ftop a :=
  fiber_eq (seg a) !elim_seg⁻¹

-- TODO: define the induction principle for "fcylinder"
--   set_option pp.notation false
--   -- The induction principle for the dependent mapping cylinder (TODO)
--   protected @[hott] def frec {P : Π(b), fcylinder f b → Type _}
--     (Pbase : Π(b : B), P _ (fbase b)) (Ptop : Π(a : A), P _ (ftop a))
--     (Pseg : Π(a : A), Pbase (f a) =[fseg a] Ptop a) {b : B} (x : fcylinder f b) : P _ x :=
--   begin
--     cases x with x p, induction p,
--     induction x: esimp,
--     { apply Pbase},
--     { apply Ptop},
--     { esimp, --fapply fiber_pathover,
--              --refine pathover_of_pathover_ap P (λx, fiber.mk x idp),

-- exact sorry}
--   end

--   @[hott] theorem frec_fseg {P : Π(b), fcylinder f b → Type _}
--     (Pbase : Π(b : B), P _ (fbase b)) (Ptop : Π(a : A), P _ (ftop a))
--     (Pseg : Π(a : A), Pbase (f a) =[fseg a] Ptop a) (a : A)
--     : apd (cylinder.frec Pbase Ptop Pseg) (fseg a) = Pseg a :=
--   sorry


end cylinder
