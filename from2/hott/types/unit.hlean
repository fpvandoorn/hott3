/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Theorems about the unit type
-/

open is_equiv equiv option eq pointed is_trunc function

namespace unit

  @[hott] protected def eta : Π(u : unit), ⋆ = u
  | eta ⋆ := idp

  @[hott] def unit_equiv_option_empty : unit ≃ option empty :=
  begin
    fapply equiv.MK,
    { intro u, exact none},
    { intro e, exact star},
    { intro e, cases e, reflexivity, contradiction},
    { intro u, cases u, reflexivity},
  end

  -- equivalences involving unit and other type constructors are in the file
  -- of the other constructor

  /- pointed and truncated unit -/

  @[hott] def punit : Set* :=
  pSet.mk unit _ ⋆

  notation `unit*` := punit

  @[hott] def is_contr_punit [instance] : is_contr punit :=
  is_contr_unit

  @[hott] def unit_arrow_eq {X : Type _} (f : unit → X) : (λx, f ⋆) = f :=
  by apply eq_of_homotopy; intro u; induction u; reflexivity

  open funext
  @[hott] def unit_arrow_eq_compose {X Y : Type _} (g : X → Y) (f : unit → X) :
    unit_arrow_eq (g ∘ f) = ap (λf, g ∘ f) (unit_arrow_eq f) :=
  begin
    apply eq_of_fn_eq_fn' apd10,
    refine right_inv apd10 _ ⬝ _,
    refine _ ⬝ ap apd10 (!compose_eq_of_homotopy)⁻¹,
    refine _ ⬝ (right_inv apd10 _)⁻¹,
    apply eq_of_homotopy, intro u, induction u, reflexivity
  end

end unit
