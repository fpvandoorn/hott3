/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

The @[hott] def of pointed types. This file is here to avoid circularities in the import graph
-/

prelude
import init.trunc

open eq equiv is_equiv is_trunc

structure pointed [class] (A : Type _) :=
  (point : A)

structure pType :=
  (carrier : Type _)
  (Point   : carrier)

notation `Type*` := pType

namespace pointed
  attribute pType.carrier [coercion]
  variables {A : Type _}

  @[hott] def pt [reducible] [H : pointed A] := point A
  @[hott] def Point [reducible] (A : Type*) := pType.Point A
  @[hott] def carrier [reducible] (A : Type*) := pType.carrier A
  protected @[hott] def Mk {A : Type _} (a : A) := pType.mk A a
  protected @[hott] def MK (A : Type _) (a : A) := pType.mk A a
  protected @[hott] def mk' (A : Type _) [H : pointed A] : Type* :=
  pType.mk A (point A)
  @[hott] def pointed_carrier [instance] (A : Type*) : pointed A :=
  pointed.mk (Point A)

end pointed
open pointed

section
  universe variable u
  structure ptrunctype (n : ℕ₋₂) extends trunctype.{u} n, pType.{u}

  @[hott] def is_trunc_ptrunctype [instance] {n : ℕ₋₂} (X : ptrunctype n)
    : is_trunc n (ptrunctype.to_pType X) :=
  trunctype.struct X

end

notation n `-Type*` := ptrunctype n
abbreviation pSet  [parsing_only] := 0-Type*
notation `Set*` := pSet

namespace pointed

  protected @[hott] def ptrunctype.mk' (n : ℕ₋₂)
    (A : Type _) [pointed A] [is_trunc n A] : n-Type* :=
  ptrunctype.mk A _ pt

  protected @[hott] def pSet.mk := @ptrunctype.mk (-1.+1)
  protected @[hott] def pSet.mk' := ptrunctype.mk' (-1.+1)

  @[hott] def ptrunctype_of_trunctype {n : ℕ₋₂} (A : n-Type _) (a : A)
    : n-Type* :=
  ptrunctype.mk A _ a

  @[hott] def ptrunctype_of_pType {n : ℕ₋₂} (A : Type*) (H : is_trunc n A)
    : n-Type* :=
  ptrunctype.mk A _ pt

  @[hott] def pSet_of_Set (A : Set) (a : A) : Set* :=
  ptrunctype.mk A _ a

  @[hott] def pSet_of_pType (A : Type*) (H : is_set A) : Set* :=
  ptrunctype.mk A _ pt

  attribute ptrunctype._trans_of_to_pType ptrunctype.to_pType ptrunctype.to_trunctype

  -- Any contractible type is pointed
  @[hott] def pointed_of_is_contr [instance] [priority 800]
    (A : Type _) [H : is_contr A] : pointed A :=
  pointed.mk !center

end pointed

/- pointed maps -/
structure ppi {A : Type*} (P : A → Type _) (x₀ : P pt) :=
  (to_fun : Π a : A, P a)
  (resp_pt : to_fun (Point A) = x₀)

@[hott] def pppi' [reducible] {A : Type*} (P : A → Type*) : Type _ :=
ppi P pt

@[hott] def ppi_const {A : Type*} (P : A → Type*) : pppi' P :=
ppi.mk (λa, pt) idp

@[hott] def pppi [reducible] {A : Type*} (P : A → Type*) : Type* :=
pointed.MK (pppi' P) (ppi_const P)

-- do we want to make this already pointed?
@[hott] def pmap [reducible] (A B : Type*) : Type _ := @pppi A (λa, B)

attribute ppi.to_fun [coercion]

infix ` →* `:28 := pmap
notation `Π*` binders `, ` r:(scoped P, pppi P) := r


namespace pointed


  @[hott] def pppi.mk [reducible] {A : Type*} {P : A → Type*} (f : Πa, P a)
    (p : f pt = pt) : pppi P :=
  ppi.mk f p

  @[hott] def pppi.to_fun [coercion] [reducible] {A : Type*} {P : A → Type*} (f : pppi' P)
    (a : A) : P a :=
  ppi.to_fun f a

	@[hott] def pmap.mk [reducible] {A B : Type*} (f : A → B)
    (p : f (Point A) = Point B) : A →* B :=
	pppi.mk f p

  abbreviation pmap.to_fun [reducible] [coercion] {A B : Type*} (f : A →* B) : A → B :=
  pppi.to_fun f

  @[hott] def respect_pt [reducible] {A : Type*} {P : A → Type _} {p₀ : P pt}
    (f : ppi P p₀) : f pt = p₀ :=
  ppi.resp_pt f

  -- notation `Π*` binders `, ` r:(scoped P, ppi _ P) := r
  -- @[hott] def pmxap.mk {A B : Type*} (f : A → B) (p : f pt = pt) : A →* B :=
  -- ppi.mk f p
  -- @[hott] def pmap.to_fun [coercion] {A B : Type*} (f : A →* B) : A → B := f

end pointed open pointed

/- pointed homotopies -/
@[hott] def phomotopy {A : Type*} {P : A → Type _} {p₀ : P pt} (f g : ppi P p₀) : Type _ :=
ppi (λa, f a = g a) (respect_pt f ⬝ (respect_pt g)⁻¹)

-- structure phomotopy {A B : Type*} (f g : A →* B) : Type _ :=
--   (homotopy : f ~ g)
--   (homotopy_pt : homotopy pt ⬝ respect_pt g = respect_pt f)

namespace pointed
  variables {A : Type*} {P : A → Type _} {p₀ : P pt} {f g : ppi P p₀}

  infix ` ~* `:50 := phomotopy
  @[hott] def phomotopy.mk [reducible] (h : f ~ g)
    (p : h pt ⬝ respect_pt g = respect_pt f) : f ~* g :=
  ppi.mk h (eq_con_inv_of_con_eq p)

  @[hott] def to_homotopy [coercion] [reducible] (p : f ~* g) : Πa, f a = g a := p
  @[hott] def to_homotopy_pt [reducible] (p : f ~* g) :
    p pt ⬝ respect_pt g = respect_pt f :=
  con_eq_of_eq_con_inv (respect_pt p)


end pointed
