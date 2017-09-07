/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura
-/

prelude
import init.logic

-- TODO(Leo): remove duplication between this file and algebra/relation.lean
-- We need some of the following definitions asap when "initializing" Lean.

variables {A B : Type _} (R : B → B → Type _)
local infix `≺`:50 := R

@[hott] def reflexive := ∀x, x ≺ x

@[hott] def symmetric := ∀⦃x y⦄, x ≺ y → y ≺ x

@[hott] def transitive := ∀⦃x y z⦄, x ≺ y → y ≺ z → x ≺ z

@[hott] def irreflexive := ∀x, ¬ x ≺ x

@[hott] def anti_symmetric := ∀⦃x y⦄, x ≺ y → y ≺ x → x = y

@[hott] def empty_relation := λa₁ a₂ : A, empty

@[hott] def subrelation (Q R : B → B → Type _) := ∀⦃x y⦄, Q x y → R x y

@[hott] def inv_image (f : A → B) : A → A → Type _ :=
λa₁ a₂, f a₁ ≺ f a₂

@[hott] def inv_image.trans (f : A → B) (H : transitive R) : transitive (inv_image R f) :=
λ (a₁ a₂ a₃ : A) (H₁ : inv_image R f a₁ a₂) (H₂ : inv_image R f a₂ a₃), H H₁ H₂

@[hott] def inv_image.irreflexive (f : A → B) (H : irreflexive R) : irreflexive (inv_image R f) :=
λ (a : A) (H₁ : inv_image R f a a), H (f a) H₁

inductive tc {A : Type _} (R : A → A → Type _) : A → A → Type _ :=
| base  : ∀a b, R a b → tc R a b
| trans : ∀a b c, tc R a b → tc R b c → tc R a c
