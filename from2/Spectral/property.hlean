/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import types.trunc .logic
open funext eq trunc is_trunc logic

@[hott] def property (X : Type _) := X → Prop

namespace property

variable {X : Type _}

/- membership and subproperty -/

@[hott] def mem (x : X) (a : property X) := a x
infix ∈ := mem
notation a ∉ b := ¬ mem a b

/-@[hott] theorem ext {a b : property X} (H : ∀x, x ∈ a ↔ x ∈ b) : a = b :=
eq_of_homotopy (take x, propext (H x))
-/

@[hott] def subproperty (a b : property X) : Prop := Prop.mk (∀⦃x⦄, x ∈ a → x ∈ b) _
infix ⊆ := subproperty

@[hott] def superproperty (s t : property X) : Prop := t ⊆ s
infix ⊇ := superproperty

@[hott] theorem subproperty.refl (a : property X) : a ⊆ a := take x, assume H, H

@[hott] theorem subproperty.trans {a b c : property X} (subab : a ⊆ b) (subbc : b ⊆ c) : a ⊆ c :=
take x, assume ax, subbc (subab ax)

/-
@[hott] theorem subproperty.antisymm {a b : property X} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
ext (λ x, iff.intro (λ ina, h₁ ina) (λ inb, h₂ inb))
-/

-- an alterantive name
/-
@[hott] theorem eq_of_subproperty_of_subproperty {a b : property X} (h₁ : a ⊆ b) (h₂ : b ⊆ a) : a = b :=
subproperty.antisymm h₁ h₂
-/

@[hott] theorem exteq_of_subproperty_of_subproperty {a b : property X} (h₁ : a ⊆ b) (h₂ : b ⊆ a) :
  ∀ ⦃x⦄, x ∈ a ↔ x ∈ b :=
λ x, iff.intro (λ h, h₁ h) (λ h, h₂ h)

@[hott] theorem mem_of_subproperty_of_mem {s₁ s₂ : property X} {a : X} : s₁ ⊆ s₂ → a ∈ s₁ → a ∈ s₂ :=
assume h₁ h₂, h₁ _ h₂

/- empty property -/

@[hott] def empty : property X := λx, false
notation `∅` := property.empty

@[hott] theorem not_mem_empty (x : X) : ¬ (x ∈ ∅) :=
assume H : x ∈ ∅, false.elim H

@[hott] theorem mem_empty_eq (x : X) : x ∈ ∅ = false := rfl

/-
@[hott] theorem eq_empty_of_forall_not_mem {s : property X} (H : ∀ x, x ∉ s) : s = ∅ :=
ext (take x, iff.intro
  (assume xs, absurd xs (H x))
  (assume xe, absurd xe (not_mem_empty x)))
-/

@[hott] theorem ne_empty_of_mem {s : property X} {x : X} (H : x ∈ s) : s ≠ ∅ :=
  begin intro Hs, rewrite Hs at H, apply not_mem_empty x H end

@[hott] theorem empty_subproperty (s : property X) : ∅ ⊆ s :=
take x, assume H, false.elim H

/-@[hott] theorem eq_empty_of_subproperty_empty {s : property X} (H : s ⊆ ∅) : s = ∅ :=
subproperty.antisymm H (empty_subproperty s)

@[hott] theorem subproperty_empty_iff (s : property X) : s ⊆ ∅ ↔ s = ∅ :=
iff.intro eq_empty_of_subproperty_empty (take xeq, by rewrite xeq; apply subproperty.refl ∅)
-/

/- universal property -/

@[hott] def univ : property X := λx, true

@[hott] theorem mem_univ (x : X) : x ∈ univ := trivial

@[hott] theorem mem_univ_eq (x : X) : x ∈ univ = true := rfl

@[hott] theorem empty_ne_univ [h : inhabited X] : (empty : property X) ≠ univ :=
assume H : empty = univ,
absurd (mem_univ (inhabited.value h)) (eq.rec_on H (not_mem_empty (arbitrary X)))

@[hott] theorem subproperty_univ (s : property X) : s ⊆ univ := λ x H, trivial

/-
@[hott] theorem eq_univ_of_univ_subproperty {s : property X} (H : univ ⊆ s) : s = univ :=
eq_of_subproperty_of_subproperty (subproperty_univ s) H
-/

/-
@[hott] theorem eq_univ_of_forall {s : property X} (H : ∀ x, x ∈ s) : s = univ :=
ext (take x, iff.intro (assume H', trivial) (assume H', H x))
-/

/- union -/

@[hott] def union (a b : property X) : property X := λx, x ∈ a ∨ x ∈ b
notation a ∪ b := union a b

@[hott] theorem mem_union_left {x : X} {a : property X} (b : property X) : x ∈ a → x ∈ a ∪ b :=
assume h, or.inl h

@[hott] theorem mem_union_right {x : X} {b : property X} (a : property X) : x ∈ b → x ∈ a ∪ b :=
assume h, or.inr h

@[hott] theorem mem_unionl {x : X} {a b : property X} : x ∈ a → x ∈ a ∪ b :=
assume h, or.inl h

@[hott] theorem mem_unionr {x : X} {a b : property X} : x ∈ b → x ∈ a ∪ b :=
assume h, or.inr h

@[hott] theorem mem_or_mem_of_mem_union {x : X} {a b : property X} (H : x ∈ a ∪ b) : x ∈ a ∨ x ∈ b := H

@[hott] theorem mem_union.elim {x : X} {a b : property X} {P : Prop}
    (H₁ : x ∈ a ∪ b) (H₂ : x ∈ a → P) (H₃ : x ∈ b → P) : P :=
or.elim H₁ H₂ H₃

@[hott] theorem mem_union_iff (x : X) (a b : property X) : x ∈ a ∪ b ↔ x ∈ a ∨ x ∈ b := !iff.refl

@[hott] theorem mem_union_eq (x : X) (a b : property X) : x ∈ a ∪ b = (x ∈ a ∨ x ∈ b) := rfl

--@[hott] theorem union_self (a : property X) : a ∪ a = a :=
--ext (take x, !or_self)

--@[hott] theorem union_empty (a : property X) : a ∪ ∅ = a :=
--ext (take x, !or_false)

--@[hott] theorem empty_union (a : property X) : ∅ ∪ a = a :=
--ext (take x, !false_or)

--@[hott] theorem union_comm (a b : property X) : a ∪ b = b ∪ a :=
--ext (take x, or.comm)

--@[hott] theorem union_assoc (a b c : property X) : (a ∪ b) ∪ c = a ∪ (b ∪ c) :=
--ext (take x, or.assoc)

--@[hott] theorem union_left_comm (s₁ s₂ s₃ : property X) : s₁ ∪ (s₂ ∪ s₃) = s₂ ∪ (s₁ ∪ s₃) :=
--!left_comm union_comm union_assoc s₁ s₂ s₃

--@[hott] theorem union_right_comm (s₁ s₂ s₃ : property X) : (s₁ ∪ s₂) ∪ s₃ = (s₁ ∪ s₃) ∪ s₂ :=
--!right_comm union_comm union_assoc s₁ s₂ s₃

@[hott] theorem subproperty_union_left (s t : property X) : s ⊆ s ∪ t := λ x H, or.inl H

@[hott] theorem subproperty_union_right (s t : property X) : t ⊆ s ∪ t := λ x H, or.inr H

@[hott] theorem union_subproperty {s t r : property X} (sr : s ⊆ r) (tr : t ⊆ r) : s ∪ t ⊆ r :=
λ x xst, or.elim xst (λ xs, sr xs) (λ xt, tr xt)

/- intersection -/

@[hott] def inter (a b : property X) : property X := λx, x ∈ a ∧ x ∈ b
notation a ∩ b := inter a b

@[hott] theorem mem_inter_iff (x : X) (a b : property X) : x ∈ a ∩ b ↔ x ∈ a ∧ x ∈ b := !iff.refl

@[hott] theorem mem_inter_eq (x : X) (a b : property X) : x ∈ a ∩ b = (x ∈ a ∧ x ∈ b) := rfl

@[hott] theorem mem_inter {x : X} {a b : property X} (Ha : x ∈ a) (Hb : x ∈ b) : x ∈ a ∩ b :=
and.intro Ha Hb

@[hott] theorem mem_of_mem_inter_left {x : X} {a b : property X} (H : x ∈ a ∩ b) : x ∈ a :=
and.left H

@[hott] theorem mem_of_mem_inter_right {x : X} {a b : property X} (H : x ∈ a ∩ b) : x ∈ b :=
and.right H

--@[hott] theorem inter_self (a : property X) : a ∩ a = a :=
--ext (take x, !and_self)

--@[hott] theorem inter_empty (a : property X) : a ∩ ∅ = ∅ :=
--ext (take x, !and_false)

--@[hott] theorem empty_inter (a : property X) : ∅ ∩ a = ∅ :=
--ext (take x, !false_and)

--@[hott] theorem nonempty_of_inter_nonempty_right {T : Type _} {s t : property T} (H : s ∩ t ≠ ∅) : t ≠ ∅ :=
--suppose t = ∅,
--have s ∩ t = ∅, by rewrite this; apply inter_empty,
--H this

--@[hott] theorem nonempty_of_inter_nonempty_left {T : Type _} {s t : property T} (H : s ∩ t ≠ ∅) : s ≠ ∅ :=
--suppose s = ∅,
--have s ∩ t = ∅, by rewrite this; apply empty_inter,
--H this

--@[hott] theorem inter_comm (a b : property X) : a ∩ b = b ∩ a :=
--ext (take x, !and.comm)

--@[hott] theorem inter_assoc (a b c : property X) : (a ∩ b) ∩ c = a ∩ (b ∩ c) :=
--ext (take x, !and.assoc)

--@[hott] theorem inter_left_comm (s₁ s₂ s₃ : property X) : s₁ ∩ (s₂ ∩ s₃) = s₂ ∩ (s₁ ∩ s₃) :=
--!left_comm inter_comm inter_assoc s₁ s₂ s₃

--@[hott] theorem inter_right_comm (s₁ s₂ s₃ : property X) : (s₁ ∩ s₂) ∩ s₃ = (s₁ ∩ s₃) ∩ s₂ :=
--!right_comm inter_comm inter_assoc s₁ s₂ s₃

--@[hott] theorem inter_univ (a : property X) : a ∩ univ = a :=
--ext (take x, !and_true)

--@[hott] theorem univ_inter (a : property X) : univ ∩ a = a :=
--ext (take x, !true_and)

@[hott] theorem inter_subproperty_left (s t : property X) : s ∩ t ⊆ s := λ x H, and.left H

@[hott] theorem inter_subproperty_right (s t : property X) : s ∩ t ⊆ t := λ x H, and.right H

@[hott] theorem inter_subproperty_inter_right {s t : property X} (u : property X) (H : s ⊆ t) : s ∩ u ⊆ t ∩ u :=
take x, assume xsu, and.intro (H (and.left xsu)) (and.right xsu)

@[hott] theorem inter_subproperty_inter_left {s t : property X} (u : property X) (H : s ⊆ t) : u ∩ s ⊆ u ∩ t :=
take x, assume xus, and.intro (and.left xus) (H (and.right xus))

@[hott] theorem subproperty_inter {s t r : property X} (rs : r ⊆ s) (rt : r ⊆ t) : r ⊆ s ∩ t :=
λ x xr, and.intro (rs xr) (rt xr)

--@[hott] theorem not_mem_of_mem_of_not_mem_inter_left {s t : property X} {x : X} (Hxs : x ∈ s) (Hnm : x ∉ s ∩ t) : x ∉ t :=
--  suppose x ∈ t,
--  have x ∈ s ∩ t, from and.intro Hxs this,
--  show false, from Hnm this

--@[hott] theorem not_mem_of_mem_of_not_mem_inter_right {s t : property X} {x : X} (Hxs : x ∈ t) (Hnm : x ∉ s ∩ t) : x ∉ s :=
--  suppose x ∈ s,
--  have x ∈ s ∩ t, from and.intro this Hxs,
--  show false, from Hnm this

/- distributivity laws -/

--@[hott] theorem inter_distrib_left (s t u : property X) : s ∩ (t ∪ u) = (s ∩ t) ∪ (s ∩ u) :=
--ext (take x, !and.left_distrib)

--@[hott] theorem inter_distrib_right (s t u : property X) : (s ∪ t) ∩ u = (s ∩ u) ∪ (t ∩ u) :=
--ext (take x, !and.right_distrib)

--@[hott] theorem union_distrib_left (s t u : property X) : s ∪ (t ∩ u) = (s ∪ t) ∩ (s ∪ u) :=
--ext (take x, !or.left_distrib)

--@[hott] theorem union_distrib_right (s t u : property X) : (s ∩ t) ∪ u = (s ∪ u) ∩ (t ∪ u) :=
--ext (take x, !or.right_distrib)


/- property-builder notation -/

-- {x : X | P}
@[hott] def property_of (P : X → Prop) : property X := P
notation `{` binder ` | ` r:(scoped:1 P, property_of P) `}` := r

@[hott] theorem mem_property_of {P : X → Prop} {a : X} (h : P a) : a ∈ {x | P x} := h

@[hott] theorem of_mem_property_of {P : X → Prop} {a : X} (h : a ∈ {x | P x}) : P a := h

-- {x ∈ s | P}
@[hott] def sep (P : X → Prop) (s : property X) : property X := λx, x ∈ s ∧ P x
notation `{` binder ` ∈ ` s ` | ` r:(scoped:1 p, sep p s) `}` := r

/- insert -/

@[hott] def insert (x : X) (a : property X) : property X := {y : X | y = x ∨ y ∈ a}

abbreviation insert_same_level.{u} := @insert.{u u}

-- '{x, y, z}
notation `'{`:max a:(foldr `, ` (x b, insert_same_level x b) ∅) `}`:0 := a

@[hott] theorem subproperty_insert (x : X) (a : property X) : a ⊆ insert x a :=
take y, assume ys, or.inr ys

@[hott] theorem mem_insert (x : X) (s : property X) : x ∈ insert x s :=
or.inl rfl

@[hott] theorem mem_insert_of_mem {x : X} {s : property X} (y : X) : x ∈ s → x ∈ insert y s :=
assume h, or.inr h

@[hott] theorem eq_or_mem_of_mem_insert {x a : X} {s : property X} : x ∈ insert a s → x = a ∨ x ∈ s :=
assume h, h

/- singleton -/

open trunc_index

@[hott] theorem mem_singleton_iff {X : Type _} [is_set X] (a b : X) : a ∈ '{b} ↔ a = b :=
iff.intro
  (assume ainb, or.elim ainb (λ aeqb, aeqb) (λ f, false.elim f))
  (assume aeqb, or.inl aeqb)

@[hott] theorem mem_singleton (a : X) : a ∈ '{a} := !mem_insert

@[hott] theorem eq_of_mem_singleton {X : Type _} [is_set X] {x y : X} (h : x ∈ '{y}) : x = y :=
or.elim (eq_or_mem_of_mem_insert h)
  (suppose x = y, this)
  (suppose x ∈ ∅, absurd this (not_mem_empty x))

@[hott] theorem mem_singleton_of_eq {x y : X} (H : x = y) : x ∈ '{y} :=
eq.symm H ▸ mem_singleton y

/-
@[hott] theorem insert_eq (x : X) (s : property X) : insert x s = '{x} ∪ s :=
ext (take y, iff.intro
  (suppose y ∈ insert x s,
    or.elim this (suppose y = x, or.inl (or.inl this)) (suppose y ∈ s, or.inr this))
  (suppose y ∈ '{x} ∪ s,
    or.elim this
      (suppose y ∈ '{x}, or.inl (eq_of_mem_singleton this))
      (suppose y ∈ s, or.inr this)))
-/

/-
@[hott] theorem pair_eq_singleton (a : X) : '{a, a} = '{a} :=
by rewrite [insert_eq_of_mem !mem_singleton]
-/
/-
@[hott] theorem singleton_ne_empty (a : X) : '{a} ≠ ∅ :=
begin
  intro H,
  apply not_mem_empty a,
  rewrite -H,
  apply mem_insert
end
-/

end property
