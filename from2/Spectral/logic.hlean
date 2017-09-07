/-
Copyright (c) 2017 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad
-/
import types.trunc
open funext eq trunc is_trunc prod sum

--reserve prefix `¬`:40
--reserve prefix `~`:40
--reserve infixr ` ∧ `:35
--reserve infixr ` /\ `:35
--reserve infixr ` \/ `:30
--reserve infixr ` ∨ `:30
--reserve infix ` <-> `:20
--reserve infix ` ↔ `:20

namespace logic

section
open trunc_index

@[hott] def propext {p q : Prop} (h : p ↔ q) : p = q :=
tua (equiv_of_iff_of_is_prop h)

end

@[hott] def false : Prop := trunctype.mk (lift empty) _

@[hott] def false.elim {A : Type _} (h : false) : A := lift.rec empty.elim h

@[hott] def true : Prop := trunctype.mk (lift unit) _

@[hott] def true.intro : true := lift.up unit.star

@[hott] def trivial : true := lift.up unit.star

@[hott] def and (p q : Prop) : Prop := tprod p q

infixr ` ∧ ` := and
infixr ` /\ ` := and

@[hott] def and.intro {p q : Prop} (h₁ : p) (h₂ : q) : and p q := prod.mk h₁ h₂

@[hott] def and.left {p q : Prop} (h : p ∧ q) : p := prod.pr1 h

@[hott] def and.right {p q : Prop} (h : p ∧ q) : q := prod.pr2 h

@[hott] def not (p : Prop) : Prop := trunctype.mk (p → empty) _

@[hott] def or.inl := @or.intro_left

@[hott] def or.inr := @or.intro_right

@[hott] def or.elim {A B C : Type _} [is_prop C] (h₀ : A ∨ B) (h₁ : (A → C)) (h₂ : B → C) : C :=
begin
  apply trunc.elim_on h₀,
  intro h₃,
  apply sum.elim h₃ h₁ h₂
end

end logic
