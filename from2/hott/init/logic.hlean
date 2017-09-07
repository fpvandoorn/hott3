/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Floris van Doorn
-/

prelude
import init.reserved_notation
open unit

@[hott] def id [reducible] {A : Type _} (a : A) : A :=
a

/- not -/

@[hott] def not [reducible] (a : Type _) := a → empty
prefix ¬ := not

@[hott] def absurd {a b : Type _} (H₁ : a) (H₂ : ¬a) : b :=
empty.rec (λ e, b) (H₂ H₁)

@[hott] def mt {a b : Type _} (H₁ : a → b) (H₂ : ¬b) : ¬a :=
assume Ha : a, absurd (H₁ Ha) H₂

@[hott] def not_empty : ¬empty :=
assume H : empty, H

@[hott] def non_contradictory (a : Type _) : Type _ := ¬¬a

@[hott] def non_contradictory_intro {a : Type _} (Ha : a) : ¬¬a :=
assume Hna : ¬a, absurd Ha Hna

@[hott] def not.intro {a : Type _} (H : a → empty) : ¬a := H

/- empty -/

@[hott] def empty.elim {c : Type _} (H : empty) : c :=
empty.rec _ H

/- eq -/

infix = := eq
@[hott] def rfl {A : Type _} {a : A} := eq.refl a

/-
  These notions are here only to make porting from the standard library easier.
  They are defined again in init/path.hlean, and those definitions will be used
  throughout the HoTT-library. That's why the notation for eq below is only local.
-/
namespace eq
  variables {A : Type _} {a b c : A}

  @[hott] def subst {P : A → Type _} (H₁ : a = b) (H₂ : P a) : P b :=
  eq.rec H₂ H₁

  @[hott] def trans (H₁ : a = b) (H₂ : b = c) : a = c :=
  subst H₂ H₁

  @[hott] def symm (H : a = b) : b = a :=
  subst H (refl a)

  @[hott] def mp {a b : Type _} : (a = b) → a → b :=
  eq.rec_on

  @[hott] def mpr {a b : Type _} : (a = b) → b → a :=
  assume H₁ H₂, eq.rec_on (eq.symm H₁) H₂

  namespace ops end ops -- this is just to ensure that this namespace exists. There is nothing in it
end eq

local postfix ⁻¹ := eq.symm --input with \sy or \-1 or \inv
local infixl ⬝ := eq.trans
local infixr ▸ := eq.subst

-- Auxiliary @[hott] def used by automation. It has the same type of eq.rec in the standard library
@[hott] def eq.nrec.{l₁ l₂} {A : Type l₂} {a : A} {C : A → Type l₁} (H₁ : C a) (b : A) (H₂ : a = b) : C b :=
eq.rec H₁ H₂

@[hott] def congr {A B : Type _} {f₁ f₂ : A → B} {a₁ a₂ : A} (H₁ : f₁ = f₂) (H₂ : a₁ = a₂) : f₁ a₁ = f₂ a₂ :=
eq.subst H₁ (eq.subst H₂ rfl)

@[hott] def congr_fun {A : Type _} {B : A → Type _} {f g : Π x, B x} (H : f = g) (a : A) : f a = g a :=
eq.subst H (eq.refl (f a))

@[hott] def congr_arg {A B : Type _} (a a' : A) (f : A → B) (Ha : a = a') : f a = f a' :=
eq.subst Ha rfl

@[hott] def congr_arg2 {A B C : Type _} (a a' : A) (b b' : B) (f : A → B → C) (Ha : a = a') (Hb : b = b') : f a b = f a' b' :=
eq.subst Ha (eq.subst Hb rfl)

section
  variables {A : Type _} {a b c: A}
  open eq.ops

  @[hott] def trans_rel_left (R : A → A → Type _) (H₁ : R a b) (H₂ : b = c) : R a c :=
  H₂ ▸ H₁

  @[hott] def trans_rel_right (R : A → A → Type _) (H₁ : a = b) (H₂ : R b c) : R a c :=
  H₁⁻¹ ▸ H₂
end

attribute eq.subst [subst]
attribute eq.refl [refl]
attribute eq.trans [trans]
attribute eq.symm [symm]

namespace lift
  @[hott] def down_up.{l₁ l₂} {A : Type l₁} (a : A) : down (up.{l₁ l₂} a) = a :=
  rfl

  @[hott] def up_down.{l₁ l₂} {A : Type l₁} (a : lift.{l₁ l₂} A) : up (down a) = a :=
  lift.rec_on a (λ d, rfl)
end lift

/- ne -/

@[hott] def ne [reducible] {A : Type _} (a b : A) := ¬(a = b)
notation a ≠ b := ne a b

namespace ne
  open eq.ops
  variable {A : Type _}
  variables {a b : A}

  @[hott] def intros (H : a = b → empty) : a ≠ b := H

  @[hott] def elim (H : a ≠ b) : a = b → empty := H

  @[hott] def irrefl (H : a ≠ a) : empty := H rfl

  @[hott] def symm (H : a ≠ b) : b ≠ a :=
  assume (H₁ : b = a), H (H₁⁻¹)
end ne

@[hott] def empty_of_ne {A : Type _} {a : A} : a ≠ a → empty := ne.irrefl

section
  open eq.ops
  variables {p : Type}

  @[hott] def ne_empty_of_self : p → p ≠ empty :=
  assume (Hp : p) (Heq : p = empty), Heq ▸ Hp

  @[hott] def ne_unit_of_not : ¬p → p ≠ unit :=
  assume (Hnp : ¬p) (Heq : p = unit), (Heq ▸ Hnp) star

  @[hott] def unit_ne_empty : ¬unit = empty :=
  ne_empty_of_self star
end

/- prod -/

abbreviation pair := @prod.mk
infixr × := prod

variables {a b c d : Type _}

attribute prod.rec [elim]
attribute prod.mk [intro!]

protected @[hott] def prod.elim (H₁ : a × b) (H₂ : a → b → c) : c :=
prod.rec H₂ H₁

@[hott] def prod.swap : a × b → b × a :=
prod.rec (λHa Hb, prod.mk Hb Ha)

/- sum -/

infixr ⊎ := sum

attribute sum.rec [elim]

protected @[hott] def sum.elim (H₁ : a ⊎ b) (H₂ : a → c) (H₃ : b → c) : c :=
sum.rec H₂ H₃ H₁

@[hott] def non_contradictory_em (a : Type _) : ¬¬(a ⊎ ¬a) :=
assume not_em : ¬(a ⊎ ¬a),
  have neg_a : ¬a, from
    assume pos_a : a, absurd (sum.inl pos_a) not_em,
  absurd (sum.inr neg_a) not_em

@[hott] def sum.swap : a ⊎ b → b ⊎ a := sum.rec sum.inr sum.inl


/- iff -/

@[hott] def iff (a b : Type _) := (a → b) × (b → a)

notation a <-> b := iff a b
notation a ↔ b := iff a b

@[hott] def iff.intro : (a → b) → (b → a) → (a ↔ b) := prod.mk

attribute iff.intro [intro!]

@[hott] def iff.elim : ((a → b) → (b → a) → c) → (a ↔ b) → c := prod.rec

attribute iff.elim [recursor 5] [elim]

@[hott] def iff.elim_left : (a ↔ b) → a → b := prod.pr1

@[hott] def iff.mp := @iff.elim_left

@[hott] def iff.elim_right : (a ↔ b) → b → a := prod.pr2

@[hott] def iff.mpr := @iff.elim_right

@[hott] def iff.refl [refl] (a : Type _) : a ↔ a :=
iff.intro (assume H, H) (assume H, H)

@[hott] def iff.rfl {a : Type _} : a ↔ a :=
iff.refl a

@[hott] def iff.trans [trans] (H₁ : a ↔ b) (H₂ : b ↔ c) : a ↔ c :=
iff.intro
  (assume Ha, iff.mp H₂ (iff.mp H₁ Ha))
  (assume Hc, iff.mpr H₁ (iff.mpr H₂ Hc))

@[hott] def iff.symm [symm] (H : a ↔ b) : b ↔ a :=
iff.intro (iff.elim_right H) (iff.elim_left H)

@[hott] def iff.comm : (a ↔ b) ↔ (b ↔ a) :=
iff.intro iff.symm iff.symm

@[hott] def iff.of_eq {a b : Type _} (H : a = b) : a ↔ b :=
eq.rec_on H iff.rfl

@[hott] def not_iff_not_of_iff (H₁ : a ↔ b) : ¬a ↔ ¬b :=
iff.intro
 (assume (Hna : ¬ a) (Hb : b), Hna (iff.elim_right H₁ Hb))
 (assume (Hnb : ¬ b) (Ha : a), Hnb (iff.elim_left H₁ Ha))

@[hott] def of_iff_unit (H : a ↔ unit) : a :=
iff.mp (iff.symm H) star

@[hott] def not_of_iff_empty : (a ↔ empty) → ¬a := iff.mp

@[hott] def iff_unit_intro (H : a) : a ↔ unit :=
iff.intro
  (λ Hl, star)
  (λ Hr, H)

@[hott] def iff_empty_intro (H : ¬a) : a ↔ empty :=
iff.intro H (empty.rec _)

@[hott] def not_non_contradictory_iff_absurd (a : Type _) : ¬¬¬a ↔ ¬a :=
iff.intro
  (λ (Hl : ¬¬¬a) (Ha : a), Hl (non_contradictory_intro Ha))
  absurd

@[hott] def imp_congr [congr] (H1 : a ↔ c) (H2 : b ↔ d) : (a → b) ↔ (c → d) :=
iff.intro
  (λHab Hc, iff.mp H2 (Hab (iff.mpr H1 Hc)))
  (λHcd Ha, iff.mpr H2 (Hcd (iff.mp H1 Ha)))

@[hott] def not_not_intro (Ha : a) : ¬¬a :=
assume Hna : ¬a, Hna Ha

@[hott] def not_of_not_not_not (H : ¬¬¬a) : ¬a :=
λ Ha, absurd (not_not_intro Ha) H

@[hott] def not_unit [simp] : (¬ unit) ↔ empty :=
iff_empty_intro (not_not_intro star)

@[hott] def not_empty_iff [simp] : (¬ empty) ↔ unit :=
iff_unit_intro not_empty

@[hott] def not_congr (H : a ↔ b) : ¬a ↔ ¬b :=
iff.intro (λ H₁ H₂, H₁ (iff.mpr H H₂)) (λ H₁ H₂, H₁ (iff.mp H H₂))

@[hott] def ne_self_iff_empty [simp] {A : Type _} (a : A) : (not (a = a)) ↔ empty :=
iff.intro empty_of_ne empty.elim

@[hott] def eq_self_iff_unit [simp] {A : Type _} (a : A) : (a = a) ↔ unit :=
iff_unit_intro rfl

@[hott] def iff_not_self [simp] (a : Type _) : (a ↔ ¬a) ↔ empty :=
iff_empty_intro (λ H,
   have H' : ¬a, from (λ Ha, (iff.mp H Ha) Ha),
   H' (iff.mpr H H'))

@[hott] def not_iff_self [simp] (a : Type _) : (¬a ↔ a) ↔ empty :=
iff_empty_intro (λ H,
   have H' : ¬a, from (λ Ha, (iff.mpr H Ha) Ha),
   H' (iff.mp H H'))

@[hott] def unit_iff_empty [simp] : (unit ↔ empty) ↔ empty :=
iff_empty_intro (λ H, iff.mp H star)

@[hott] def empty_iff_unit [simp] : (empty ↔ unit) ↔ empty :=
iff_empty_intro (λ H, iff.mpr H star)

@[hott] def empty_of_unit_iff_empty : (unit ↔ empty) → empty :=
assume H, iff.mp H star

/- prod simp rules -/
@[hott] def prod.imp (H₂ : a → c) (H₃ : b → d) : a × b → c × d :=
prod.rec (λHa Hb, prod.mk (H₂ Ha) (H₃ Hb))

@[hott] def prod_congr [congr] (H1 : a ↔ c) (H2 : b ↔ d) : (a × b) ↔ (c × d) :=
iff.intro (prod.imp (iff.mp H1) (iff.mp H2)) (prod.imp (iff.mpr H1) (iff.mpr H2))

@[hott] def prod.comm [simp] : a × b ↔ b × a :=
iff.intro prod.swap prod.swap

@[hott] def prod.assoc [simp] : (a × b) × c ↔ a × (b × c) :=
iff.intro
  (prod.rec (λ H' Hc, prod.rec (λ Ha Hb, prod.mk Ha (prod.mk Hb Hc)) H'))
  (prod.rec (λ Ha, prod.rec (λ Hb Hc, prod.mk (prod.mk Ha Hb) Hc)))

@[hott] def prod.pr1_comm [simp] : a × (b × c) ↔ b × (a × c) :=
iff.trans (iff.symm !prod.assoc) (iff.trans (prod_congr !prod.comm !iff.refl) !prod.assoc)

@[hott] def prod_iff_left {a b : Type _} (Hb : b) : (a × b) ↔ a :=
iff.intro prod.pr1 (λHa, prod.mk Ha Hb)

@[hott] def prod_iff_right {a b : Type _} (Ha : a) : (a × b) ↔ b :=
iff.intro prod.pr2 (prod.mk Ha)

@[hott] def prod_unit [simp] (a : Type _) : a × unit ↔ a :=
prod_iff_left star

@[hott] def unit_prod [simp] (a : Type _) : unit × a ↔ a :=
prod_iff_right star

@[hott] def prod_empty [simp] (a : Type _) : a × empty ↔ empty :=
iff_empty_intro prod.pr2

@[hott] def empty_prod [simp] (a : Type _) : empty × a ↔ empty :=
iff_empty_intro prod.pr1

@[hott] def not_prod_self [simp] (a : Type _) : (¬a × a) ↔ empty :=
iff_empty_intro (λ H, prod.elim H (λ H₁ H₂, absurd H₂ H₁))

@[hott] def prod_not_self [simp] (a : Type _) : (a × ¬a) ↔ empty :=
iff_empty_intro (λ H, prod.elim H (λ H₁ H₂, absurd H₁ H₂))

@[hott] def prod_self [simp] (a : Type _) : a × a ↔ a :=
iff.intro prod.pr1 (assume H, prod.mk H H)

/- sum simp rules -/

@[hott] def sum.imp (H₂ : a → c) (H₃ : b → d) : a ⊎ b → c ⊎ d :=
sum.rec (λ H, sum.inl (H₂ H)) (λ H, sum.inr (H₃ H))

@[hott] def sum.imp_left (H : a → b) : a ⊎ c → b ⊎ c :=
sum.imp H id

@[hott] def sum.imp_right (H : a → b) : c ⊎ a → c ⊎ b :=
sum.imp id H

@[hott] def sum_congr [congr] (H1 : a ↔ c) (H2 : b ↔ d) : (a ⊎ b) ↔ (c ⊎ d) :=
iff.intro (sum.imp (iff.mp H1) (iff.mp H2)) (sum.imp (iff.mpr H1) (iff.mpr H2))

@[hott] def sum.comm [simp] : a ⊎ b ↔ b ⊎ a := iff.intro sum.swap sum.swap

@[hott] def sum.assoc [simp] : (a ⊎ b) ⊎ c ↔ a ⊎ (b ⊎ c) :=
iff.intro
  (sum.rec (sum.imp_right sum.inl) (λ H, sum.inr (sum.inr H)))
  (sum.rec (λ H, sum.inl (sum.inl H)) (sum.imp_left sum.inr))

@[hott] def sum.left_comm [simp] : a ⊎ (b ⊎ c) ↔ b ⊎ (a ⊎ c) :=
iff.trans (iff.symm !sum.assoc) (iff.trans (sum_congr !sum.comm !iff.refl) !sum.assoc)

@[hott] def sum_unit [simp] (a : Type _) : a ⊎ unit ↔ unit :=
iff_unit_intro (sum.inr star)

@[hott] def unit_sum [simp] (a : Type _) : unit ⊎ a ↔ unit :=
iff_unit_intro (sum.inl star)

@[hott] def sum_empty [simp] (a : Type _) : a ⊎ empty ↔ a :=
iff.intro (sum.rec id empty.elim) sum.inl

@[hott] def empty_sum [simp] (a : Type _) : empty ⊎ a ↔ a :=
iff.trans sum.comm !sum_empty

@[hott] def sum_self [simp] (a : Type _) : a ⊎ a ↔ a :=
iff.intro (sum.rec id id) sum.inl

/- sum resolution rulse -/

@[hott] def sum.resolve_left {a b : Type _} (H : a ⊎ b) (na : ¬ a) : b :=
  sum.elim H (λ Ha, absurd Ha na) id

@[hott] def sum.neg_resolve_left {a b : Type _} (H : ¬ a ⊎ b) (Ha : a) : b :=
  sum.elim H (λ na, absurd Ha na) id

@[hott] def sum.resolve_right {a b : Type _} (H : a ⊎ b) (nb : ¬ b) : a :=
  sum.elim H id (λ Hb, absurd Hb nb)

@[hott] def sum.neg_resolve_right {a b : Type _} (H : a ⊎ ¬ b) (Hb : b) : a :=
  sum.elim H id (λ nb, absurd Hb nb)

/- iff simp rules -/

@[hott] def iff_unit [simp] (a : Type _) : (a ↔ unit) ↔ a :=
iff.intro (assume H, iff.mpr H star) iff_unit_intro

@[hott] def unit_iff [simp] (a : Type _) : (unit ↔ a) ↔ a :=
iff.trans iff.comm !iff_unit

@[hott] def iff_empty [simp] (a : Type _) : (a ↔ empty) ↔ ¬ a :=
iff.intro prod.pr1 iff_empty_intro

@[hott] def empty_iff [simp] (a : Type _) : (empty ↔ a) ↔ ¬ a :=
iff.trans iff.comm !iff_empty

@[hott] def iff_self [simp] (a : Type _) : (a ↔ a) ↔ unit :=
iff_unit_intro iff.rfl

@[hott] def iff_congr [congr] (H1 : a ↔ c) (H2 : b ↔ d) : (a ↔ b) ↔ (c ↔ d) :=
prod_congr (imp_congr H1 H2) (imp_congr H2 H1)

/- decidable -/

inductive decidable [class] (p : Type _) : Type _ :=
| inl :  p → decidable p
| inr : ¬p → decidable p

@[hott] def decidable_unit [instance] : decidable unit :=
decidable.inl star

@[hott] def decidable_empty [instance] : decidable empty :=
decidable.inr not_empty

-- We use "dependent" if-then-else to be able to communicate the if-then-else condition
-- to the branches
@[hott] def dite (c : Type _) [H : decidable c] {A : Type _} : (c → A) → (¬ c → A) → A :=
decidable.rec_on H

/- if-then-else -/

@[hott] def ite (c : Type _) [H : decidable c] {A : Type _} (t e : A) : A :=
decidable.rec_on H (λ Hc, t) (λ Hnc, e)

namespace decidable
  variables {p q : Type _}

  @[hott] def by_cases {q : Type _} [C : decidable p] : (p → q) → (¬p → q) → q := !dite

  @[hott] theorem em (p : Type _) [H : decidable p] : p ⊎ ¬p := by_cases sum.inl sum.inr

  @[hott] theorem by_contradiction [Hp : decidable p] (H : ¬p → empty) : p :=
  if H1 : p then H1 else empty.rec _ (H H1)
end decidable

section
  variables {p q : Type _}
  open decidable
  @[hott] def  decidable_of_decidable_of_iff (Hp : decidable p) (H : p ↔ q) : decidable q :=
  if Hp : p then inl (iff.mp H Hp)
  else inr (iff.mp (not_iff_not_of_iff H) Hp)

  @[hott] def decidable_of_decidable_of_eq {p q : Type _} (Hp : decidable p) (H : p = q)
    : decidable q :=
  decidable_of_decidable_of_iff Hp (iff.of_eq H)

  protected @[hott] def sum.by_cases [Hp : decidable p] [Hq : decidable q] {A : Type _}
                                   (h : p ⊎ q) (h₁ : p → A) (h₂ : q → A) : A :=
  if hp : p then h₁ hp else
    if hq : q then h₂ hq else
      empty.rec _ (sum.elim h hp hq)
end

section
  variables {p q : Type _}
  open decidable (rec_on inl inr)

  @[hott] def decidable_prod [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p × q) :=
  if hp : p then
    if hq : q then inl (prod.mk hp hq)
    else inr (assume H : p × q, hq (prod.pr2 H))
  else inr (assume H : p × q, hp (prod.pr1 H))

  @[hott] def decidable_sum [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ⊎ q) :=
  if hp : p then inl (sum.inl hp) else
    if hq : q then inl (sum.inr hq) else
      inr (sum.rec hp hq)

  @[hott] def decidable_not [instance] [Hp : decidable p] : decidable (¬p) :=
  if hp : p then inr (absurd hp) else inl hp

  @[hott] def decidable_implies [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p → q) :=
  if hp : p then
    if hq : q then inl (assume H, hq)
    else inr (assume H : p → q, absurd (H hp) hq)
  else inl (assume Hp, absurd Hp hp)

  @[hott] def decidable_iff [instance] [Hp : decidable p] [Hq : decidable q] : decidable (p ↔ q) :=
  decidable_prod

end

@[hott] def decidable_pred [reducible] {A : Type _} (R : A   →   Type _) := Π (a   : A), decidable (R a)
@[hott] def decidable_rel  [reducible] {A : Type _} (R : A → A → Type _) := Π (a b : A), decidable (R a b)
@[hott] def decidable_eq   [reducible] (A : Type _) := decidable_rel (@eq A)
@[hott] def decidable_ne [instance] {A : Type _} [H : decidable_eq A] (a b : A) : decidable (a ≠ b) :=
decidable_implies

namespace bool
  @[hott] theorem ff_ne_tt : ff = tt → empty
  | [none]
end bool

open bool
@[hott] def is_dec_eq {A : Type _} (p : A → A → bool) : Type _   := Π ⦃x y : A⦄, p x y = tt → x = y
@[hott] def is_dec_refl {A : Type _} (p : A → A → bool) : Type _ := Πx, p x x = tt

open decidable
protected @[hott] def bool.has_decidable_eq [instance] : Πa b : bool, decidable (a = b)
| ff ff := inl rfl
| ff tt := inr ff_ne_tt
| tt ff := inr (ne.symm ff_ne_tt)
| tt tt := inl rfl

@[hott] def decidable_eq_of_bool_pred {A : Type _} {p : A → A → bool} (H₁ : is_dec_eq p) (H₂ : is_dec_refl p) : decidable_eq A :=
take x y : A, if Hp : p x y = tt then inl (H₁ Hp)
 else inr (assume Hxy : x = y, (eq.subst Hxy Hp) (H₂ y))

/- inhabited -/

inductive inhabited [class] (A : Type _) : Type _ :=
mk : A → inhabited A

protected @[hott] def inhabited.value {A : Type _} : inhabited A → A :=
inhabited.rec (λa, a)

protected @[hott] def inhabited.destruct {A : Type _} {B : Type _} (H1 : inhabited A) (H2 : A → B) : B :=
inhabited.rec H2 H1

@[hott] def default (A : Type _) [H : inhabited A] : A :=
inhabited.value H

@[hott] def arbitrary [irreducible] (A : Type _) [H : inhabited A] : A :=
inhabited.value H

@[hott] def Type.is_inhabited [instance] : inhabited Type _ :=
inhabited.mk (lift unit)

@[hott] def inhabited_fun [instance] (A : Type _) {B : Type _} [H : inhabited B] : inhabited (A → B) :=
inhabited.rec_on H (λb, inhabited.mk (λa, b))

@[hott] def inhabited_Pi [instance] (A : Type _) {B : A → Type _} [H : Πx, inhabited (B x)] :
  inhabited (Πx, B x) :=
inhabited.mk (λa, !default)

protected @[hott] def bool.is_inhabited [instance] : inhabited bool :=
inhabited.mk ff

protected @[hott] def pos_num.is_inhabited [instance] : inhabited pos_num :=
inhabited.mk pos_num.one

protected @[hott] def num.is_inhabited [instance] : inhabited num :=
inhabited.mk num.zero

inductive nonempty [class] (A : Type _) : Type _ :=
intro : A → nonempty A

protected @[hott] def nonempty.elim {A : Type _} {B : Type _} (H1 : nonempty A) (H2 : A → B) : B :=
nonempty.rec H2 H1

@[hott] theorem nonempty_of_inhabited [instance] {A : Type _} [H : inhabited A] : nonempty A :=
nonempty.intro !default

@[hott] theorem nonempty_of_exists {A : Type _} {P : A → Type _} : (sigma P) → nonempty A :=
sigma.rec (λw H, nonempty.intro w)

/- subsingleton -/

inductive subsingleton [class] (A : Type _) : Type _ :=
intro : (Π a b : A, a = b) → subsingleton A

protected @[hott] def subsingleton.elim {A : Type _} [H : subsingleton A] : Π(a b : A), a = b :=
subsingleton.rec (λp, p) H

protected @[hott] theorem rec_subsingleton {p : Type _} [H : decidable p]
    {H1 : p → Type _} {H2 : ¬p → Type _}
    [H3 : Π(h : p), subsingleton (H1 h)] [H4 : Π(h : ¬p), subsingleton (H2 h)]
  : subsingleton (decidable.rec_on H H1 H2) :=
decidable.rec_on H (λh, H3 h) (λh, H4 h) --this can be proven using dependent version of "by_cases"

@[hott] theorem if_pos {c : Type _} [H : decidable c] (Hc : c) {A : Type _} {t e : A} : (ite c t e) = t :=
decidable.rec
  (λ Hc : c,    eq.refl (@ite c (decidable.inl Hc) A t e))
  (λ Hnc : ¬c,  absurd Hc Hnc)
  H

@[hott] theorem if_neg {c : Type _} [H : decidable c] (Hnc : ¬c) {A : Type _} {t e : A} : (ite c t e) = e :=
decidable.rec
  (λ Hc : c,    absurd Hc Hnc)
  (λ Hnc : ¬c,  eq.refl (@ite c (decidable.inr Hnc) A t e))
  H

@[hott] theorem if_t_t [simp] (c : Type _) [H : decidable c] {A : Type _} (t : A) : (ite c t t) = t :=
decidable.rec
  (λ Hc  : c,  eq.refl (@ite c (decidable.inl Hc)  A t t))
  (λ Hnc : ¬c, eq.refl (@ite c (decidable.inr Hnc) A t t))
  H

@[hott] theorem implies_of_if_pos {c t e : Type _} [H : decidable c] (h : ite c t e) : c → t :=
assume Hc, eq.rec_on (if_pos Hc) h

@[hott] theorem implies_of_if_neg {c t e : Type _} [H : decidable c] (h : ite c t e) : ¬c → e :=
assume Hnc, eq.rec_on (if_neg Hnc) h

@[hott] theorem if_ctx_congr {A : Type _} {b c : Type _} [dec_b : decidable b] [dec_c : decidable c]
                     {x y u v : A}
                     (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = ite c u v :=
decidable.rec_on dec_b
  (λ hp : b, calc
    ite b x y = x           : if_pos hp
         ...  = u           : h_t (iff.mp h_c hp)
         ...  = ite c u v : if_pos (iff.mp h_c hp))
  (λ hn : ¬b, calc
    ite b x y = y         : if_neg hn
         ...  = v         : h_e (iff.mp (not_iff_not_of_iff h_c) hn)
         ...  = ite c u v : if_neg (iff.mp (not_iff_not_of_iff h_c) hn))

@[hott] theorem if_congr [congr] {A : Type _} {b c : Type _} [dec_b : decidable b] [dec_c : decidable c]
                 {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = ite c u v :=
@if_ctx_congr A b c dec_b dec_c x y u v h_c (λ h, h_t) (λ h, h_e)

@[hott] theorem if_ctx_simp_congr {A : Type _} {b c : Type _} [dec_b : decidable b] {x y u v : A}
                        (h_c : b ↔ c) (h_t : c → x = u) (h_e : ¬c → y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@if_ctx_congr A b c dec_b (decidable_of_decidable_of_iff dec_b h_c) x y u v h_c h_t h_e

@[hott] theorem if_simp_congr [congr] {A : Type _} {b c : Type _} [dec_b : decidable b] {x y u v : A}
                 (h_c : b ↔ c) (h_t : x = u) (h_e : y = v) :
        ite b x y = (@ite c (decidable_of_decidable_of_iff dec_b h_c) A u v) :=
@if_ctx_simp_congr A b c dec_b x y u v h_c (λ h, h_t) (λ h, h_e)

@[hott] def if_unit [simp] {A : Type _} (t e : A) : (if unit then t else e) = t :=
if_pos star

@[hott] def if_empty [simp] {A : Type _} (t e : A) : (if empty then t else e) = e :=
if_neg not_empty

@[hott] theorem if_ctx_congr_prop {b c x y u v : Type _} [dec_b : decidable b] [dec_c : decidable c]
                      (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ ite c u v :=
decidable.rec_on dec_b
  (λ hp : b, calc
    ite b x y ↔ x         : iff.of_eq (if_pos hp)
         ...  ↔ u         : h_t (iff.mp h_c hp)
         ...  ↔ ite c u v : iff.of_eq (if_pos (iff.mp h_c hp)))
  (λ hn : ¬b, calc
    ite b x y ↔ y         : iff.of_eq (if_neg hn)
         ...  ↔ v         : h_e (iff.mp (not_iff_not_of_iff h_c) hn)
         ...  ↔ ite c u v : iff.of_eq (if_neg (iff.mp (not_iff_not_of_iff h_c) hn)))

@[hott] theorem if_congr_prop [congr] {b c x y u v : Type _} [dec_b : decidable b] [dec_c : decidable c]
                      (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ ite c u v :=
if_ctx_congr_prop h_c (λ h, h_t) (λ h, h_e)

@[hott] theorem if_ctx_simp_congr_prop {b c x y u v : Type _} [dec_b : decidable b]
                               (h_c : b ↔ c) (h_t : c → (x ↔ u)) (h_e : ¬c → (y ↔ v)) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) Type _ u v) :=
@if_ctx_congr_prop b c x y u v dec_b (decidable_of_decidable_of_iff dec_b h_c) h_c h_t h_e

@[hott] theorem if_simp_congr_prop [congr] {b c x y u v : Type _} [dec_b : decidable b]
                           (h_c : b ↔ c) (h_t : x ↔ u) (h_e : y ↔ v) :
        ite b x y ↔ (@ite c (decidable_of_decidable_of_iff dec_b h_c) Type _ u v) :=
@if_ctx_simp_congr_prop b c x y u v dec_b h_c (λ h, h_t) (λ h, h_e)

-- Remark: dite and ite are "definitionally equal" when we ignore the proofs.
@[hott] theorem dite_ite_eq (c : Type _) [H : decidable c] {A : Type _} (t : A) (e : A) : dite c (λh, t) (λh, e) = ite c t e :=
rfl

@[hott] def is_unit (c : Type _) [H : decidable c] : Type :=
if c then unit else empty

@[hott] def is_empty (c : Type _) [H : decidable c] : Type :=
if c then empty else unit

@[hott] def of_is_unit {c : Type _} [H₁ : decidable c] (H₂ : is_unit c) : c :=
decidable.rec_on H₁ (λ Hc, Hc) (λ Hnc, empty.rec _ (if_neg Hnc ▸ H₂))

notation `dec_star` := of_is_unit star

@[hott] theorem not_of_not_is_unit {c : Type _} [H₁ : decidable c] (H₂ : ¬ is_unit c) : ¬ c :=
if Hc : c then absurd star (if_pos Hc ▸ H₂) else Hc

@[hott] theorem not_of_is_empty {c : Type _} [H₁ : decidable c] (H₂ : is_empty c) : ¬ c :=
if Hc : c then empty.rec _ (if_pos Hc ▸ H₂) else Hc

@[hott] theorem of_not_is_empty {c : Type _} [H₁ : decidable c] (H₂ : ¬ is_empty c) : c :=
if Hc : c then Hc else absurd star (if_neg Hc ▸ H₂)

-- The following symbols should not be considered in the pattern inference procedure used by
-- heuristic instantiation.
attribute prod sum not iff ite dite eq ne [no_pattern]

-- namespace used to collect congruence rules for "contextual simplification"
namespace contextual
  attribute if_ctx_simp_congr      [congr]
  attribute if_ctx_simp_congr_prop [congr]
end contextual
