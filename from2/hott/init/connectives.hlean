/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura, Haitao Zhang

The propositional connectives.
-/
prelude

import .types
open unit

variables {a b c d : Type _}

/- implies -/

@[hott] def imp (a b : Type _) : Type _ := a → b

@[hott] def imp.id (H : a) : a := H

@[hott] def imp.intro (H : a) (H₂ : b) : a := H

@[hott] def imp.mp (H : a) (H₂ : a → b) : b :=
H₂ H

@[hott] def imp.syl (H : a → b) (H₂ : c → a) (Hc : c) : b :=
H (H₂ Hc)

@[hott] def imp.left (H : a → b) (H₂ : b → c) (Ha : a) : c :=
H₂ (H Ha)

@[hott] def imp_unit (a : Type _) : (a → unit) ↔ unit :=
iff_unit_intro (imp.intro star)

@[hott] def unit_imp (a : Type _) : (unit → a) ↔ a :=
iff.intro (assume H, H star) imp.intro

@[hott] def imp_empty (a : Type _) : (a → empty) ↔ ¬ a := iff.rfl

@[hott] def empty_imp (a : Type _) : (empty → a) ↔ unit :=
iff_unit_intro empty.elim

/- not -/

@[hott] def not.elim {A : Type _} (H1 : ¬a) (H2 : a) : A := absurd H2 H1

@[hott] def not.mto {a b : Type _} : (a → b) → ¬b → ¬a := imp.left

@[hott] def not_imp_not_of_imp {a b : Type _} : (a → b) → ¬b → ¬a := not.mto

@[hott] def not_not_of_not_implies : ¬(a → b) → ¬¬a :=
not.mto not.elim

@[hott] def not_of_not_implies : ¬(a → b) → ¬b :=
not.mto imp.intro

@[hott] def not_not_em : ¬¬(a ⊎ ¬a) :=
assume not_em : ¬(a ⊎ ¬a),
not_em (sum.inr (not.mto sum.inl not_em))

@[hott] def not_iff_not (H : a ↔ b) : ¬a ↔ ¬b :=
iff.intro (not.mto (iff.mpr H)) (not.mto (iff.mp H))

/- prod -/

@[hott] def not_prod_of_not_left (b : Type _) : ¬a → ¬(a × b) :=
not.mto prod.pr1

@[hott] def not_prod_of_not_right (a : Type _) {b : Type _} : ¬b →  ¬(a × b) :=
not.mto prod.pr2

@[hott] def prod.imp_left (H : a → b) : a × c → b × c :=
prod.imp H imp.id

@[hott] def prod.imp_right (H : a → b) : c × a → c × b :=
prod.imp imp.id H

@[hott] def prod_of_prod_of_imp_of_imp (H₁ : a × b) (H₂ : a → c) (H₃ : b → d) : c × d :=
prod.imp H₂ H₃ H₁

@[hott] def prod_of_prod_of_imp_left (H₁ : a × c) (H : a → b) : b × c :=
prod.imp_left H H₁

@[hott] def prod_of_prod_of_imp_right (H₁ : c × a) (H : a → b) : c × b :=
prod.imp_right H H₁

@[hott] def prod_imp_iff (a b c : Type _) : (a × b → c) ↔ (a → b → c) :=
iff.intro (λH a b, H (pair a b)) prod.rec

/- sum -/

@[hott] def not_sum : ¬a → ¬b → ¬(a ⊎ b) := sum.rec

@[hott] def sum_of_sum_of_imp_of_imp (H₁ : a ⊎ b) (H₂ : a → c) (H₃ : b → d) : c ⊎ d :=
sum.imp H₂ H₃ H₁

@[hott] def sum_of_sum_of_imp_left (H₁ : a ⊎ c) (H : a → b) : b ⊎ c :=
sum.imp_left H H₁

@[hott] def sum_of_sum_of_imp_right (H₁ : c ⊎ a) (H : a → b) : c ⊎ b :=
sum.imp_right H H₁

@[hott] def sum.elim3 (H : a ⊎ b ⊎ c) (Ha : a → d) (Hb : b → d) (Hc : c → d) : d :=
sum.elim H Ha (assume H₂, sum.elim H₂ Hb Hc)

@[hott] def sum_resolve_right (H₁ : a ⊎ b) (H₂ : ¬a) : b :=
sum.elim H₁ (not.elim H₂) imp.id

@[hott] def sum_resolve_left (H₁ : a ⊎ b) : ¬b → a :=
sum_resolve_right (sum.swap H₁)

@[hott] def sum.imp_distrib : ((a ⊎ b) → c) ↔ ((a → c) × (b → c)) :=
iff.intro
  (λH, pair (imp.syl H sum.inl) (imp.syl H sum.inr))
  (prod.rec sum.rec)

@[hott] def sum_iff_right_of_imp {a b : Type _} (Ha : a → b) : (a ⊎ b) ↔ b :=
iff.intro (sum.rec Ha imp.id) sum.inr

@[hott] def sum_iff_left_of_imp {a b : Type _} (Hb : b → a) : (a ⊎ b) ↔ a :=
iff.intro (sum.rec imp.id Hb) sum.inl

@[hott] def sum_iff_sum (H1 : a ↔ c) (H2 : b ↔ d) : (a ⊎ b) ↔ (c ⊎ d) :=
iff.intro (sum.imp (iff.mp H1) (iff.mp H2)) (sum.imp (iff.mpr H1) (iff.mpr H2))

/- distributivity -/

@[hott] def prod.pr1_distrib (a b c : Type _) : a × (b ⊎ c) ↔ (a × b) ⊎ (a × c) :=
iff.intro
  (prod.rec (λH, sum.imp (pair H) (pair H)))
  (sum.rec (prod.imp_right sum.inl) (prod.imp_right sum.inr))

@[hott] def prod.pr2_distrib (a b c : Type _) : (a ⊎ b) × c ↔ (a × c) ⊎ (b × c) :=
iff.trans (iff.trans !prod.comm !prod.pr1_distrib) (sum_iff_sum !prod.comm !prod.comm)

@[hott] def sum.left_distrib (a b c : Type _) : a ⊎ (b × c) ↔ (a ⊎ b) × (a ⊎ c) :=
iff.intro
  (sum.rec (λH, pair (sum.inl H) (sum.inl H)) (prod.imp sum.inr sum.inr))
  (prod.rec (sum.rec (imp.syl imp.intro sum.inl) (imp.syl sum.imp_right pair)))

@[hott] def sum.right_distrib (a b c : Type _) : (a × b) ⊎ c ↔ (a ⊎ c) × (b ⊎ c) :=
iff.trans (iff.trans !sum.comm !sum.left_distrib) (prod_congr !sum.comm !sum.comm)

/- iff -/

@[hott] def iff.def : (a ↔ b) = ((a → b) × (b → a)) := rfl

@[hott] def pi_imp_pi {A : Type _} {P Q : A → Type _} (H : Πa, (P a → Q a)) (p : Πa, P a) (a : A) : Q a :=
(H a) (p a)

@[hott] def pi_iff_pi {A : Type _} {P Q : A → Type _} (H : Πa, (P a ↔ Q a)) : (Πa, P a) ↔ (Πa, Q a) :=
iff.intro (λp a, iff.elim_left (H a) (p a)) (λq a, iff.elim_right (H a) (q a))

@[hott] def imp_iff {P : Type _} (Q : Type _) (p : P) : (P → Q) ↔ Q :=
iff.intro (λf, f p) imp.intro
