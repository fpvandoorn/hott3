/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jakob von Raumer

Basic datatypes
-/

prelude
notation [parsing_only] `Type _'` := Type _+1
notation [parsing_only] `Type _₊` := Type _+1
notation `Type` := Type 0
notation `Type 1` := Type 1
notation `Type₂` := Type 2
notation `Type₃` := Type 3

inductive poly_unit.{l} : Type l :=
star : poly_unit

inductive unit : Type :=
star : unit

inductive empty : Type

inductive eq.{l} {A : Type l} (a : A) : A → Type l :=
refl : eq a a

structure lift.{l₁ l₂} (A : Type l₁) : Type max l₁ l₂ :=
up :: (down : A)

inductive prod (A B : Type _) :=
mk : A → B → prod A B

@[hott] def prod.pr1 [reducible] {A B : Type _} (p : prod A B) : A :=
prod.rec (λ a b, a) p

@[hott] def prod.pr2 [reducible] {A B : Type _} (p : prod A B) : B :=
prod.rec (λ a b, b) p

@[hott] def prod.destruct [reducible] := @prod.cases_on

inductive sum (A B : Type _) : Type _ :=
| inl {} : A → sum A B
| inr {} : B → sum A B

@[hott] def sum.intro_left [reducible] {A : Type _} (B : Type _) (a : A) : sum A B :=
sum.inl a

@[hott] def sum.intro_right [reducible] (A : Type _) {B : Type _} (b : B) : sum A B :=
sum.inr b

inductive sigma {A : Type _} (B : A → Type _) :=
mk : Π (a : A), B a → sigma B

@[hott] def sigma.pr1 [reducible] {A : Type _} {B : A → Type _} (p : sigma B) : A :=
sigma.rec (λ a b, a) p

@[hott] def sigma.pr2 [reducible] {A : Type _} {B : A → Type _} (p : sigma B) : B (sigma.pr1 p) :=
sigma.rec (λ a b, b) p

-- pos_num and num are two auxiliary datatypes used when parsing numerals such as 13, 0, 26
-- in an [priority n] flag.
inductive pos_num : Type _ :=
| one  : pos_num
| bit1 : pos_num → pos_num
| bit0 : pos_num → pos_num

namespace pos_num
  @[hott] def succ (a : pos_num) : pos_num :=
  pos_num.rec_on a (bit0 one) (λn r, bit0 r) (λn r, bit1 n)
end pos_num

inductive num : Type _ :=
| zero  : num
| pos   : pos_num → num

namespace num
  open pos_num
  @[hott] def succ (a : num) : num :=
  num.rec_on a (pos one) (λp, pos (succ p))
end num

inductive bool : Type _ :=
| ff : bool
| tt : bool

inductive char : Type _ :=
mk : bool → bool → bool → bool → bool → bool → bool → bool → char

inductive string : Type _ :=
| empty : string
| str   : char → string → string

inductive option (A : Type _) : Type _ :=
| none {} : option A
| some    : A → option A

-- Remark: we manually generate the nat.rec_on, nat.induction_on, nat.cases_on and nat.no_confusion.
-- We do that because we want 0 instead of nat.zero in these eliminators.
set_option inductive.rec_on   false
set_option inductive.cases_on false
inductive nat :=
| zero : nat
| succ : nat → nat
