/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Leonardo de Moura, Jeremy Avigad, Floris van Doorn
-/
prelude
import init.datatypes

notation `assume` binders `,` r:(scoped f, f) := r
notation `take`   binders `,` r:(scoped f, f) := r

structure has_zero    [class] (A : Type _) := (zero : A)
structure has_one     [class] (A : Type _) := (one : A)
structure has_add     [class] (A : Type _) := (add : A → A → A)
structure has_mul     [class] (A : Type _) := (mul : A → A → A)
structure has_inv     [class] (A : Type _) := (inv : A → A)
structure has_neg     [class] (A : Type _) := (neg : A → A)
structure has_sub     [class] (A : Type _) := (sub : A → A → A)
structure has_div     [class] (A : Type _) := (div : A → A → A)
structure has_mod     [class] (A : Type _) := (mod : A → A → A)
structure has_dvd.{l} [class] (A : Type l) : Type l+1 := (dvd : A → A → Type l)
structure has_le.{l}  [class] (A : Type l) : Type l+1 := (le : A → A → Type l)
structure has_lt.{l}  [class] (A : Type l) : Type l+1 := (lt : A → A → Type l)

@[hott] def zero [reducible] {A : Type _} [s : has_zero A] : A            := has_zero.zero A
@[hott] def one  [reducible] {A : Type _} [s : has_one A]  : A            := has_one.one A
@[hott] def add  [reducible] {A : Type _} [s : has_add A]  : A → A → A    := has_add.add
@[hott] def mul              {A : Type _} [s : has_mul A]  : A → A → A    := has_mul.mul
@[hott] def sub              {A : Type _} [s : has_sub A]  : A → A → A    := has_sub.sub
@[hott] def div              {A : Type _} [s : has_div A]  : A → A → A    := has_div.div
@[hott] def dvd              {A : Type _} [s : has_dvd A]  : A → A → Type _ := has_dvd.dvd
@[hott] def mod              {A : Type _} [s : has_mod A]  : A → A → A    := has_mod.mod
@[hott] def neg              {A : Type _} [s : has_neg A]  : A → A        := has_neg.neg
@[hott] def inv              {A : Type _} [s : has_inv A]  : A → A        := has_inv.inv
@[hott] def le               {A : Type _} [s : has_le A]   : A → A → Type _ := has_le.le
@[hott] def lt               {A : Type _} [s : has_lt A]   : A → A → Type _ := has_lt.lt

@[hott] def ge [reducible] {A : Type _} [s : has_le A] (a b : A) : Type _ := le b a
@[hott] def gt [reducible] {A : Type _} [s : has_lt A] (a b : A) : Type _ := lt b a

/-
  bit0 and bit1 are two auxiliary @[hott] def used when parsing numerals such as 13, 0, 26.
  The parser will generate the terms (bit1 (bit0 (bit1 one))), zero, and
  (bit0 (bit1 (bit0 (bit1 one)))). This works in any type with an addition, a zero and a one.
  More specifically, there must be type class instances for the classes for has_add, has_zero and
  has_one
-/
@[hott] def bit0 [reducible] {A : Type _} [s  : has_add A] (a  : A)                 : A := add a a
@[hott] def bit1 [reducible] {A : Type _} [s₁ : has_one A] [s₂ : has_add A] (a : A) : A :=
add (bit0 a) one

@[hott] def num_has_zero [instance]  : has_zero num :=
has_zero.mk num.zero

@[hott] def num_has_one [instance] : has_one num :=
has_one.mk (num.pos pos_num.one)

@[hott] def pos_num_has_one [instance] : has_one pos_num :=
has_one.mk (pos_num.one)

namespace pos_num
  open bool
  @[hott] def is_one (a : pos_num) : bool :=
  pos_num.rec_on a tt (λn r, ff) (λn r, ff)

  @[hott] def pred (a : pos_num) : pos_num :=
  pos_num.rec_on a one (λn r, bit0 n) (λn r, bool.rec_on (is_one n) (bit1 r) one)

  @[hott] def size (a : pos_num) : pos_num :=
  pos_num.rec_on a one (λn r, succ r) (λn r, succ r)

  @[hott] def add (a b : pos_num) : pos_num :=
  pos_num.rec_on a
    succ
    (λn f b, pos_num.rec_on b
      (succ (bit1 n))
      (λm r, succ (bit1 (f m)))
      (λm r, bit1 (f m)))
    (λn f b, pos_num.rec_on b
      (bit1 n)
      (λm r, bit1 (f m))
      (λm r, bit0 (f m)))
    b
end pos_num

@[hott] def pos_num_has_add [instance] : has_add pos_num :=
has_add.mk pos_num.add

namespace num
  open pos_num

  @[hott] def add (a b : num) : num :=
  num.rec_on a b (λpa, num.rec_on b (pos pa) (λpb, pos (pos_num.add pa pb)))
end num

@[hott] def num_has_add [instance] : has_add num :=
has_add.mk num.add

@[hott] def std.priority.default : num := 1000
@[hott] def std.priority.max     : num := 4294967295

namespace nat
  protected @[hott] def prio := num.add std.priority.default 100

  protected @[hott] def add (a b : nat) : nat :=
  nat.rec a (λ b₁ r, succ r) b

  @[hott] def of_num (n : num) : nat :=
  num.rec zero
    (λ n, pos_num.rec (succ zero) (λ n r, nat.add (nat.add r r) (succ zero)) (λ n r, nat.add r r) n) n
end nat

attribute pos_num_has_add pos_num_has_one num_has_zero num_has_one num_has_add
          [instance] [priority nat.prio]

@[hott] def nat_has_zero [instance] [priority nat.prio] : has_zero nat :=
has_zero.mk nat.zero

@[hott] def nat_has_one [instance] [priority nat.prio] : has_one nat :=
has_one.mk (nat.succ (nat.zero))

@[hott] def nat_has_add [instance] [priority nat.prio] : has_add nat :=
has_add.mk nat.add

/-
  Global declarations of right binding strength

  If a module reassigns these, it will be incompatible with other modules that adhere to these
  conventions.

  When hovering over a symbol, use "C-c C-k" to see how to input it.
-/
@[hott] def std.prec.max   : num := 1024 -- the strength of application, identifiers, (, [, etc.
@[hott] def std.prec.arrow : num := 25

/-
The next @[hott] def is "max + 10". It can be used e.g. for postfix operations that should
be stronger than application.
-/

@[hott] def std.prec.max_plus :=
num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ (num.succ
  (num.succ std.prec.max)))))))))

/- Logical operations and relations -/

reserve prefix `¬`:40
reserve prefix `~`:40
reserve infixr ` ∧ `:35
reserve infixr ` /\ `:35
reserve infixr ` \/ `:30
reserve infixr ` ∨ `:30
reserve infix ` <-> `:20
reserve infix ` ↔ `:20
reserve infix ` = `:50
reserve infix ` ≠ `:50
reserve infix ` ≈ `:50
reserve infix ` ~ `:50
reserve infix ` ≡ `:50

reserve infixr ` ∘ `:60                 -- input with \comp
reserve postfix `⁻¹`:std.prec.max_plus  -- input with \sy or \-1 or \inv

reserve infixl ` ⬝ `:75
reserve infixr ` ▸ `:75
reserve infixr ` ▹ `:75

/- types and type constructors -/

reserve infixr ` ⊎ `:30
reserve infixr ` × `:35

/- arithmetic operations -/

reserve infixl ` + `:65
reserve infixl ` - `:65
reserve infixl ` * `:70
reserve infixl ` / `:70
reserve infixl ` % `:70
reserve prefix `-`:100
reserve infix ` ^ `:80

reserve infix ` <= `:50
reserve infix ` ≤ `:50
reserve infix ` < `:50
reserve infix ` >= `:50
reserve infix ` ≥ `:50
reserve infix ` > `:50

/- boolean operations -/

reserve infixl ` && `:70
reserve infixl ` || `:65

/- set operations -/

reserve infix ` ∈ `:50
reserve infix ` ∉ `:50
reserve infixl ` ∩ `:70
reserve infixl ` ∪ `:65
reserve infix ` ⊆ `:50
reserve infix ` ⊇ `:50

/- other symbols -/

reserve infix ` ∣ `:50
reserve infixl ` ++ `:65
reserve infixr ` :: `:67

/-
  in the HoTT library we might not always want to overload the following notation,
  so we put it in namespace algebra
-/

infix +    := add
infix *    := mul
infix -    := sub
infix /    := div
infix ∣    := dvd
infix %    := mod
prefix -   := neg
namespace algebra
postfix ⁻¹ := inv
end algebra
infix ≤    := le
infix ≥    := ge
infix <    := lt
infix >    := gt

notation [parsing_only] x ` +[`:65 A:0 `] `:0 y:65 := @add A _ x y
notation [parsing_only] x ` -[`:65 A:0 `] `:0 y:65 := @sub A _ x y
notation [parsing_only] x ` *[`:70 A:0 `] `:0 y:70 := @mul A _ x y
notation [parsing_only] x ` /[`:70 A:0 `] `:0 y:70 := @div A _ x y
notation [parsing_only] x ` ∣[`:70 A:0 `] `:0 y:70 := @dvd A _ x y
notation [parsing_only] x ` %[`:70 A:0 `] `:0 y:70 := @mod A _ x y
notation [parsing_only] x ` ≤[`:50 A:0 `] `:0 y:50 := @le A _ x y
notation [parsing_only] x ` ≥[`:50 A:0 `] `:0 y:50 := @ge A _ x y
notation [parsing_only] x ` <[`:50 A:0 `] `:0 y:50 := @lt A _ x y
notation [parsing_only] x ` >[`:50 A:0 `] `:0 y:50 := @gt A _ x y
