/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

-/

import algebra.binary algebra.priority

open eq eq.ops   -- note: ⁻¹ will be overloaded
open binary algebra is_trunc
set_option class.force_new true

variable {A : Type _}

/- inf_semigroup -/

namespace algebra

structure inf_semigroup [class] (A : Type _) extends has_mul A :=
(mul_assoc : Πa b c, mul (mul a b) c = mul a (mul b c))

@[hott] def mul.assoc [s : inf_semigroup A] (a b c : A) : a * b * c = a * (b * c) :=
!inf_semigroup.mul_assoc

structure comm_inf_semigroup [class] (A : Type _) extends inf_semigroup A :=
(mul_comm : Πa b, mul a b = mul b a)

@[hott] def mul.comm [s : comm_inf_semigroup A] (a b : A) : a * b = b * a :=
!comm_inf_semigroup.mul_comm

@[hott] theorem mul.left_comm [s : comm_inf_semigroup A] (a b c : A) : a * (b * c) = b * (a * c) :=
binary.left_comm (@mul.comm A _) (@mul.assoc A _) a b c

@[hott] theorem mul.right_comm [s : comm_inf_semigroup A] (a b c : A) : (a * b) * c = (a * c) * b :=
binary.right_comm (@mul.comm A _) (@mul.assoc A _) a b c

structure left_cancel_inf_semigroup [class] (A : Type _) extends inf_semigroup A :=
(mul_left_cancel : Πa b c, mul a b = mul a c → b = c)

@[hott] theorem mul.left_cancel [s : left_cancel_inf_semigroup A] {a b c : A} :
  a * b = a * c → b = c :=
!left_cancel_inf_semigroup.mul_left_cancel

abbreviation eq_of_mul_eq_mul_left' := @mul.left_cancel

structure right_cancel_inf_semigroup [class] (A : Type _) extends inf_semigroup A :=
(mul_right_cancel : Πa b c, mul a b = mul c b → a = c)

@[hott] def mul.right_cancel [s : right_cancel_inf_semigroup A] {a b c : A} :
  a * b = c * b → a = c :=
!right_cancel_inf_semigroup.mul_right_cancel

abbreviation eq_of_mul_eq_mul_right' := @mul.right_cancel

/- additive inf_semigroup -/

@[hott] def add_inf_semigroup [class] : Type _ → Type _ := inf_semigroup

@[hott] def has_add_of_add_inf_semigroup [reducible] [trans_instance] (A : Type _) [H : add_inf_semigroup A] :
  has_add A :=
has_add.mk (@inf_semigroup.mul A H)

@[hott] def add.assoc [s : add_inf_semigroup A] (a b c : A) : a + b + c = a + (b + c) :=
@mul.assoc A s a b c

@[hott] def add_comm_inf_semigroup [class] : Type _ → Type _ := comm_inf_semigroup

@[hott] def add_inf_semigroup_of_add_comm_inf_semigroup [reducible] [trans_instance] (A : Type _)
  [H : add_comm_inf_semigroup A] : add_inf_semigroup A :=
@comm_inf_semigroup.to_inf_semigroup A H

@[hott] def add.comm [s : add_comm_inf_semigroup A] (a b : A) : a + b = b + a :=
@mul.comm A s a b

@[hott] theorem add.left_comm [s : add_comm_inf_semigroup A] (a b c : A) :
  a + (b + c) = b + (a + c) :=
binary.left_comm (@add.comm A _) (@add.assoc A _) a b c

@[hott] theorem add.right_comm [s : add_comm_inf_semigroup A] (a b c : A) : (a + b) + c = (a + c) + b :=
binary.right_comm (@add.comm A _) (@add.assoc A _) a b c

@[hott] def add_left_cancel_inf_semigroup [class] : Type _ → Type _ := left_cancel_inf_semigroup

@[hott] def add_inf_semigroup_of_add_left_cancel_inf_semigroup [reducible] [trans_instance] (A : Type _)
  [H : add_left_cancel_inf_semigroup A] : add_inf_semigroup A :=
@left_cancel_inf_semigroup.to_inf_semigroup A H

@[hott] def add.left_cancel [s : add_left_cancel_inf_semigroup A] {a b c : A} :
  a + b = a + c → b = c :=
@mul.left_cancel A s a b c

abbreviation eq_of_add_eq_add_left := @add.left_cancel

@[hott] def add_right_cancel_inf_semigroup [class] : Type _ → Type _ := right_cancel_inf_semigroup

@[hott] def add_inf_semigroup_of_add_right_cancel_inf_semigroup [reducible] [trans_instance] (A : Type _)
  [H : add_right_cancel_inf_semigroup A] : add_inf_semigroup A :=
@right_cancel_inf_semigroup.to_inf_semigroup A H

@[hott] def add.right_cancel [s : add_right_cancel_inf_semigroup A] {a b c : A} :
  a + b = c + b → a = c :=
@mul.right_cancel A s a b c

abbreviation eq_of_add_eq_add_right := @add.right_cancel

/- inf_monoid -/

structure inf_monoid [class] (A : Type _) extends inf_semigroup A, has_one A :=
(one_mul : Πa, mul one a = a) (mul_one : Πa, mul a one = a)

@[hott] def one_mul [s : inf_monoid A] (a : A) : 1 * a = a := !inf_monoid.one_mul

@[hott] def mul_one [s : inf_monoid A] (a : A) : a * 1 = a := !inf_monoid.mul_one

structure comm_inf_monoid [class] (A : Type _) extends inf_monoid A, comm_inf_semigroup A

/- additive inf_monoid -/

@[hott] def add_inf_monoid [class] : Type _ → Type _ := inf_monoid

@[hott] def add_inf_semigroup_of_add_inf_monoid [reducible] [trans_instance] (A : Type _)
  [H : add_inf_monoid A] : add_inf_semigroup A :=
@inf_monoid.to_inf_semigroup A H

@[hott] def has_zero_of_add_inf_monoid [reducible] [trans_instance] (A : Type _)
  [H : add_inf_monoid A] : has_zero A :=
has_zero.mk (@inf_monoid.one A H)

@[hott] def zero_add [s : add_inf_monoid A] (a : A) : 0 + a = a := @inf_monoid.one_mul A s a

@[hott] def add_zero [s : add_inf_monoid A] (a : A) : a + 0 = a := @inf_monoid.mul_one A s a

@[hott] def add_comm_inf_monoid [class] : Type _ → Type _ := comm_inf_monoid

@[hott] def add_inf_monoid_of_add_comm_inf_monoid [reducible] [trans_instance] (A : Type _)
  [H : add_comm_inf_monoid A] : add_inf_monoid A :=
@comm_inf_monoid.to_inf_monoid A H

@[hott] def add_comm_inf_semigroup_of_add_comm_inf_monoid [reducible] [trans_instance] (A : Type _)
  [H : add_comm_inf_monoid A] : add_comm_inf_semigroup A :=
@comm_inf_monoid.to_comm_inf_semigroup A H

/- group -/

structure inf_group [class] (A : Type _) extends inf_monoid A, has_inv A :=
(mul_left_inv : Πa, mul (inv a) a = one)

-- Note: with more work, we could derive the axiom one_mul

section inf_group

  variable [s : inf_group A]
  include s

  @[hott] def mul.left_inv (a : A) : a⁻¹ * a = 1 := !inf_group.mul_left_inv

  @[hott] theorem inv_mul_cancel_left (a b : A) : a⁻¹ * (a * b) = b :=
  by rewrite [-mul.assoc, mul.left_inv, one_mul]

  @[hott] theorem inv_mul_cancel_right (a b : A) : a * b⁻¹ * b = a :=
  by rewrite [mul.assoc, mul.left_inv, mul_one]

  @[hott] theorem inv_eq_of_mul_eq_one {a b : A} (H : a * b = 1) : a⁻¹ = b :=
  by rewrite [-mul_one a⁻¹, -H, inv_mul_cancel_left]

  @[hott] theorem one_inv : 1⁻¹ = (1 : A) := inv_eq_of_mul_eq_one (one_mul 1)

  @[hott] theorem inv_inv (a : A) : (a⁻¹)⁻¹ = a := inv_eq_of_mul_eq_one (mul.left_inv a)

  @[hott] theorem inv.inj {a b : A} (H : a⁻¹ = b⁻¹) : a = b :=
  by rewrite [-inv_inv a, H, inv_inv b]

  @[hott] theorem inv_eq_inv_iff_eq (a b : A) : a⁻¹ = b⁻¹ ↔ a = b :=
  iff.intro (assume H, inv.inj H) (assume H, ap _ H)

  @[hott] theorem inv_eq_one_iff_eq_one (a : A) : a⁻¹ = 1 ↔ a = 1 :=
  one_inv ▸ inv_eq_inv_iff_eq a 1

  @[hott] theorem inv_eq_one {a : A} (H : a = 1) : a⁻¹ = 1 :=
  iff.mpr (inv_eq_one_iff_eq_one a) H

  @[hott] theorem eq_one_of_inv_eq_one (a : A) : a⁻¹ = 1 → a = 1 :=
    iff.mp !inv_eq_one_iff_eq_one

  @[hott] theorem eq_inv_of_eq_inv {a b : A} (H : a = b⁻¹) : b = a⁻¹ :=
  by rewrite [H, inv_inv]

  @[hott] theorem eq_inv_iff_eq_inv (a b : A) : a = b⁻¹ ↔ b = a⁻¹ :=
  iff.intro !eq_inv_of_eq_inv !eq_inv_of_eq_inv

  @[hott] theorem eq_inv_of_mul_eq_one {a b : A} (H : a * b = 1) : a = b⁻¹ :=
  begin apply eq_inv_of_eq_inv, symmetry, exact inv_eq_of_mul_eq_one H end

  @[hott] theorem mul.right_inv (a : A) : a * a⁻¹ = 1 :=
  calc
    a * a⁻¹ = (a⁻¹)⁻¹ * a⁻¹ : inv_inv
        ... = 1             : mul.left_inv

  @[hott] theorem mul_inv_cancel_left (a b : A) : a * (a⁻¹ * b) = b :=
  calc
    a * (a⁻¹ * b) = a * a⁻¹ * b : by rewrite mul.assoc
      ... = 1 * b               : mul.right_inv
      ... = b                   : one_mul

  @[hott] theorem mul_inv_cancel_right (a b : A) : a * b * b⁻¹ = a :=
  calc
    a * b * b⁻¹ = a * (b * b⁻¹) : mul.assoc
      ... = a * 1 : mul.right_inv
      ... = a : mul_one

  @[hott] theorem mul_inv (a b : A) : (a * b)⁻¹ = b⁻¹ * a⁻¹ :=
  inv_eq_of_mul_eq_one
    (calc
      a * b * (b⁻¹ * a⁻¹) = a * (b * (b⁻¹ * a⁻¹)) : mul.assoc
        ... = a * a⁻¹                             : mul_inv_cancel_left
        ... = 1                                   : mul.right_inv)

  @[hott] theorem eq_of_mul_inv_eq_one {a b : A} (H : a * b⁻¹ = 1) : a = b :=
  calc
    a = a * b⁻¹ * b : by rewrite inv_mul_cancel_right
      ... = 1 * b   : H
      ... = b       : one_mul

  @[hott] theorem eq_mul_inv_of_mul_eq {a b c : A} (H : a * c = b) : a = b * c⁻¹ :=
  by rewrite [-H, mul_inv_cancel_right]

  @[hott] theorem eq_inv_mul_of_mul_eq {a b c : A} (H : b * a = c) : a = b⁻¹ * c :=
  by rewrite [-H, inv_mul_cancel_left]

  @[hott] theorem inv_mul_eq_of_eq_mul {a b c : A} (H : b = a * c) : a⁻¹ * b = c :=
  by rewrite [H, inv_mul_cancel_left]

  @[hott] theorem mul_inv_eq_of_eq_mul {a b c : A} (H : a = c * b) : a * b⁻¹ = c :=
  by rewrite [H, mul_inv_cancel_right]

  @[hott] theorem eq_mul_of_mul_inv_eq {a b c : A} (H : a * c⁻¹ = b) : a = b * c :=
  !inv_inv ▸ (eq_mul_inv_of_mul_eq H)

  @[hott] theorem eq_mul_of_inv_mul_eq {a b c : A} (H : b⁻¹ * a = c) : a = b * c :=
  !inv_inv ▸ (eq_inv_mul_of_mul_eq H)

  @[hott] theorem mul_eq_of_eq_inv_mul {a b c : A} (H : b = a⁻¹ * c) : a * b = c :=
  !inv_inv ▸ (inv_mul_eq_of_eq_mul H)

  @[hott] theorem mul_eq_of_eq_mul_inv {a b c : A} (H : a = c * b⁻¹) : a * b = c :=
  !inv_inv ▸ (mul_inv_eq_of_eq_mul H)

  @[hott] theorem mul_eq_iff_eq_inv_mul (a b c : A) : a * b = c ↔ b = a⁻¹ * c :=
  iff.intro eq_inv_mul_of_mul_eq mul_eq_of_eq_inv_mul

  @[hott] theorem mul_eq_iff_eq_mul_inv (a b c : A) : a * b = c ↔ a = c * b⁻¹ :=
  iff.intro eq_mul_inv_of_mul_eq mul_eq_of_eq_mul_inv

  @[hott] theorem mul_left_cancel {a b c : A} (H : a * b = a * c) : b = c :=
  by rewrite [-inv_mul_cancel_left a b, H, inv_mul_cancel_left]

  @[hott] theorem mul_right_cancel {a b c : A} (H : a * b = c * b) : a = c :=
  by rewrite [-mul_inv_cancel_right a b, H, mul_inv_cancel_right]

  @[hott] theorem mul_eq_one_of_mul_eq_one {a b : A} (H : b * a = 1) : a * b = 1 :=
  by rewrite [-inv_eq_of_mul_eq_one H, mul.left_inv]

  @[hott] theorem mul_eq_one_iff_mul_eq_one (a b : A) : a * b = 1 ↔ b * a = 1 :=
  iff.intro !mul_eq_one_of_mul_eq_one !mul_eq_one_of_mul_eq_one

  @[hott] def conj_by (g a : A) := g * a * g⁻¹
  @[hott] def is_conjugate (a b : A) := Σ x, conj_by x b = a

  local infixl ` ~ ` := is_conjugate
  local infixr ` ∘c `:55 := conj_by

  @[hott] lemma conj_compose (f g a : A) : f ∘c g ∘c a = f*g ∘c a :=
      calc f ∘c g ∘c a = f * (g * a * g⁻¹) * f⁻¹ : rfl
      ... = f * (g * a) * g⁻¹ * f⁻¹ : mul.assoc
      ... = f * g * a * g⁻¹ * f⁻¹ : mul.assoc
      ... = f * g * a * (g⁻¹ * f⁻¹) : mul.assoc
      ... = f * g * a * (f * g)⁻¹ : mul_inv
  @[hott] lemma conj_id (a : A) : 1 ∘c a = a :=
      calc 1 * a * 1⁻¹ = a * 1⁻¹ : one_mul
      ... = a * 1 : one_inv
      ... = a : mul_one
  @[hott] lemma conj_one (g : A) : g ∘c 1 = 1 :=
      calc g * 1 * g⁻¹ = g * g⁻¹ : mul_one
      ... = 1 : mul.right_inv
  @[hott] lemma conj_inv_cancel (g : A) : Π a, g⁻¹ ∘c g ∘c a = a :=
      assume a, calc
      g⁻¹ ∘c g ∘c a = g⁻¹*g ∘c a : conj_compose
      ... = 1 ∘c a : mul.left_inv
      ... = a : conj_id

  @[hott] lemma conj_inv (g : A) : Π a, (g ∘c a)⁻¹ = g ∘c a⁻¹ :=
    take a, calc
    (g * a * g⁻¹)⁻¹ = g⁻¹⁻¹ * (g * a)⁻¹   : mul_inv
                ... = g⁻¹⁻¹ * (a⁻¹ * g⁻¹) : mul_inv
                ... = g⁻¹⁻¹ * a⁻¹ * g⁻¹   : mul.assoc
                ... = g * a⁻¹ * g⁻¹       : inv_inv

  @[hott] lemma is_conj.refl (a : A) : a ~ a := sigma.mk 1 (conj_id a)

  @[hott] lemma is_conj.symm (a b : A) : a ~ b → b ~ a :=
      assume Pab, obtain x (Pconj : x ∘c b = a), from Pab,
      have Pxinv : x⁻¹ ∘c x ∘c b = x⁻¹ ∘c a,   begin congruence, assumption end,
      sigma.mk x⁻¹ (inverse (conj_inv_cancel x b ▸ Pxinv))

  @[hott] lemma is_conj.trans (a b c : A) : a ~ b → b ~ c → a ~ c :=
      assume Pab, assume Pbc,
      obtain x (Px : x ∘c b = a), from Pab,
      obtain y (Py : y ∘c c = b), from Pbc,
      sigma.mk (x*y) (calc
      x*y ∘c c = x ∘c y ∘c c : conj_compose
      ... = x ∘c b : Py
      ... = a : Px)

  @[hott] def inf_group.to_left_cancel_inf_semigroup [trans_instance] : left_cancel_inf_semigroup A :=
  ⦃ left_cancel_inf_semigroup, s,
    mul_left_cancel := @mul_left_cancel A s ⦄

  @[hott] def inf_group.to_right_cancel_inf_semigroup [trans_instance] : right_cancel_inf_semigroup A :=
  ⦃ right_cancel_inf_semigroup, s,
    mul_right_cancel := @mul_right_cancel A s ⦄

  @[hott] def one_unique {a : A} (H : Πb, a * b = b) : a = 1 :=
  !mul_one⁻¹ ⬝ H 1

end inf_group

structure ab_inf_group [class] (A : Type _) extends inf_group A, comm_inf_monoid A

/- additive inf_group -/

@[hott] def add_inf_group [class] : Type _ → Type _ := inf_group

@[hott] def add_inf_semigroup_of_add_inf_group [reducible] [trans_instance] (A : Type _)
  [H : add_inf_group A] : add_inf_monoid A :=
@inf_group.to_inf_monoid A H

@[hott] def has_neg_of_add_inf_group [reducible] [trans_instance] (A : Type _)
  [H : add_inf_group A] : has_neg A :=
has_neg.mk (@inf_group.inv A H)

section add_inf_group

  variables [s : add_inf_group A]
  include s

  @[hott] theorem add.left_inv (a : A) : -a + a = 0 := @inf_group.mul_left_inv A s a

  @[hott] theorem neg_add_cancel_left (a b : A) : -a + (a + b) = b :=
  by rewrite [-add.assoc, add.left_inv, zero_add]

  @[hott] theorem neg_add_cancel_right (a b : A) : a + -b + b = a :=
  by rewrite [add.assoc, add.left_inv, add_zero]

  @[hott] theorem neg_eq_of_add_eq_zero {a b : A} (H : a + b = 0) : -a = b :=
  by rewrite [-add_zero (-a), -H, neg_add_cancel_left]

  @[hott] theorem neg_zero : -0 = (0 : A) := neg_eq_of_add_eq_zero (zero_add 0)

  @[hott] theorem neg_neg (a : A) : -(-a) = a := neg_eq_of_add_eq_zero (add.left_inv a)

  @[hott] theorem eq_neg_of_add_eq_zero {a b : A} (H : a + b = 0) : a = -b :=
  by rewrite [-neg_eq_of_add_eq_zero H, neg_neg]

  @[hott] theorem neg.inj {a b : A} (H : -a = -b) : a = b :=
  calc
    a = -(-a) : neg_neg
      ... = b : neg_eq_of_add_eq_zero (H⁻¹ ▸ (add.left_inv _))

  @[hott] theorem neg_eq_neg_iff_eq (a b : A) : -a = -b ↔ a = b :=
  iff.intro (assume H, neg.inj H) (assume H, ap _ H)

  @[hott] theorem eq_of_neg_eq_neg {a b : A} : -a = -b → a = b :=
    iff.mp !neg_eq_neg_iff_eq

  @[hott] theorem neg_eq_zero_iff_eq_zero (a : A) : -a = 0 ↔ a = 0 :=
  neg_zero ▸ !neg_eq_neg_iff_eq

  @[hott] theorem eq_zero_of_neg_eq_zero {a : A} : -a = 0 → a = 0 :=
    iff.mp !neg_eq_zero_iff_eq_zero

  @[hott] theorem eq_neg_of_eq_neg {a b : A} (H : a = -b) : b = -a :=
  H⁻¹ ▸ (neg_neg b)⁻¹

  @[hott] theorem eq_neg_iff_eq_neg (a b : A) : a = -b ↔ b = -a :=
  iff.intro !eq_neg_of_eq_neg !eq_neg_of_eq_neg

  @[hott] theorem add.right_inv (a : A) : a + -a = 0 :=
  calc
    a + -a = -(-a) + -a : neg_neg
      ... = 0 : add.left_inv

  @[hott] theorem add_neg_cancel_left (a b : A) : a + (-a + b) = b :=
  by rewrite [-add.assoc, add.right_inv, zero_add]

  @[hott] theorem add_neg_cancel_right (a b : A) : a + b + -b = a :=
  by rewrite [add.assoc, add.right_inv, add_zero]

  @[hott] theorem neg_add_rev (a b : A) : -(a + b) = -b + -a :=
  neg_eq_of_add_eq_zero
    begin
      rewrite [add.assoc, add_neg_cancel_left, add.right_inv]
    end

  -- TODO: delete these in favor of sub rules?
  @[hott] theorem eq_add_neg_of_add_eq {a b c : A} (H : a + c = b) : a = b + -c :=
  H ▸ !add_neg_cancel_right⁻¹

  @[hott] theorem eq_neg_add_of_add_eq {a b c : A} (H : b + a = c) : a = -b + c :=
  H ▸ !neg_add_cancel_left⁻¹

  @[hott] theorem neg_add_eq_of_eq_add {a b c : A} (H : b = a + c) : -a + b = c :=
  H⁻¹ ▸ !neg_add_cancel_left

  @[hott] theorem add_neg_eq_of_eq_add {a b c : A} (H : a = c + b) : a + -b = c :=
  H⁻¹ ▸ !add_neg_cancel_right

  @[hott] theorem eq_add_of_add_neg_eq {a b c : A} (H : a + -c = b) : a = b + c :=
  !neg_neg ▸ (eq_add_neg_of_add_eq H)

  @[hott] theorem eq_add_of_neg_add_eq {a b c : A} (H : -b + a = c) : a = b + c :=
  !neg_neg ▸ (eq_neg_add_of_add_eq H)

  @[hott] theorem add_eq_of_eq_neg_add {a b c : A} (H : b = -a + c) : a + b = c :=
  !neg_neg ▸ (neg_add_eq_of_eq_add H)

  @[hott] theorem add_eq_of_eq_add_neg {a b c : A} (H : a = c + -b) : a + b = c :=
  !neg_neg ▸ (add_neg_eq_of_eq_add H)

  @[hott] theorem add_eq_iff_eq_neg_add (a b c : A) : a + b = c ↔ b = -a + c :=
  iff.intro eq_neg_add_of_add_eq add_eq_of_eq_neg_add

  @[hott] theorem add_eq_iff_eq_add_neg (a b c : A) : a + b = c ↔ a = c + -b :=
  iff.intro eq_add_neg_of_add_eq add_eq_of_eq_add_neg

  @[hott] theorem add_left_cancel {a b c : A} (H : a + b = a + c) : b = c :=
  calc b = -a + (a + b) : !neg_add_cancel_left⁻¹
     ... = -a + (a + c) : H
     ... = c : neg_add_cancel_left

  @[hott] theorem add_right_cancel {a b c : A} (H : a + b = c + b) : a = c :=
  calc a = (a + b) + -b : !add_neg_cancel_right⁻¹
     ... = (c + b) + -b : H
     ... = c : add_neg_cancel_right

  @[hott] def add_inf_group.to_add_left_cancel_inf_semigroup [reducible] [trans_instance] :
    add_left_cancel_inf_semigroup A :=
  @inf_group.to_left_cancel_inf_semigroup A s

  @[hott] def add_inf_group.to_add_right_cancel_inf_semigroup [reducible] [trans_instance] :
    add_right_cancel_inf_semigroup A :=
  @inf_group.to_right_cancel_inf_semigroup A s

  @[hott] theorem add_neg_eq_neg_add_rev {a b : A} : a + -b = -(b + -a) :=
  by rewrite [neg_add_rev, neg_neg]

  /- sub -/

  -- TODO: derive corresponding facts for div in a field
  @[hott] protected def algebra.sub [reducible] (a b : A) : A := a + -b

  @[hott] def add_inf_group_has_sub [instance] : has_sub A :=
  has_sub.mk algebra.sub

  @[hott] theorem sub_eq_add_neg (a b : A) : a - b = a + -b := rfl

  @[hott] theorem sub_self (a : A) : a - a = 0 := !add.right_inv

  @[hott] theorem sub_add_cancel (a b : A) : a - b + b = a := !neg_add_cancel_right

  @[hott] theorem add_sub_cancel (a b : A) : a + b - b = a := !add_neg_cancel_right

  @[hott] theorem eq_of_sub_eq_zero {a b : A} (H : a - b = 0) : a = b :=
  calc
    a = (a - b) + b : !sub_add_cancel⁻¹
      ... = 0 + b : H
      ... = b : zero_add

  @[hott] theorem eq_iff_sub_eq_zero (a b : A) : a = b ↔ a - b = 0 :=
  iff.intro (assume H, H ▸ !sub_self) (assume H, eq_of_sub_eq_zero H)

  @[hott] theorem zero_sub (a : A) : 0 - a = -a := !zero_add

  @[hott] theorem sub_zero (a : A) : a - 0 = a :=
  by rewrite [sub_eq_add_neg, neg_zero, add_zero]

  @[hott] theorem sub_neg_eq_add (a b : A) : a - (-b) = a + b :=
  by change a + -(-b) = a + b; rewrite neg_neg

  @[hott] theorem neg_sub (a b : A) : -(a - b) = b - a :=
  neg_eq_of_add_eq_zero
    (calc
      a - b + (b - a) = a - b + b - a : by krewrite -add.assoc
        ... = a - a                   : sub_add_cancel
        ... = 0                       : sub_self)

  @[hott] theorem add_sub (a b c : A) : a + (b - c) = a + b - c := !add.assoc⁻¹

  @[hott] theorem sub_add_eq_sub_sub_swap (a b c : A) : a - (b + c) = a - c - b :=
  calc
    a - (b + c) = a + (-c - b) : by rewrite [sub_eq_add_neg, neg_add_rev]
            ... = a - c - b    : by krewrite -add.assoc

  @[hott] theorem sub_eq_iff_eq_add (a b c : A) : a - b = c ↔ a = c + b :=
  iff.intro (assume H, eq_add_of_add_neg_eq H) (assume H, add_neg_eq_of_eq_add H)

  @[hott] theorem eq_sub_iff_add_eq (a b c : A) : a = b - c ↔ a + c = b :=
  iff.intro (assume H, add_eq_of_eq_add_neg H) (assume H, eq_add_neg_of_add_eq H)

  @[hott] theorem eq_iff_eq_of_sub_eq_sub {a b c d : A} (H : a - b = c - d) : a = b ↔ c = d :=
  calc
    a = b ↔ a - b = 0   : eq_iff_sub_eq_zero
      ... = (c - d = 0) : H
      ... ↔ c = d       : iff.symm (eq_iff_sub_eq_zero c d)

  @[hott] theorem eq_sub_of_add_eq {a b c : A} (H : a + c = b) : a = b - c :=
  !eq_add_neg_of_add_eq H

  @[hott] theorem sub_eq_of_eq_add {a b c : A} (H : a = c + b) : a - b = c :=
  !add_neg_eq_of_eq_add H

  @[hott] theorem eq_add_of_sub_eq {a b c : A} (H : a - c = b) : a = b + c :=
  eq_add_of_add_neg_eq H

  @[hott] theorem add_eq_of_eq_sub {a b c : A} (H : a = c - b) : a + b = c :=
  add_eq_of_eq_add_neg H

  @[hott] def zero_unique {a : A} (H : Πb, a + b = b) : a = 0 :=
  !add_zero⁻¹ ⬝ H 0

end add_inf_group

@[hott] def add_ab_inf_group [class] : Type _ → Type _ := ab_inf_group

@[hott] def add_inf_group_of_add_ab_inf_group [reducible] [trans_instance] (A : Type _)
  [H : add_ab_inf_group A] : add_inf_group A :=
@ab_inf_group.to_inf_group A H

@[hott] def add_comm_inf_monoid_of_add_ab_inf_group [reducible] [trans_instance] (A : Type _)
  [H : add_ab_inf_group A] : add_comm_inf_monoid A :=
@ab_inf_group.to_comm_inf_monoid A H

section add_ab_inf_group
  variable [s : add_ab_inf_group A]
  include s

  @[hott] theorem sub_add_eq_sub_sub (a b c : A) : a - (b + c) = a - b - c :=
  !add.comm ▸ !sub_add_eq_sub_sub_swap

  @[hott] theorem neg_add_eq_sub (a b : A) : -a + b = b - a := !add.comm

  @[hott] theorem neg_add (a b : A) : -(a + b) = -a + -b := add.comm (-b) (-a) ▸ neg_add_rev a b

  @[hott] theorem sub_add_eq_add_sub (a b c : A) : a - b + c = a + c - b := !add.right_comm

  @[hott] theorem sub_sub (a b c : A) : a - b - c = a - (b + c) :=
  by rewrite [▸ a + -b + -c = _, add.assoc, -neg_add]

  @[hott] theorem add_sub_add_left_eq_sub (a b c : A) : (c + a) - (c + b) = a - b :=
  by rewrite [sub_add_eq_sub_sub, (add.comm c a), add_sub_cancel]

  @[hott] theorem eq_sub_of_add_eq' {a b c : A} (H : c + a = b) : a = b - c :=
  !eq_sub_of_add_eq (!add.comm ▸ H)

  @[hott] theorem sub_eq_of_eq_add' {a b c : A} (H : a = b + c) : a - b = c :=
  !sub_eq_of_eq_add (!add.comm ▸ H)

  @[hott] theorem eq_add_of_sub_eq' {a b c : A} (H : a - b = c) : a = b + c :=
  !add.comm ▸ eq_add_of_sub_eq H

  @[hott] theorem add_eq_of_eq_sub' {a b c : A} (H : b = c - a) : a + b = c :=
  !add.comm ▸ add_eq_of_eq_sub H

  @[hott] theorem sub_sub_self (a b : A) : a - (a - b) = b :=
  by rewrite [sub_eq_add_neg, neg_sub, add.comm, sub_add_cancel]

  @[hott] theorem add_sub_comm (a b c d : A) : a + b - (c + d) = (a - c) + (b - d) :=
    by rewrite [sub_add_eq_sub_sub, -sub_add_eq_add_sub a c b, add_sub]

  @[hott] theorem sub_eq_sub_add_sub (a b c : A) : a - b = c - b + (a - c) :=
    by rewrite [add_sub, sub_add_cancel] ⬝ !add.comm

  @[hott] theorem neg_neg_sub_neg (a b : A) : - (-a - -b) = a - b :=
    by rewrite [neg_sub, sub_neg_eq_add, neg_add_eq_sub]
end add_ab_inf_group

@[hott] def inf_group_of_add_inf_group (A : Type _) [G : add_inf_group A] : inf_group A :=
⦃inf_group,
  mul             := has_add.add,
  mul_assoc       := add.assoc,
  one             := !has_zero.zero,
  one_mul         := zero_add,
  mul_one         := add_zero,
  inv             := has_neg.neg,
  mul_left_inv    := add.left_inv ⦄

@[hott] theorem add.comm4 [s : add_comm_inf_semigroup A] :
  Π (n m k l : A), n + m + (k + l) = n + k + (m + l) :=
comm4 add.comm add.assoc

@[hott] def add1 [s : has_add A] [s' : has_one A] (a : A) : A := add a one

@[hott] theorem add_comm_three [s : add_comm_inf_semigroup A] (a b c : A) : a + b + c = c + b + a :=
  by rewrite [{a + _}add.comm, {_ + c}add.comm, -*add.assoc]

@[hott] theorem add_comm_four [s : add_comm_inf_semigroup A] (a b : A) :
  a + a + (b + b) = (a + b) + (a + b) :=
!add.comm4

@[hott] theorem add_comm_middle [s : add_comm_inf_semigroup A] (a b c : A) : a + b + c = a + c + b :=
  by rewrite [add.assoc, add.comm b, -add.assoc]

@[hott] theorem bit0_add_bit0 [s : add_comm_inf_semigroup A] (a b : A) : bit0 a + bit0 b = bit0 (a + b) :=
  !add_comm_four

@[hott] theorem bit0_add_bit0_helper [s : add_comm_inf_semigroup A] (a b t : A) (H : a + b = t) :
        bit0 a + bit0 b = bit0 t :=
  by rewrite -H; apply bit0_add_bit0

@[hott] theorem bit1_add_bit0 [s : add_comm_inf_semigroup A] [s' : has_one A] (a b : A) :
        bit1 a + bit0 b = bit1 (a + b) :=
  begin
    rewrite [↑bit0, ↑bit1, add_comm_middle], congruence, apply add_comm_four
  end

@[hott] theorem bit1_add_bit0_helper [s : add_comm_inf_semigroup A] [s' : has_one A] (a b t : A)
        (H : a + b = t) : bit1 a + bit0 b = bit1 t :=
  by rewrite -H; apply bit1_add_bit0

@[hott] theorem bit0_add_bit1 [s : add_comm_inf_semigroup A] [s' : has_one A] (a b : A) :
        bit0 a + bit1 b = bit1 (a + b) :=
  by rewrite [{bit0 a + bit1 b}add.comm,{a + b}add.comm]; exact bit1_add_bit0 b a

@[hott] theorem bit0_add_bit1_helper [s : add_comm_inf_semigroup A] [s' : has_one A] (a b t : A)
        (H : a + b = t) : bit0 a + bit1 b = bit1 t :=
  by rewrite -H; apply bit0_add_bit1

@[hott] theorem bit1_add_bit1 [s : add_comm_inf_semigroup A] [s' : has_one A] (a b : A) :
        bit1 a + bit1 b = bit0 (add1 (a + b)) :=
  begin
    rewrite ↑[bit0, bit1, add1, add.assoc],
    rewrite [*add.assoc, {_ + (b + 1)}add.comm, {_ + (b + 1 + _)}add.comm,
      {_ + (b + 1 + _ + _)}add.comm, *add.assoc, {1 + a}add.comm, -{b + (a + 1)}add.assoc,
      {b + a}add.comm, *add.assoc]
  end

@[hott] theorem bit1_add_bit1_helper [s : add_comm_inf_semigroup A] [s' : has_one A] (a b t s: A)
        (H : (a + b) = t) (H2 : add1 t = s) : bit1 a + bit1 b = bit0 s :=
  begin rewrite [-H2, -H], apply bit1_add_bit1 end

@[hott] theorem bin_add_zero [s : add_inf_monoid A] (a : A) : a + zero = a := !add_zero

@[hott] theorem bin_zero_add [s : add_inf_monoid A] (a : A) : zero + a = a := !zero_add

@[hott] theorem one_add_bit0 [s : add_comm_inf_semigroup A] [s' : has_one A] (a : A) : one + bit0 a = bit1 a :=
  begin rewrite ↑[bit0, bit1], rewrite add.comm end

@[hott] theorem bit0_add_one [s : has_add A] [s' : has_one A] (a : A) : bit0 a + one = bit1 a :=
  rfl

@[hott] theorem bit1_add_one [s : has_add A] [s' : has_one A] (a : A) : bit1 a + one = add1 (bit1 a) :=
  rfl

@[hott] theorem bit1_add_one_helper [s : has_add A] [s' : has_one A] (a t : A) (H : add1 (bit1 a) = t) :
        bit1 a + one = t :=
  by rewrite -H

@[hott] theorem one_add_bit1 [s : add_comm_inf_semigroup A] [s' : has_one A] (a : A) :
        one + bit1 a = add1 (bit1 a) := !add.comm

@[hott] theorem one_add_bit1_helper [s : add_comm_inf_semigroup A] [s' : has_one A] (a t : A)
        (H : add1 (bit1 a) = t) : one + bit1 a = t :=
  by rewrite -H; apply one_add_bit1

@[hott] theorem add1_bit0 [s : has_add A] [s' : has_one A] (a : A) : add1 (bit0 a) = bit1 a :=
  rfl

@[hott] theorem add1_bit1 [s : add_comm_inf_semigroup A] [s' : has_one A] (a : A) :
        add1 (bit1 a) = bit0 (add1 a) :=
  begin
    rewrite ↑[add1, bit1, bit0],
    rewrite [add.assoc, add_comm_four]
  end

@[hott] theorem add1_bit1_helper [s : add_comm_inf_semigroup A] [s' : has_one A] (a t : A) (H : add1 a = t) :
        add1 (bit1 a) = bit0 t :=
  by rewrite -H; apply add1_bit1

@[hott] theorem add1_one [s : has_add A] [s' : has_one A] : add1 (one : A) = bit0 one :=
  rfl

@[hott] theorem add1_zero [s : add_inf_monoid A] [s' : has_one A] : add1 (zero : A) = one :=
  begin
    rewrite [↑add1, zero_add]
  end

@[hott] theorem one_add_one [s : has_add A] [s' : has_one A] : (one : A) + one = bit0 one :=
  rfl

@[hott] theorem subst_into_sum [s : has_add A] (l r tl tr t : A) (prl : l = tl) (prr : r = tr)
        (prt : tl + tr = t) : l + r = t :=
   by rewrite [prl, prr, prt]

@[hott] theorem neg_zero_helper [s : add_inf_group A] (a : A) (H : a = 0) : - a = 0 :=
  by rewrite [H, neg_zero]


end algebra
