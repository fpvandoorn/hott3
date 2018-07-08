/-
Copyright (c) 2014 Robert Lewis. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Lewis

Structures with multiplicative and additive components, including division rings and fields.
The development is modeled after Isabelle's library.
-/
import .ring
universes u v w
hott_theory
set_option old_structure_cmd true

namespace hott
variable {A : Type _}

namespace algebra
@[hott, class] structure division_ring (A : Type _) extends ring A, has_inv A, zero_ne_one_class A :=
  (mul_inv_cancel : Π{a}, a ≠ zero → mul a (inv a) = one)
  (inv_mul_cancel : Π{a}, a ≠ zero → mul (inv a) a = one)

section division_ring
  variables [s : division_ring A] {a b c : A}
  include s

  @[hott] protected def algebra.div (a b : A) : A := a * b⁻¹

  @[hott, instance] def division_ring_has_div : has_div A :=
  has_div.mk algebra.div

  @[hott] lemma division.def (a b : A) : a / b = a * b⁻¹ :=
  rfl

  @[hott] theorem mul_inv_cancel (H : a ≠ 0) : a * a⁻¹ = 1 :=
  division_ring.mul_inv_cancel H

  @[hott] theorem inv_mul_cancel (H : a ≠ 0) : a⁻¹ * a = 1 :=
  division_ring.inv_mul_cancel H

  @[hott] theorem inv_eq_one_div (a : A) : a⁻¹ = 1 / a := (one_mul _)⁻¹

  @[hott] theorem div_eq_mul_one_div (a b : A) : a / b = a * (1 / b) :=
    by rewrite [*division.def, one_mul]

  @[hott] theorem mul_one_div_cancel (H : a ≠ 0) : a * (1 / a) = 1 :=
    by rewrite [-inv_eq_one_div, (mul_inv_cancel H)]

  @[hott] theorem one_div_mul_cancel (H : a ≠ 0) : (1 / a) * a = 1 :=
    by rewrite [-inv_eq_one_div, (inv_mul_cancel H)]

  @[hott] theorem div_self (H : a ≠ 0) : a / a = 1 := mul_inv_cancel H

  @[hott] theorem one_div_one : 1 / 1 = (1:A) := div_self (ne.symm zero_ne_one)

  @[hott] theorem mul_div_assoc (a b : A) : (a * b) / c = a * (b / c) := mul.assoc _ _ _

  @[hott] theorem one_div_ne_zero (H : a ≠ 0) : 1 / a ≠ 0 :=
    assume H2 : 1 / a = 0,
    have C1 : 0 = (1:A), from symm (by rewrite [-(mul_one_div_cancel H), H2, mul_zero]),
    absurd C1 zero_ne_one

  @[hott] theorem one_inv_eq : 1⁻¹ = (1:A) :=
  by rewrite [-mul_one ((1:A)⁻¹), inv_mul_cancel (ne.symm (@zero_ne_one A _))]

  @[hott] theorem div_one (a : A) : a / 1 = a :=
    by rewrite [*division.def, one_inv_eq, mul_one]

  @[hott] theorem zero_div (a : A) : 0 / a = 0 := zero_mul _

  -- note: integral domain has a "mul_ne_zero". A commutative division ring is an integral
  -- domain, but let's not define that class for now.
  @[hott] theorem division_ring.mul_ne_zero (Ha : a ≠ 0) (Hb : b ≠ 0) : a * b ≠ 0 :=
    assume H : a * b = 0,
    have C1 : a = 0, by rewrite [-(mul_one a), -(mul_one_div_cancel Hb), -mul.assoc, H, zero_mul],
      absurd C1 Ha

  @[hott] theorem mul_ne_zero_comm (H : a * b ≠ 0) : b * a ≠ 0 :=
    have H2 : a ≠ 0 × b ≠ 0, from ne_zero_prod_ne_zero_of_mul_ne_zero H,
    division_ring.mul_ne_zero (prod.pr2 H2) (prod.pr1 H2)

  @[hott] theorem eq_one_div_of_mul_eq_one (H : a * b = 1) : b = 1 / a :=
    have a ≠ 0, from
      (suppose a = 0,
       have 0 = (1:A), by rewrite [-(zero_mul b), -this, H],
       absurd this zero_ne_one),
    show b = 1 / a, from symm (calc
      1 / a = (1 / a) * 1       : mul_one
        ... = (1 / a) * (a * b) : H
        ... = (1 / a) * a * b   : mul.assoc
        ... = 1 * b             : one_div_mul_cancel this
        ... = b                 : one_mul)

  @[hott] theorem eq_one_div_of_mul_eq_one_left (H : b * a = 1) : b = 1 / a :=
    have a ≠ 0, from
      (suppose a = 0,
       have 0 = 1, from symm (calc
          1 = b * a : symm H
        ... = b * 0 : this
        ... = 0     : mul_zero),
      absurd this zero_ne_one),
    show b = 1 / a, from symm (calc
      1 / a = 1 * (1 / a)       : one_mul
        ... = b * a * (1 / a)   : H
        ... = b * (a * (1 / a)) : mul.assoc
        ... = b * 1             : mul_one_div_cancel this
        ... = b                 : mul_one)

  @[hott] theorem division_ring.one_div_mul_one_div (Ha : a ≠ 0) (Hb : b ≠ 0) :
      (1 / a) * (1 / b) = 1 / (b * a) :=
    have (b * a) * ((1 / a) * (1 / b)) = 1, by
      rewrite [mul.assoc, -(mul.assoc a), (mul_one_div_cancel Ha), one_mul,
               (mul_one_div_cancel Hb)],
    eq_one_div_of_mul_eq_one this

  @[hott] theorem one_div_neg_one_eq_neg_one : (1:A) / (-1) = -1 :=
    have (-1) * (-1) = (1:A), by rewrite [-neg_eq_neg_one_mul, neg_neg],
    symm (eq_one_div_of_mul_eq_one this)

  @[hott] theorem division_ring.one_div_neg_eq_neg_one_div (H : a ≠ 0) : 1 / (- a) = - (1 / a) :=
    have -1 ≠ (0:A), from
      (suppose -1 = 0, absurd (symm (calc
          1 = -(-1) : neg_neg
        ... = -0    : this
        ... = (0:A) : neg_zero)) zero_ne_one),
    calc
      1 / (- a) = 1 / ((-1) * a)        : neg_eq_neg_one_mul
            ... = (1 / a) * (1 / (- 1)) : division_ring.one_div_mul_one_div H this
            ... = (1 / a) * (-1)        : one_div_neg_one_eq_neg_one
            ... = - (1 / a)             : mul_neg_one_eq_neg

  @[hott] theorem div_neg_eq_neg_div (b : A) (Ha : a ≠ 0) : b / (- a) = - (b / a) :=
    calc
      b / (- a) = b * (1 / (- a)) : by rewrite -inv_eq_one_div
            ... = b * -(1 / a)    : division_ring.one_div_neg_eq_neg_one_div Ha
            ... = -(b * (1 / a))  : neg_mul_eq_mul_neg
            ... = - (b * a⁻¹)     : inv_eq_one_div

  @[hott] theorem neg_div (a b : A) : (-b) / a = - (b / a) :=
    by rewrite [neg_eq_neg_one_mul, mul_div_assoc, -neg_eq_neg_one_mul]

  @[hott] theorem division_ring.neg_div_neg_eq (a : A) {b : A} (Hb : b ≠ 0) : (-a) / (-b) = a / b :=
    by rewrite [(div_neg_eq_neg_div _ Hb), neg_div, neg_neg]

  @[hott] theorem division_ring.one_div_one_div (H : a ≠ 0) : 1 / (1 / a) = a :=
    symm (eq_one_div_of_mul_eq_one_left (mul_one_div_cancel H))

  @[hott] theorem division_ring.eq_of_one_div_eq_one_div (Ha : a ≠ 0) (Hb : b ≠ 0) (H : 1 / a = 1 / b) :
      a = b :=
    by rewrite [-(division_ring.one_div_one_div Ha), H, (division_ring.one_div_one_div Hb)]

  @[hott] theorem mul_inv_eq (Ha : a ≠ 0) (Hb : b ≠ 0) : (b * a)⁻¹ = a⁻¹ * b⁻¹ :=
    inverse (calc
      a⁻¹ * b⁻¹ = (1 / a) * b⁻¹ : inv_eq_one_div
      ... = (1 / a) * (1 / b)   : inv_eq_one_div
      ... = (1 / (b * a))       : division_ring.one_div_mul_one_div Ha Hb
      ... = (b * a)⁻¹           : inv_eq_one_div)

  @[hott] theorem mul_div_cancel (a : A) {b : A} (Hb : b ≠ 0) : a * b / b = a :=
    by rewrite [*division.def, mul.assoc, (mul_inv_cancel Hb), mul_one]

  @[hott] theorem div_mul_cancel (a : A) {b : A} (Hb : b ≠ 0) : a / b * b = a :=
    by rewrite [*division.def, mul.assoc, (inv_mul_cancel Hb), mul_one]

  @[hott] theorem div_add_div_same (a b c : A) : a / c + b / c = (a + b) / c := !right_distrib⁻¹

  @[hott] theorem div_sub_div_same (a b c : A) : (a / c) - (b / c) = (a - b) / c :=
    by rewrite [sub_eq_add_neg, -neg_div, div_add_div_same]

  @[hott] theorem one_div_mul_add_mul_one_div_eq_one_div_add_one_div (Ha : a ≠ 0) (Hb : b ≠ 0) :
          (1 / a) * (a + b) * (1 / b) = 1 / a + 1 / b :=
    by rewrite [(left_distrib (1 / a)), (one_div_mul_cancel Ha), right_distrib, one_mul,
      mul.assoc, (mul_one_div_cancel Hb), mul_one, add.comm]

  @[hott] theorem one_div_mul_sub_mul_one_div_eq_one_div_add_one_div (Ha : a ≠ 0) (Hb : b ≠ 0) :
          (1 / a) * (b - a) * (1 / b) = 1 / a - 1 / b :=
    by rewrite [(mul_sub_left_distrib (1 / a)), (one_div_mul_cancel Ha), mul_sub_right_distrib,
      one_mul, mul.assoc, (mul_one_div_cancel Hb), mul_one]

  @[hott] theorem div_eq_one_iff_eq (a : A) {b : A} (Hb : b ≠ 0) : a / b = 1 ↔ a = b :=
    iff.intro
    (suppose a / b = 1, symm (calc
      b   = 1 * b     : one_mul
      ... = a / b * b : this
      ... = a         : div_mul_cancel _ Hb))
    (suppose a = b, calc
      a / b = b / b : this
        ... = 1     : div_self Hb)

  @[hott] theorem eq_of_div_eq_one (a : A) {b : A} (Hb : b ≠ 0) : a / b = 1 → a = b :=
    iff.mp (!div_eq_one_iff_eq Hb)

  @[hott] theorem eq_div_iff_mul_eq (a : A) {b : A} (Hc : c ≠ 0) : a = b / c ↔ a * c = b :=
    iff.intro
      (suppose a = b / c, by rewrite [this, (!div_mul_cancel Hc)])
      (suppose a * c = b, begin rewrite [-mul_div_cancel a Hc, this] end)

  @[hott] theorem eq_div_of_mul_eq (a b : A) {c : A} (Hc : c ≠ 0) : a * c = b → a = b / c :=
    iff.mpr (!eq_div_iff_mul_eq Hc)

  @[hott] theorem mul_eq_of_eq_div (a b: A) {c : A} (Hc : c ≠ 0) : a = b / c → a * c = b :=
    iff.mp (!eq_div_iff_mul_eq Hc)

  @[hott] theorem add_div_eq_mul_add_div (a b : A) {c : A} (Hc : c ≠ 0) : a + b / c = (a * c + b) / c :=
    have (a + b / c) * c = a * c + b, by rewrite [right_distrib, (!div_mul_cancel Hc)],
    (iff.elim_right (!eq_div_iff_mul_eq Hc)) this

  @[hott] theorem mul_mul_div (a : A) {c : A} (Hc : c ≠ 0) : a = a * c * (1 / c) :=
    calc
      a   = a * 1             : mul_one
      ... = a * (c * (1 / c)) : mul_one_div_cancel Hc
      ... = a * c * (1 / c)   : mul.assoc

  -- There are many similar rules to these last two in the Isabelle library
  -- that haven't been ported yet. Do as necessary.
end division_ring

@[hott, class] structure field (A : Type _) extends division_ring A, comm_ring A

section field
  variables [s : field A] {a b c d: A}
  include s

  @[hott] theorem field.one_div_mul_one_div (Ha : a ≠ 0) (Hb : b ≠ 0) : (1 / a) * (1 / b) =  1 / (a * b) :=
     by rewrite [(division_ring.one_div_mul_one_div Ha Hb), mul.comm b]

  @[hott] theorem field.div_mul_right (Hb : b ≠ 0) (H : a * b ≠ 0) : a / (a * b) = 1 / b :=
    have a ≠ 0, from prod.pr1 (ne_zero_prod_ne_zero_of_mul_ne_zero H),
    symm (calc
      1 / b = 1 * (1 / b)             : one_mul
        ... = (a * a⁻¹) * (1 / b)     : mul_inv_cancel this
        ... = a * (a⁻¹ * (1 / b))     : mul.assoc
        ... = a * ((1 / a) * (1 / b)) : inv_eq_one_div
        ... = a * (1 / (b * a))       : division_ring.one_div_mul_one_div this Hb
        ... = a * (1 / (a * b))       : mul.comm
        ... = a * (a * b)⁻¹           : inv_eq_one_div)

  @[hott] theorem field.div_mul_left (Ha : a ≠ 0) (H : a * b ≠ 0) : b / (a * b) = 1 / a :=
    let H1 : b * a ≠ 0 := mul_ne_zero_comm H in
    by rewrite [mul.comm a, (field.div_mul_right Ha H1)]

  @[hott] theorem mul_div_cancel_left (Ha : a ≠ 0) : a * b / a = b :=
    by rewrite [mul.comm a, (!mul_div_cancel Ha)]

  @[hott] theorem mul_div_cancel' (Hb : b ≠ 0) : b * (a / b) = a :=
    by rewrite [mul.comm, (!div_mul_cancel Hb)]

  @[hott] theorem one_div_add_one_div (Ha : a ≠ 0) (Hb : b ≠ 0) : 1 / a + 1 / b = (a + b) / (a * b) :=
    have a * b ≠ 0, from (division_ring.mul_ne_zero Ha Hb),
    by rewrite [add.comm, -(field.div_mul_left Ha this), -(field.div_mul_right Hb this), *division.def,
                -right_distrib]

  @[hott] theorem field.div_mul_div (a : A) {b : A} (c : A) {d : A} (Hb : b ≠ 0) (Hd : d ≠ 0) :
      (a / b) * (c / d) = (a * c) / (b * d) :=
     by rewrite [*division.def, 2 mul.assoc, (mul.comm b⁻¹), mul.assoc, (mul_inv_eq Hd Hb)]

  @[hott] theorem mul_div_mul_left (a : A) {b c : A} (Hb : b ≠ 0) (Hc : c ≠ 0) :
      (c * a) / (c * b) = a / b :=
    by rewrite [-(!field.div_mul_div Hc Hb), (div_self Hc), one_mul]

  @[hott] theorem mul_div_mul_right (a : A) {b c : A} (Hb : b ≠ 0) (Hc : c ≠ 0) :
      (a * c) / (b * c) = a / b :=
    by rewrite [(mul.comm a), (mul.comm b), (!mul_div_mul_left Hb Hc)]

  @[hott] theorem div_mul_eq_mul_div (a b c : A) : (b / c) * a = (b * a) / c :=
    by rewrite [*division.def, mul.assoc, (mul.comm c⁻¹), -mul.assoc]

  @[hott] theorem field.div_mul_eq_mul_div_comm (a b : A) {c : A} (Hc : c ≠ 0) :
      (b / c) * a = b * (a / c) :=
    by rewrite [(div_mul_eq_mul_div), -(one_mul c), -(!field.div_mul_div (ne.symm zero_ne_one) Hc),
                div_one, one_mul]

  @[hott] theorem div_add_div (a : A) {b : A} (c : A) {d : A} (Hb : b ≠ 0) (Hd : d ≠ 0) :
      (a / b) + (c / d) = ((a * d) + (b * c)) / (b * d) :=
    by rewrite [-(!mul_div_mul_right Hb Hd), -(!mul_div_mul_left Hd Hb), div_add_div_same]

  @[hott] theorem div_sub_div (a : A) {b : A} (c : A) {d : A} (Hb : b ≠ 0) (Hd : d ≠ 0) :
      (a / b) - (c / d) = ((a * d) - (b * c)) / (b * d) :=
      by rewrite [*sub_eq_add_neg, neg_eq_neg_one_mul, -mul_div_assoc, (!div_add_div Hb Hd),
         -mul.assoc, (mul.comm b), mul.assoc, -neg_eq_neg_one_mul]

  @[hott] theorem mul_eq_mul_of_div_eq_div (a : A) {b : A} (c : A) {d : A} (Hb : b ≠ 0)
      (Hd : d ≠ 0) (H : a / b = c / d) : a * d = c * b :=
    by rewrite [-mul_one (a*d), mul.assoc, (mul.comm d), -mul.assoc, -(div_self Hb),
         -(!field.div_mul_eq_mul_div_comm Hb), H, (div_mul_eq_mul_div), (!div_mul_cancel Hd)]

  @[hott] theorem field.one_div_div (Ha : a ≠ 0) (Hb : b ≠ 0) : 1 / (a / b) = b / a :=
    have (a / b) * (b / a) = 1, from calc
      (a / b) * (b / a) = (a * b) / (b * a) : !field.div_mul_div Hb Ha
      ... = (a * b) / (a * b) : mul.comm
      ... = 1 : div_self (division_ring.mul_ne_zero Ha Hb),
    symm (eq_one_div_of_mul_eq_one this)

  @[hott] theorem field.div_div_eq_mul_div (a : A) {b c : A} (Hb : b ≠ 0) (Hc : c ≠ 0) :
      a / (b / c) = (a * c) / b :=
    by rewrite [div_eq_mul_one_div, (field.one_div_div Hb Hc), -mul_div_assoc]

  @[hott] theorem field.div_div_eq_div_mul (a : A) {b c : A} (Hb : b ≠ 0) (Hc : c ≠ 0) :
      (a / b) / c = a / (b * c) :=
    by rewrite [div_eq_mul_one_div, (!field.div_mul_div Hb Hc), mul_one]

  @[hott] theorem field.div_div_div_div_eq (a : A) {b c d : A} (Hb : b ≠ 0) (Hc : c ≠ 0) (Hd : d ≠ 0) :
       (a / b) / (c / d) = (a * d) / (b * c) :=
    by rewrite [(!field.div_div_eq_mul_div Hc Hd), (div_mul_eq_mul_div),
                (!field.div_div_eq_div_mul Hb Hc)]

  @[hott] theorem field.div_mul_eq_div_mul_one_div (a : A) {b c : A} (Hb : b ≠ 0) (Hc : c ≠ 0) :
      a / (b * c) = (a / b) * (1 / c) :=
    by rewrite [-!field.div_div_eq_div_mul Hb Hc, -div_eq_mul_one_div]

  @[hott] theorem eq_of_mul_eq_mul_of_nonzero_left {a b c : A} (H : a ≠ 0) (H2 : a * b = a * c) : b = c :=
    by rewrite [-one_mul b, -div_self H, div_mul_eq_mul_div, H2, mul_div_cancel_left H]

  @[hott] theorem eq_of_mul_eq_mul_of_nonzero_right {a b c : A} (H : c ≠ 0) (H2 : a * c = b * c) : a = b :=
    by rewrite [-mul_one a, -div_self H, -mul_div_assoc, H2, mul_div_cancel _ H]

end field

@[hott, class] structure discrete_field (A : Type _) extends field A :=
  (has_decidable_eq : decidable_eq A)
  (inv_zero : inv zero = zero)

attribute [instance] discrete_field.has_decidable_eq

section discrete_field
  variable [s : discrete_field A]
  include s
  variables {a b c d : A}

  -- many of the theorems in discrete_field are the same as theorems in field sum division ring,
  -- but with fewer hypotheses since 0⁻¹ = 0 and equality is decidable.

  @[hott] theorem discrete_field.eq_zero_sum_eq_zero_of_mul_eq_zero
    (x y : A) (H : x * y = 0) : x = 0 ⊎ y = 0 :=
  decidable.by_cases
    (suppose x = 0, sum.inl this)
    (suppose x ≠ 0,
      sum.inr (by rewrite [-one_mul y, -(inv_mul_cancel this), mul.assoc, H, mul_zero]))

  @[hott, instance] def discrete_field.to_integral_domain : integral_domain A :=
  ⦃ integral_domain, s,
    eq_zero_sum_eq_zero_of_mul_eq_zero := discrete_field.eq_zero_sum_eq_zero_of_mul_eq_zero⦄

  @[hott] theorem inv_zero : 0⁻¹ = (0:A) := !discrete_field.inv_zero

  @[hott] theorem one_div_zero : 1 / 0 = (0:A) :=
    calc
      1 / 0 = 1 * 0⁻¹ : refl
        ... = 1 * 0   : inv_zero
        ... = 0 : mul_zero

  @[hott] theorem div_zero (a : A) : a / 0 = 0 := by rewrite [div_eq_mul_one_div, one_div_zero, mul_zero]

  @[hott] theorem ne_zero_of_one_div_ne_zero (H : 1 / a ≠ 0) : a ≠ 0 :=
    assume Ha : a = 0, absurd (Ha⁻¹ ▸ one_div_zero) H

  @[hott] theorem eq_zero_of_one_div_eq_zero (H : 1 / a = 0) : a = 0 :=
    decidable.by_cases
      (assume Ha, Ha)
      (assume Ha, empty.elim ((one_div_ne_zero Ha) H))

  variables (a b)
  @[hott] theorem one_div_mul_one_div' : (1 / a) * (1 / b) = 1 / (b * a) :=
    decidable.by_cases
      (suppose a = 0,
        by rewrite [this, div_zero, zero_mul, -(@div_zero A s 1), mul_zero b])
      (assume Ha : a ≠ 0,
        decidable.by_cases
          (suppose b = 0,
            by rewrite [this, div_zero, mul_zero, -(@div_zero A s 1), zero_mul a])
          (suppose b ≠ 0, division_ring.one_div_mul_one_div Ha this))

  @[hott] theorem one_div_neg_eq_neg_one_div : 1 / (- a) = - (1 / a) :=
    decidable.by_cases
      (suppose a = 0, by rewrite [this, neg_zero, 2 div_zero, neg_zero])
      (suppose a ≠ 0, division_ring.one_div_neg_eq_neg_one_div this)

  @[hott] theorem neg_div_neg_eq : (-a) / (-b) = a / b :=
    decidable.by_cases
      (assume Hb : b = 0, by rewrite [Hb, neg_zero, 2 div_zero])
      (assume Hb : b ≠ 0, !division_ring.neg_div_neg_eq Hb)

  @[hott] theorem one_div_one_div : 1 / (1 / a) = a :=
    decidable.by_cases
      (assume Ha : a = 0, by rewrite [Ha, 2 div_zero])
      (assume Ha : a ≠ 0, division_ring.one_div_one_div Ha)

  variables {a b}
  @[hott] theorem eq_of_one_div_eq_one_div (H : 1 / a = 1 / b) : a = b :=
    decidable.by_cases
      (assume Ha : a = 0,
      have Hb : b = 0, from eq_zero_of_one_div_eq_zero (by rewrite [-H, Ha, div_zero]),
      Hb⁻¹ ▸ Ha)
      (assume Ha : a ≠ 0,
      have Hb : b ≠ 0, from ne_zero_of_one_div_ne_zero (H ▸ (one_div_ne_zero Ha)),
      division_ring.eq_of_one_div_eq_one_div Ha Hb H)

  variables (a b)
  @[hott] theorem mul_inv' : (b * a)⁻¹ = a⁻¹ * b⁻¹ :=
    decidable.by_cases
      (assume Ha : a = 0, by rewrite [Ha, mul_zero, 2 inv_zero, zero_mul])
      (assume Ha : a ≠ 0,
        decidable.by_cases
          (assume Hb : b = 0, by rewrite [Hb, zero_mul, 2 inv_zero, mul_zero])
          (assume Hb : b ≠ 0, mul_inv_eq Ha Hb))

-- the following are specifically for fields
  @[hott] theorem one_div_mul_one_div : (1 / a) * (1 / b) =  1 / (a * b) :=
     by rewrite [one_div_mul_one_div', mul.comm b]

  variable {a}
  @[hott] theorem div_mul_right (Ha : a ≠ 0) : a / (a * b) = 1 / b :=
    decidable.by_cases
      (assume Hb : b = 0, by rewrite [Hb, mul_zero, 2 div_zero])
      (assume Hb : b ≠ 0, field.div_mul_right Hb (mul_ne_zero Ha Hb))

  variables (a) {b}
  @[hott] theorem div_mul_left (Hb : b ≠ 0) : b / (a * b) = 1 / a :=
    by rewrite [mul.comm a, div_mul_right _ Hb]

  variables (a b c)
  @[hott] theorem div_mul_div : (a / b) * (c / d) = (a * c) / (b * d) :=
    decidable.by_cases
      (assume Hb : b = 0, by rewrite [Hb, div_zero, zero_mul, -(@div_zero A s (a * c)), zero_mul])
      (assume Hb : b ≠ 0,
        decidable.by_cases
          (assume Hd : d = 0, by rewrite [Hd, div_zero, mul_zero, -(@div_zero A s (a * c)),
                                          mul_zero])
          (assume Hd : d ≠ 0, !field.div_mul_div Hb Hd))

  variable {c}
  @[hott] theorem mul_div_mul_left' (Hc : c ≠ 0) : (c * a) / (c * b) = a / b :=
    decidable.by_cases
      (assume Hb : b = 0, by rewrite [Hb, mul_zero, 2 div_zero])
      (assume Hb : b ≠ 0, !mul_div_mul_left Hb Hc)

  @[hott] theorem mul_div_mul_right' (Hc : c ≠ 0) : (a * c) / (b * c) = a / b :=
    by rewrite [(mul.comm a), (mul.comm b), (!mul_div_mul_left' Hc)]

  variables (a b c d)
  @[hott] theorem div_mul_eq_mul_div_comm : (b / c) * a = b * (a / c) :=
    decidable.by_cases
      (assume Hc : c = 0, by rewrite [Hc, div_zero, zero_mul, -(mul_zero b), -(@div_zero A s a)])
      (assume Hc : c ≠ 0, !field.div_mul_eq_mul_div_comm Hc)

  @[hott] theorem one_div_div : 1 / (a / b) = b / a :=
    decidable.by_cases
      (assume Ha : a = 0, by rewrite [Ha, zero_div, 2 div_zero])
      (assume Ha : a ≠ 0,
      decidable.by_cases
        (assume Hb : b = 0, by rewrite [Hb, 2 div_zero, zero_div])
        (assume Hb : b ≠ 0, field.one_div_div Ha Hb))

  @[hott] theorem div_div_eq_mul_div : a / (b / c) = (a * c) / b :=
    by rewrite [div_eq_mul_one_div, one_div_div, -mul_div_assoc]

  @[hott] theorem div_div_eq_div_mul : (a / b) / c = a / (b * c) :=
    by rewrite [div_eq_mul_one_div, div_mul_div, mul_one]

  @[hott] theorem div_div_div_div_eq : (a / b) / (c / d) = (a * d) / (b * c) :=
    by rewrite [div_div_eq_mul_div, div_mul_eq_mul_div, div_div_eq_div_mul]

  variable {a}
  @[hott] theorem div_helper (H : a ≠ 0) : (1 / (a * b)) * a = 1 / b :=
    by rewrite [div_mul_eq_mul_div, one_mul, !div_mul_right H]

  variable (a)
  @[hott] theorem div_mul_eq_div_mul_one_div : a / (b * c) = (a / b) * (1 / c) :=
    by rewrite [-div_div_eq_div_mul, -div_eq_mul_one_div]

end discrete_field

namespace norm_num

@[hott] theorem div_add_helper [s : field A] (n d b c val : A) (Hd : d ≠ 0) (H : n + b * d = val)
        (H2 : c * d = val) : n / d + b = c :=
  begin
    apply eq_of_mul_eq_mul_of_nonzero_right Hd,
    rewrite [H2, -H, right_distrib, div_mul_cancel _ Hd]
 end

@[hott] theorem add_div_helper [s : field A] (n d b c val : A) (Hd : d ≠ 0) (H : d * b + n = val)
        (H2 : d * c = val) : b + n / d = c :=
  begin
    apply eq_of_mul_eq_mul_of_nonzero_left Hd,
    rewrite [H2, -H, left_distrib, mul_div_cancel' Hd]
 end

@[hott] theorem div_mul_helper [s : field A] (n d c v : A) (Hd : d ≠ 0) (H : (n * c) / d = v) :
        (n / d) * c = v :=
  by rewrite [-H, field.div_mul_eq_mul_div_comm _ _ Hd, mul_div_assoc]

@[hott] theorem mul_div_helper [s : field A] (a n d v : A) (Hd : d ≠ 0) (H : (a * n) / d = v) :
        a * (n / d) = v :=
  by rewrite [-H, mul_div_assoc]

@[hott] theorem nonzero_of_div_helper [s : field A] (a b : A) (Ha : a ≠ 0) (Hb : b ≠ 0) : a / b ≠ 0 :=
  begin
    intro Hab,
    have Habb : (a / b) * b = 0, by rewrite [Hab, zero_mul],
    rewrite [div_mul_cancel _ Hb at Habb],
    exact Ha Habb
  end

@[hott] theorem div_helper [s : field A] (n d v : A) (Hd : d ≠ 0) (H : v * d = n) : n / d = v :=
  begin
    apply eq_of_mul_eq_mul_of_nonzero_right Hd,
    rewrite (div_mul_cancel _ Hd),
    exact inverse H
  end

@[hott] theorem div_eq_div_helper [s : field A] (a b c d v : A) (H1 : a * d = v) (H2 : c * b = v)
        (Hb : b ≠ 0) (Hd : d ≠ 0) : a / b = c / d :=
  begin
    apply eq_div_of_mul_eq,
    exact Hd,
    rewrite div_mul_eq_mul_div,
    apply inverse,
    apply eq_div_of_mul_eq,
    exact Hb,
    rewrite [H1, H2]
  end

@[hott] theorem subst_into_div [s : has_div A] (a₁ b₁ a₂ b₂ v : A) (H : a₁ / b₁ = v) (H1 : a₂ = a₁)
        (H2 : b₂ = b₁) : a₂ / b₂ = v :=
  by rewrite [H1, H2, H]

end norm_num
end algebra
end hott
