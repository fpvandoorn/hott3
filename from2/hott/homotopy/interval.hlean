/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the interval
-/

import .susp types.eq types.prod cubical.square
open eq susp unit equiv is_trunc nat prod pointed

@[hott] def interval : Type := susp unit

namespace interval

  @[hott] def zero : interval := north
  @[hott] def one  : interval := south
  @[hott] def seg  : zero = one := merid star

  @[hott] protected def rec {P : interval → Type _} (P0 : P zero) (P1 : P one)
    (Ps : P0 =[seg] P1) (x : interval) : P x :=
  begin
    fapply susp.rec_on x,
    { exact P0},
    { exact P1},
    { intro x, cases x, exact Ps}
  end

  @[hott] protected def rec_on [reducible] {P : interval → Type _} (x : interval)
    (P0 : P zero) (P1 : P one) (Ps : P0 =[seg] P1) : P x :=
  interval.rec P0 P1 Ps x

  @[hott] theorem rec_seg {P : interval → Type _} (P0 : P zero) (P1 : P one) (Ps : P0 =[seg] P1)
      : apd (interval.rec P0 P1 Ps) seg = Ps :=
  !rec_merid

  @[hott] protected def elim {P : Type _} (P0 P1 : P) (Ps : P0 = P1) (x : interval) : P :=
  interval.rec P0 P1 (pathover_of_eq _ Ps) x

  @[hott] protected def elim_on [reducible] {P : Type _} (x : interval) (P0 P1 : P)
    (Ps : P0 = P1) : P :=
  interval.elim P0 P1 Ps x

  @[hott] theorem elim_seg {P : Type _} (P0 P1 : P) (Ps : P0 = P1)
    : ap (interval.elim P0 P1 Ps) seg = Ps :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant seg),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑interval.elim,rec_seg],
  end

  @[hott] protected def elim_type (P0 P1 : Type _) (Ps : P0 ≃ P1) (x : interval) : Type _ :=
  interval.elim P0 P1 (ua Ps) x

  @[hott] protected def elim_type_on [reducible] (x : interval) (P0 P1 : Type _) (Ps : P0 ≃ P1)
    : Type _ :=
  interval.elim_type P0 P1 Ps x

  @[hott] theorem elim_type_seg (P0 P1 : Type _) (Ps : P0 ≃ P1)
    : transport (interval.elim_type P0 P1 Ps) seg = Ps :=
  by rewrite [tr_eq_cast_ap_fn,↑interval.elim_type,elim_seg];apply cast_ua_fn

  @[hott] def is_contr_interval [instance] [priority 900] : is_contr interval :=
  is_contr.mk zero (λx, interval.rec_on x idp seg !eq_pathover_r_idp)

  @[hott] def naive_funext_of_interval : naive_funext :=
  λA P f g p, ap (λ(i : interval) (x : A), interval.elim_on i (f x) (g x) (p x)) seg

  @[hott] def funext_of_interval : funext :=
  funext_from_naive_funext naive_funext_of_interval

end interval open interval

@[hott] def cube : ℕ → Type
| cube 0        := unit
| cube (succ n) := cube n × interval

abbreviation square := cube (succ (succ nat.zero))

@[hott] def cube_one_equiv_interval : cube 1 ≃ interval :=
!prod_comm_equiv ⬝e !prod_unit_equiv


@[hott] def prod_square {A B : Type _} {a a' : A} {b b' : B} (p : a = a') (q : b = b')
  : square (pair_eq p idp) (pair_eq p idp) (pair_eq idp q) (pair_eq idp q) :=
by cases p; cases q; exact ids

namespace square

  @[hott] def tl : square := (star, zero, zero)
  @[hott] def tr : square := (star, one,  zero)
  @[hott] def bl : square := (star, zero, one )
  @[hott] def br : square := (star, one,  one )
  -- s stands for "square" in the following definitions
  @[hott] def st : tl = tr := pair_eq (pair_eq idp seg) idp
  @[hott] def sb : bl = br := pair_eq (pair_eq idp seg) idp
  @[hott] def sl : tl = bl := pair_eq idp seg
  @[hott] def sr : tr = br := pair_eq idp seg
  @[hott] def sfill : square st sb sl sr := !prod_square
  @[hott] def fill : st ⬝ sr = sl ⬝ sb := !square_equiv_eq sfill

end square
