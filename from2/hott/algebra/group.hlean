/-
Copyright (c) 2014 Jeremy Avigad. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jeremy Avigad, Leonardo de Moura

Various multiplicative and additive structures. Partially modeled on Isabelle's library.
-/

import algebra.inf_group

open eq eq.ops   -- note: ⁻¹ will be overloaded
open binary algebra is_trunc
set_option class.force_new true

variable {A : Type _}

/- semigroup -/

namespace algebra

structure is_set_structure [class] (A : Type _) :=
  (is_set_carrier : is_set A)

attribute is_set_structure.is_set_carrier [instance] [priority 950]

structure semigroup [class] (A : Type _) extends is_set_structure A, inf_semigroup A

structure comm_semigroup [class] (A : Type _) extends semigroup A, comm_inf_semigroup A

structure left_cancel_semigroup [class] (A : Type _) extends semigroup A, left_cancel_inf_semigroup A

structure right_cancel_semigroup [class] (A : Type _) extends semigroup A, right_cancel_inf_semigroup A

/- additive semigroup -/

@[hott] def add_semigroup [class] : Type _ → Type _ := semigroup

@[hott] def add_semigroup.is_set_carrier [instance] [priority 900] (A : Type _) [H : add_semigroup A] :
  is_set A :=
@is_set_structure.is_set_carrier A (@semigroup.to_is_set_structure A H)

@[hott] def add_inf_semigroup_of_add_semigroup [reducible] [trans_instance] (A : Type _)
  [H : add_semigroup A] : add_inf_semigroup A :=
@semigroup.to_inf_semigroup A H

@[hott] def add_comm_semigroup [class] : Type _ → Type _ := comm_semigroup

@[hott] def add_semigroup_of_add_comm_semigroup [reducible] [trans_instance] (A : Type _)
  [H : add_comm_semigroup A] : add_semigroup A :=
@comm_semigroup.to_semigroup A H

@[hott] def add_comm_inf_semigroup_of_add_comm_semigroup [reducible] [trans_instance] (A : Type _)
  [H : add_comm_semigroup A] : add_comm_inf_semigroup A :=
@comm_semigroup.to_comm_inf_semigroup A H

@[hott] def add_left_cancel_semigroup [class] : Type _ → Type _ := left_cancel_semigroup

@[hott] def add_semigroup_of_add_left_cancel_semigroup [reducible] [trans_instance] (A : Type _)
  [H : add_left_cancel_semigroup A] : add_semigroup A :=
@left_cancel_semigroup.to_semigroup A H

@[hott] def add_left_cancel_inf_semigroup_of_add_left_cancel_semigroup [reducible] [trans_instance]
  (A : Type _) [H : add_left_cancel_semigroup A] : add_left_cancel_inf_semigroup A :=
@left_cancel_semigroup.to_left_cancel_inf_semigroup A H

@[hott] def add_right_cancel_semigroup [class] : Type _ → Type _ := right_cancel_semigroup

@[hott] def add_semigroup_of_add_right_cancel_semigroup [reducible] [trans_instance] (A : Type _)
  [H : add_right_cancel_semigroup A] : add_semigroup A :=
@right_cancel_semigroup.to_semigroup A H

@[hott] def add_right_cancel_inf_semigroup_of_add_right_cancel_semigroup [reducible] [trans_instance]
  (A : Type _) [H : add_right_cancel_semigroup A] : add_right_cancel_inf_semigroup A :=
@right_cancel_semigroup.to_right_cancel_inf_semigroup A H

/- monoid -/

structure monoid [class] (A : Type _) extends semigroup A, inf_monoid A

structure comm_monoid [class] (A : Type _) extends monoid A, comm_semigroup A, comm_inf_monoid A

/- additive monoid -/

@[hott] def add_monoid [class] : Type _ → Type _ := monoid

@[hott] def add_semigroup_of_add_monoid [reducible] [trans_instance] (A : Type _)
  [H : add_monoid A] : add_semigroup A :=
@monoid.to_semigroup A H

@[hott] def add_inf_monoid_of_add_monoid [reducible] [trans_instance] (A : Type _)
  [H : add_monoid A] : add_inf_monoid A :=
@monoid.to_inf_monoid A H

@[hott] def add_comm_monoid [class] : Type _ → Type _ := comm_monoid

@[hott] def add_monoid_of_add_comm_monoid [reducible] [trans_instance] (A : Type _)
  [H : add_comm_monoid A] : add_monoid A :=
@comm_monoid.to_monoid A H

@[hott] def add_comm_semigroup_of_add_comm_monoid [reducible] [trans_instance] (A : Type _)
  [H : add_comm_monoid A] : add_comm_semigroup A :=
@comm_monoid.to_comm_semigroup A H

@[hott] def add_comm_inf_monoid_of_add_comm_monoid [reducible] [trans_instance] (A : Type _)
  [H : add_comm_monoid A] : add_comm_inf_monoid A :=
@comm_monoid.to_comm_inf_monoid A H

@[hott] def add_monoid.to_monoid {A : Type _} [s : add_monoid A] : monoid A := s
@[hott] def add_comm_monoid.to_comm_monoid {A : Type _} [s : add_comm_monoid A] : comm_monoid A := s
@[hott] def monoid.to_add_monoid {A : Type _} [s : monoid A] : add_monoid A := s
@[hott] def comm_monoid.to_add_comm_monoid {A : Type _} [s : comm_monoid A] : add_comm_monoid A := s

/- group -/

structure group [class] (A : Type _) extends monoid A, inf_group A

@[hott] def group_of_inf_group (A : Type _) [s : inf_group A] [is_set A] : group A :=
⦃group, s, is_set_carrier := _⦄

section group

  variable [s : group A]
  include s

  @[hott] def group.to_left_cancel_semigroup [trans_instance] : left_cancel_semigroup A :=
  ⦃ left_cancel_semigroup, s,
    mul_left_cancel := @mul_left_cancel A _ ⦄

  @[hott] def group.to_right_cancel_semigroup [trans_instance] : right_cancel_semigroup A :=
  ⦃ right_cancel_semigroup, s,
    mul_right_cancel := @mul_right_cancel A _ ⦄

end group

structure ab_group [class] (A : Type _) extends group A, comm_monoid A, ab_inf_group A

@[hott] def ab_group_of_ab_inf_group (A : Type _) [s : ab_inf_group A] [is_set A] : ab_group A :=
⦃ab_group, s, is_set_carrier := _⦄

/- additive group -/

@[hott] def add_group [class] : Type _ → Type _ := group

@[hott] def add_semigroup_of_add_group [reducible] [trans_instance] (A : Type _)
  [H : add_group A] : add_monoid A :=
@group.to_monoid A H

@[hott] def add_inf_group_of_add_group [reducible] [trans_instance] (A : Type _)
  [H : add_group A] : add_inf_group A :=
@group.to_inf_group A H

@[hott] def add_group.to_group {A : Type _} [s : add_group A] : group A := s
@[hott] def group.to_add_group {A : Type _} [s : group A] : add_group A := s

@[hott] def add_group_of_add_inf_group (A : Type _) [s : add_inf_group A] [is_set A] :
  add_group A :=
⦃group, s, is_set_carrier := _⦄

section add_group

  variables [s : add_group A]
  include s

  @[hott] def add_group.to_add_left_cancel_semigroup [reducible] [trans_instance] :
    add_left_cancel_semigroup A :=
  @group.to_left_cancel_semigroup A s

  @[hott] def add_group.to_add_right_cancel_semigroup [reducible] [trans_instance] :
    add_right_cancel_semigroup A :=
  @group.to_right_cancel_semigroup A s

end add_group

@[hott] def add_ab_group [class] : Type _ → Type _ := ab_group

@[hott] def add_group_of_add_ab_group [reducible] [trans_instance] (A : Type _)
  [H : add_ab_group A] : add_group A :=
@ab_group.to_group A H

@[hott] def add_comm_monoid_of_add_ab_group [reducible] [trans_instance] (A : Type _)
  [H : add_ab_group A] : add_comm_monoid A :=
@ab_group.to_comm_monoid A H

@[hott] def add_ab_inf_group_of_add_ab_group [reducible] [trans_instance] (A : Type _)
  [H : add_ab_group A] : add_ab_inf_group A :=
@ab_group.to_ab_inf_group A H

@[hott] def add_ab_group.to_ab_group {A : Type _} [s : add_ab_group A] : ab_group A := s
@[hott] def ab_group.to_add_ab_group {A : Type _} [s : ab_group A] : add_ab_group A := s

@[hott] def add_ab_group_of_add_ab_inf_group (A : Type _) [s : add_ab_inf_group A] [is_set A] :
  add_ab_group A :=
⦃ab_group, s, is_set_carrier := _⦄

@[hott] def group_of_add_group (A : Type _) [G : add_group A] : group A :=
⦃group,
  mul             := has_add.add,
  mul_assoc       := add.assoc,
  one             := !has_zero.zero,
  one_mul         := zero_add,
  mul_one         := add_zero,
  inv             := has_neg.neg,
  mul_left_inv    := add.left_inv,
  is_set_carrier := _⦄

end algebra
open algebra
