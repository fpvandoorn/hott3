/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke, Favonia

Constructions with groups
-/

import algebra.group_theory hit.set_quotient types.list types.sum .subgroup .quotient_group

open eq algebra is_trunc set_quotient relation sigma prod prod.ops sum list trunc function
     equiv
namespace group

  variables {G G' : Group} {g g' h h' k : G}
            {A B : AbGroup}

  /- Binary products (direct product) of Groups -/
  @[hott] def product_one : G × G' := (one, one)
  @[hott] def product_inv : G × G' → G × G' :=
  λv, (v.1⁻¹, v.2⁻¹)
  @[hott] def product_mul : G × G' → G × G' → G × G' :=
  λv w, (v.1 * w.1, v.2 * w.2)

  section
  local notation 1 := product_one
  local postfix ⁻¹ := product_inv
  local infix * := product_mul

  @[hott] theorem product_mul_assoc (g₁ g₂ g₃ : G × G') : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  prod_eq !mul.assoc !mul.assoc

  @[hott] theorem product_one_mul (g : G × G') : 1 * g = g :=
  prod_eq !one_mul !one_mul

  @[hott] theorem product_mul_one (g : G × G') : g * 1 = g :=
  prod_eq !mul_one !mul_one

  @[hott] theorem product_mul_left_inv (g : G × G') : g⁻¹ * g = 1 :=
  prod_eq !mul.left_inv !mul.left_inv

  @[hott] theorem product_mul_comm {G G' : AbGroup} (g h : G × G') : g * h = h * g :=
  prod_eq !mul.comm !mul.comm

  end

  variables (G G')
  @[hott] def group_prod : group (G × G') :=
  group.mk _ product_mul product_mul_assoc product_one product_one_mul product_mul_one
           product_inv product_mul_left_inv

  @[hott] def product : Group :=
  Group.mk _ (group_prod G G')

  @[hott] def ab_group_prod (G G' : AbGroup) : ab_group (G × G') :=
  ⦃ab_group, group_prod G G', mul_comm := product_mul_comm⦄

  @[hott] def ab_product (G G' : AbGroup) : AbGroup :=
  AbGroup.mk _ (ab_group_prod G G')

  infix ` ×g `:60 := group.product
  infix ` ×ag `:60 := group.ab_product

  @[hott] def product_inl (G H : Group) : G →g G ×g H :=
    homomorphism.mk (λx, (x, one)) (λx y, prod_eq !refl !one_mul⁻¹)

  @[hott] def product_inr (G H : Group) : H →g G ×g H :=
    homomorphism.mk (λx, (one, x)) (λx y, prod_eq !one_mul⁻¹ !refl)

  @[hott] def Group_sum_elim {G H : Group} (I : AbGroup) (φ : G →g I) (ψ : H →g I) : G ×g H →g I :=
    homomorphism.mk (λx, φ x.1 * ψ x.2) abstract (λx y, calc
      φ (x.1 * y.1) * ψ (x.2 * y.2) = (φ x.1 * φ y.1) * (ψ x.2 * ψ y.2)
                                      : by exact ap011 mul (to_respect_mul φ x.1 y.1) (to_respect_mul ψ x.2 y.2)
                                ... = (φ x.1 * ψ x.2) * (φ y.1 * ψ y.2)
                                      : by exact interchange I (φ x.1) (φ y.1) (ψ x.2) (ψ y.2)) end

  @[hott] def product_functor {G G' H H' : Group} (φ : G →g H) (ψ : G' →g H') :
    G ×g G' →g H ×g H' :=
  homomorphism.mk (λx, (φ x.1, ψ x.2)) (λx y, prod_eq !to_respect_mul !to_respect_mul)

  infix ` ×→g `:60 := group.product_functor

  @[hott] def product_isomorphism {G G' H H' : Group} (φ : G ≃g H) (ψ : G' ≃g H') :
    G ×g G' ≃g H ×g H' :=
  isomorphism.mk (φ ×→g ψ) !is_equiv_prod_functor

  infix ` ×≃g `:60 := group.product_isomorphism

  @[hott] def product_group_mul_eq {G H : Group} (g h : G ×g H) : g * h = product_mul g h :=
  idp

end group
