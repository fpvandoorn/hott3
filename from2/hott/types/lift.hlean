/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about lift
-/

import ..function
open eq equiv is_equiv is_trunc pointed

namespace lift

  universe variables u v
  variables {A : Type u} (z z' : lift.{u v} A)

  @[hott] protected def eta : up (down z) = z :=
  by induction z; reflexivity

  @[hott] protected def code : lift A → lift A → Type _
  | code (up a) (up a') := a = a'

  @[hott] protected def decode : Π(z z' : lift A), lift.code z z' → z = z'
  | decode (up a) (up a') := λc, ap up c

  variables {z z'}
  @[hott] protected def encode (p : z = z') : lift.code z z' :=
  by induction p; induction z; esimp

  variables (z z')
  @[hott] def lift_eq_equiv : (z = z') ≃ lift.code z z' :=
  equiv.MK lift.encode
           !lift.decode
           abstract begin
             intro c, induction z with a, induction z' with a', esimp at *, induction c,
             reflexivity
           end end
           abstract begin
             intro p, induction p, induction z, reflexivity
           end end


  section
  variables {a a' : A}
  @[hott] def eq_of_up_eq_up (p : up a = up a') : a = a' :=
  lift.encode p

  @[hott] def lift_transport {P : A → Type _} (p : a = a') (z : lift (P a))
    : p ▸ z = up (p ▸ down z) :=
  by induction p; induction z; reflexivity
  end

  variables {A' : Type _} (f : A → A') (g : lift A → lift A')
  @[hott] def lift_functor : lift A → lift A'
  | lift_functor (up a) := up (f a)

  @[hott] def is_equiv_lift_functor [Hf : is_equiv f] : is_equiv (lift_functor f) :=
  adjointify (lift_functor f)
             (lift_functor f⁻¹)
             abstract begin
               intro z', induction z' with a',
               esimp, exact ap up !right_inv
             end end
             abstract begin
               intro z, induction z with a,
               esimp, exact ap up !left_inv
             end end

  @[hott] def lift_equiv_lift_of_is_equiv [Hf : is_equiv f] : lift A ≃ lift A' :=
  equiv.mk _ (is_equiv_lift_functor f)

  @[hott] def lift_equiv_lift (f : A ≃ A') : lift A ≃ lift A' :=
  equiv.mk _ (is_equiv_lift_functor f)

  @[hott] def lift_equiv_lift_refl (A : Type _) : lift_equiv_lift (erfl : A ≃ A) = erfl :=
  by apply equiv_eq; intro z; induction z with a; reflexivity

  @[hott] def lift_inv_functor (a : A) : A' :=
  down (g (up a))

  @[hott] def is_equiv_lift_inv_functor [Hf : is_equiv g]
    : is_equiv (lift_inv_functor g) :=
  adjointify (lift_inv_functor g)
             (lift_inv_functor g⁻¹)
             abstract begin
               intro z', rewrite [▸*,lift.eta,right_inv g],
             end end
             abstract begin
               intro z', rewrite [▸*,lift.eta,left_inv g],
             end end

  @[hott] def equiv_of_lift_equiv_lift (g : lift A ≃ lift A') : A ≃ A' :=
  equiv.mk _ (is_equiv_lift_inv_functor g)

  @[hott] def lift_functor_left_inv  : lift_inv_functor (lift_functor f) = f :=
  eq_of_homotopy (λa, idp)

  @[hott] def lift_functor_right_inv : lift_functor (lift_inv_functor g) = g :=
  begin
    apply eq_of_homotopy, intro z, induction z with a, esimp, apply lift.eta
  end

  variables (A A')
  @[hott] def is_equiv_lift_functor_fn
    : is_equiv (lift_functor : (A → A') → (lift A → lift A')) :=
  adjointify lift_functor
             lift_inv_functor
             lift_functor_right_inv
             lift_functor_left_inv

  @[hott] def lift_imp_lift_equiv : (lift A → lift A') ≃ (A → A') :=
  (equiv.mk _ (is_equiv_lift_functor_fn A A'))⁻¹ᵉ

  -- can we deduce this from lift_imp_lift_equiv?
  @[hott] def lift_equiv_lift_equiv : (lift A ≃ lift A') ≃ (A ≃ A') :=
  equiv.MK equiv_of_lift_equiv_lift
           lift_equiv_lift
           abstract begin
             intro f, apply equiv_eq, reflexivity
           end end
           abstract begin
             intro g, apply equiv_eq', esimp, apply eq_of_homotopy, intro z,
             induction z with a, esimp, apply lift.eta
           end end

  @[hott] def lift_eq_lift_equiv.{u1 u2} (A A' : Type u1)
    : (lift.{u1 u2} A = lift.{u1 u2} A') ≃ (A = A') :=
  !eq_equiv_equiv ⬝e !lift_equiv_lift_equiv ⬝e !eq_equiv_equiv⁻¹ᵉ

  @[hott] def is_embedding_lift [instance] : is_embedding lift :=
  begin
    intros A A', fapply is_equiv.homotopy_closed,
      exact to_inv !lift_eq_lift_equiv,
      exact _,
    { intro p, induction p,
      esimp [lift_eq_lift_equiv,equiv.trans,equiv.symm,eq_equiv_equiv],
      rewrite [equiv_of_eq_refl, lift_equiv_lift_refl],
      apply ua_refl}
  end

  @[hott] def plift (A : pType.{u}) : pType.{max u v} :=
  pointed.MK (lift A) (up pt)

  @[hott] def plift_functor {A B : Type*} (f : A →* B) : plift A →* plift B :=
  pmap.mk (lift_functor f) (ap up (respect_pt f))

  -- is_trunc_lift is defined in init.trunc

  @[hott] def pup {A : Type*} : A →* plift A :=
  pmap.mk up idp

  @[hott] def pdown {A : Type*} : plift A →* A :=
  pmap.mk down idp

  @[hott] def plift_functor_phomotopy {A B : Type*} (f : A →* B)
    : pdown ∘* plift_functor f ∘* pup ~* f :=
  begin
    fapply phomotopy.mk,
    { reflexivity},
    { esimp, refine !idp_con ⬝ _, refine _ ⬝ ap02 down !idp_con⁻¹,
      refine _ ⬝ !ap_compose, exact !ap_id⁻¹}
  end

  @[hott] def pequiv_plift (A : Type*) : A ≃* plift A :=
  pequiv_of_equiv (equiv_lift A) idp

  @[hott] def fiber_lift_functor {A B : Type _} (f : A → B) (b : B) :
    fiber (lift_functor f) (up b) ≃ fiber f b :=
  begin
    fapply equiv.MK: intro v; cases v with a p,
    { cases a with a, exact fiber.mk a (eq_of_fn_eq_fn' up p) },
    { exact fiber.mk (up a) (ap up p) },
    { apply ap (fiber.mk a), apply eq_of_fn_eq_fn'_ap },
    { cases a with a, esimp, apply ap (fiber.mk (up a)), apply ap_eq_of_fn_eq_fn' }
  end


end lift
