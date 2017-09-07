/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Category of sets
-/

import ..functor.basic ..category types.equiv types.lift

open eq category equiv iso is_equiv is_trunc function sigma

namespace category

  @[hott] def precategory_Set.{u} [reducible] : precategory Set.{u} :=
  precategory.mk (λx y : Set, x → y)
                 (λx y z g f a, g (f a))
                 (λx a, a)
                 (λx y z w h g f, eq_of_homotopy (λa, idp))
                 (λx y f, eq_of_homotopy (λa, idp))
                 (λx y f, eq_of_homotopy (λa, idp))

  @[hott] def Precategory_Set [reducible] : Precategory :=
  Precategory.mk Set precategory_Set

  abbreviation set := Precategory_Set

  namespace set
    local attribute is_equiv_subtype_eq [instance]
    @[hott] def iso_of_equiv {A B : set} (f : A ≃ B) : A ≅ B :=
    iso.MK (to_fun f)
           (to_inv f)
           (eq_of_homotopy (left_inv (to_fun f)))
           (eq_of_homotopy (right_inv (to_fun f)))

    @[hott] def equiv_of_iso {A B : set} (f : A ≅ B) : A ≃ B :=
    begin
      apply equiv.MK (to_hom f) (iso.to_inv f),
        exact ap10 (to_right_inverse f),
        exact ap10 (to_left_inverse f)
    end

    @[hott] def is_equiv_iso_of_equiv (A B : set)
      : is_equiv (@iso_of_equiv A B) :=
    adjointify _ (λf, equiv_of_iso f)
                 (λf, proof iso_eq idp qed)
                 (λf, equiv_eq' idp)

    local attribute is_equiv_iso_of_equiv [instance]

    @[hott] def iso_of_eq_eq_compose (A B : Set) : @iso_of_eq _ _ A B ~
      @iso_of_equiv A B ∘ @equiv_of_eq A B ∘ subtype_eq_inv _ _ ∘
      @ap _ _ (to_fun (trunctype.sigma_char 0)) A B :=
    λp, eq.rec_on p idp

    @[hott] def equiv_equiv_iso (A B : set) : (A ≃ B) ≃ (A ≅ B) :=
    equiv.MK (λf, iso_of_equiv f)
             (λf, proof equiv.MK (to_hom f)
                           (iso.to_inv f)
                           (ap10 (to_right_inverse f))
                           (ap10 (to_left_inverse  f)) qed)
             (λf, proof iso_eq idp qed)
             (λf, proof equiv_eq' idp qed)

    @[hott] def equiv_eq_iso (A B : set) : (A ≃ B) = (A ≅ B) :=
    ua !equiv_equiv_iso

    @[hott] def is_univalent_Set (A B : set) : is_equiv (iso_of_eq : A = B → A ≅ B) :=
    have H₁ : is_equiv (@iso_of_equiv A B ∘ @equiv_of_eq A B ∘ subtype_eq_inv _ _ ∘
              @ap _ _ (to_fun (trunctype.sigma_char 0)) A B), from
      @is_equiv_compose _ _ _ _ _
      (@is_equiv_compose _ _ _ _ _
         (@is_equiv_compose _ _ _ _ _
           _
           (@is_equiv_subtype_eq_inv _ _ _ _ _))
         !univalence)
       !is_equiv_iso_of_equiv,
    is_equiv.homotopy_closed _ (iso_of_eq_eq_compose A B)⁻¹ʰᵗʸ

  end set

  @[hott] def category_Set [instance] : category Set :=
  category.mk precategory_Set set.is_univalent_Set

  @[hott] def Category_Set [reducible] : Category :=
  Category.mk Set category_Set

  abbreviation cset := Category_Set

  open functor lift
  @[hott] def functor_lift.{u v} : set.{u} ⇒ set.{max u v} :=
  functor.mk tlift
             (λa b, lift_functor)
             (λa, eq_of_homotopy (λx, by induction x; reflexivity))
             (λa b c g f, eq_of_homotopy (λx, by induction x; reflexivity))


end category
