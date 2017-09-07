/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Discrete category
-/

import ..groupoid types.bool ..nat_trans

open eq is_trunc iso bool functor nat_trans

namespace category

  @[hott] def precategory_of_1_type (A : Type _) [H : is_trunc 1 A] : precategory A :=
  @precategory.mk _ _ (@is_trunc_eq _ _ H)
    (λ (a b c : A) (p : b = c) (q : a = b), q ⬝ p)
    (λ (a : A), refl a)
    (λ (a b c d : A) (p : c = d) (q : b = c) (r : a = b), con.assoc r q p)
    (λ (a b : A) (p : a = b), con_idp p)
    (λ (a b : A) (p : a = b), idp_con p)

  @[hott] def groupoid_of_1_type (A : Type _) [H : is_trunc 1 A] : groupoid A :=
  groupoid.mk !precategory_of_1_type
              (λ (a b : A) (p : a = b), is_iso.mk _ !con.right_inv !con.left_inv)

  @[hott] def Precategory_of_1_type (A : Type _) [H : is_trunc 1 A] : Precategory :=
  precategory.Mk (precategory_of_1_type A)

  @[hott] def Groupoid_of_1_type (A : Type _) [H : is_trunc 1 A] : Groupoid :=
  groupoid.Mk _ (groupoid_of_1_type A)

  @[hott] def discrete_precategory (A : Type _) [H : is_set A] : precategory A :=
  precategory_of_1_type A

  @[hott] def discrete_groupoid (A : Type _) [H : is_set A] : groupoid A :=
  groupoid_of_1_type A

  @[hott] def Discrete_precategory (A : Type _) [H : is_set A] : Precategory :=
  precategory.Mk (discrete_precategory A)

  @[hott] def Discrete_groupoid (A : Type _) [H : is_set A] : Groupoid :=
  groupoid.Mk _ (discrete_groupoid A)

  @[hott] def c2 : Precategory := Discrete_precategory bool

  @[hott] def c2_functor (C : Precategory) (x y : C) : c2 ⇒ C :=
  functor.mk (bool.rec x y)
             (bool.rec (bool.rec (λf, id) (by contradiction))
                       (bool.rec (by contradiction) (λf, id)))
             abstract (bool.rec idp idp) end
             abstract begin intros b₁ b₂ b₃ g f, induction b₁: induction b₂: induction b₃:
                            esimp at *: try contradiction: exact !id_id⁻¹ end end

  @[hott] def c2_functor_eta {C : Precategory} (F : c2 ⇒ C) :
    c2_functor C (to_fun_ob F ff) (to_fun_ob F tt) = F :=
  begin
  fapply functor_eq: esimp,
  { intro b, induction b: reflexivity},
  { intros b₁ b₂ p, induction p, induction b₁: esimp; rewrite [id_leftright]; exact !respect_id⁻¹}
  end

  @[hott] def c2_nat_trans {C : Precategory} {x y u v : C} (f : x ⟶ u) (g : y ⟶ v) :
    c2_functor C x y ⟹ c2_functor C u v :=
  begin
  fapply nat_trans.mk: esimp,
  { intro b, induction b, exact f, exact g},
  { intros b₁ b₂ p, induction p, induction b₁: esimp: apply id_comp_eq_comp_id},
  end

end category
