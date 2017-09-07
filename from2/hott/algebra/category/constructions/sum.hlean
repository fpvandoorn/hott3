/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Sum precategory and (TODO) category
-/

import ..category ..nat_trans types.sum

open eq sum is_trunc functor lift nat_trans

namespace category

  --set_option pp.universes true
  @[hott] def sum_hom.{u v w x} {obC : Type u} {obD : Type v}
    (C : precategory.{u w} obC) (D : precategory.{v x} obD)
    : obC + obD → obC + obD → Type max w x :=
  sum.rec (λc, sum.rec (λc', lift (c ⟶ c')) (λd, lift empty))
          (λd, sum.rec (λc, lift empty) (λd', lift (d ⟶ d')))

  @[hott] theorem is_set_sum_hom {obC : Type _} {obD : Type _}
    (C : precategory obC) (D : precategory obD) (x y : obC + obD)
    : is_set (sum_hom C D x y) :=
  by induction x: induction y: esimp at *: exact _

  local attribute is_set_sum_hom [instance]

  @[hott] def precategory_sum [instance] (obC obD : Type _)
    [C : precategory obC] [D : precategory obD] : precategory (obC + obD) :=
  precategory.mk (sum_hom C D)
                  (λ a b c g f, begin induction a: induction b: induction c: esimp at *;
                    induction f with f; induction g with g; (contradiction | exact up (g ∘ f)) end)
                  (λ a, by induction a: exact up id)
                  (λ a b c d h g f,
                    abstract begin induction a: induction b: induction c: induction d:
                    esimp at *; induction f with f; induction g with g; induction h with h;
                    esimp at *; try contradiction: apply ap up !assoc end end)
                  (λ a b f, abstract begin induction a: induction b: esimp at *;
                    induction f with f; esimp; try contradiction: exact ap up !id_left end end)
                  (λ a b f, abstract begin induction a: induction b: esimp at *;
                    induction f with f; esimp; try contradiction: exact ap up !id_right end end)

  @[hott] def Precategory_sum (C D : Precategory) : Precategory :=
  precategory.Mk (precategory_sum C D)

  infixr ` +c `:65 := Precategory_sum
  variables {C C' D D' : Precategory}

  @[hott] def inl_functor : C ⇒ C +c D :=
  functor.mk inl
             (λa b, up)
             (λa, idp)
             (λa b c g f, idp)

  @[hott] def inr_functor : D ⇒ C +c D :=
  functor.mk inr
             (λa b, up)
             (λa, idp)
             (λa b c g f, idp)

  @[hott] def sum_functor (F : C ⇒ D) (G : C' ⇒ D) : C +c C' ⇒ D :=
  begin
    fapply functor.mk: esimp,
    { intro a, induction a, exact F a, exact G a},
    { intros a b f, induction a: induction b: esimp at *;
     induction f with f; esimp; try contradiction: (exact F f|exact G f)},
    { exact abstract begin intro a, induction a: esimp; apply respect_id end end},
    { intros a b c g f, induction a: induction b: induction c: esimp at *;
                induction f with f; induction g with g; try contradiction:
                esimp; apply respect_comp}, -- REPORT: abstracting this argument fails
  end

  infixr ` +f `:65 := sum_functor

  @[hott] def sum_functor_eta (F : C +c C' ⇒ D) : F ∘f inl_functor +f F ∘f inr_functor = F :=
  begin
  fapply functor_eq: esimp,
  { intro a, induction a: reflexivity},
  { exact abstract begin esimp, intros a b f,
    induction a: induction b: esimp at *; induction f with f; esimp;
    try contradiction: apply id_leftright end end}
  end

  @[hott] def sum_functor_inl (F : C ⇒ D) (G : C' ⇒ D) : (F +f G) ∘f inl_functor = F :=
  begin
  fapply functor_eq,
    reflexivity,
    esimp, intros, apply id_leftright
  end

  @[hott] def sum_functor_inr (F : C ⇒ D) (G : C' ⇒ D) : (F +f G) ∘f inr_functor = G :=
  begin
  fapply functor_eq,
    reflexivity,
    esimp, intros, apply id_leftright
  end

  @[hott] def sum_functor_sum (F : C ⇒ D) (G : C' ⇒ D') : C +c C' ⇒ D +c D' :=
  (inl_functor ∘f F) +f (inr_functor ∘f G)

  @[hott] def sum_nat_trans {F F' : C ⇒ D} {G G' : C' ⇒ D} (η : F ⟹ F') (θ : G ⟹ G')
    : F +f G ⟹ F' +f G' :=
  begin
    fapply nat_trans.mk,
    { intro a, induction a: esimp, exact η a, exact θ a},
    { intros a b f, induction a: induction b: esimp at *; induction f with f; esimp;
      try contradiction: apply naturality}
  end
  infixr ` +n `:65 := sum_nat_trans

end category
