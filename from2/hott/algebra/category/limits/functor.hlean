/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Functor category has (co)limits if the codomain has them
-/

import .colimits

open functor nat_trans eq is_trunc

namespace category

  -- preservation of limits
  variables {D C I : Precategory}

  @[hott] def functor_limit_object
    [H : has_limits_of_shape D I] (F : I ⇒ D ^c C) : C ⇒ D :=
  begin
  have lem : Π(c d : carrier C) (f : hom c d) ⦃i j : carrier I⦄ (k : i ⟶ j),
    (constant2_functor F d) k ∘ to_fun_hom (F i) f ∘ limit_morphism (constant2_functor F c) i =
      to_fun_hom (F j) f ∘ limit_morphism (constant2_functor F c) j,
  begin intros c d f i j k, rewrite [-limit_commute _ k,▸*,+assoc,▸*,-naturality (F k) f] end,

  fapply functor.mk,
   { intro c, exact limit_object (constant2_functor F c)},
   { intros c d f, fapply hom_limit,
     { intro i, refine to_fun_hom (F i) f ∘ !limit_morphism},
     { apply lem}},
   { exact abstract begin intro c, symmetry, apply eq_hom_limit, intro i,
     rewrite [id_right,respect_id,▸*,id_left] end end},
   { intros a b c g f, symmetry, apply eq_hom_limit, intro i, -- report: adding abstract fails here
     rewrite [respect_comp,assoc,hom_limit_commute,-assoc,hom_limit_commute,assoc]}
  end

  @[hott] def functor_limit_cone
    [H : has_limits_of_shape D I] (F : I ⇒ D ^c C) : cone_obj F :=
  begin
  fapply cone_obj.mk,
  { exact functor_limit_object F},
  { fapply nat_trans.mk,
    { intro i, esimp, fapply nat_trans.mk,
      { intro c, esimp, apply limit_morphism},
      { intros c d f, rewrite [▸*,hom_limit_commute (constant2_functor F d)]}},
    { intros i j k, apply nat_trans_eq, intro c,
      rewrite [▸*,id_right,limit_commute (constant2_functor F c)]}}
  end

  variables (D C I)
  @[hott] def has_limits_of_shape_functor [instance] [H : has_limits_of_shape D I]
    : has_limits_of_shape (D ^c C) I :=
  begin
    intro F, fapply has_terminal_object.mk,
    { exact functor_limit_cone F},
    { intro c, esimp at *, induction c with G η, induction η with η p, esimp at *,
      fapply is_contr.mk,
      { fapply cone_hom.mk,
        { fapply nat_trans.mk,
          { intro c, esimp, fapply hom_limit,
            { intro i, esimp, exact η i c},
            { intros i j k, esimp, exact ap010 natural_map (p k) c ⬝ !id_right}},
          { intros c d f, esimp, fapply @limit_cone_unique,
            { intro i, esimp, exact to_fun_hom (F i) f ∘ η i c},
            { intros i j k, rewrite [▸*,assoc,-naturality,-assoc,-compose_def,p k,▸*,id_right]},
            { intro i, rewrite [assoc, hom_limit_commute (constant2_functor F d),▸*,-assoc,
                                hom_limit_commute]},
            { intro i, rewrite [assoc, hom_limit_commute (constant2_functor F d),naturality]}}},
        { intro i, apply nat_trans_eq, intro c,
          rewrite [▸*,hom_limit_commute (constant2_functor F c)]}},
      { intro h, induction h with f q, apply cone_hom_eq,
        apply nat_trans_eq, intro c, esimp at *, symmetry,
        apply eq_hom_limit, intro i, exact ap010 natural_map (q i) c}}
  end

  @[hott] def is_complete_functor [instance] [H : is_complete D] : is_complete (D ^c C) :=
  λI, _

  variables {D C I}
  -- preservation of colimits

  -- @[hott] def constant2_functor_op (F : I ⇒ (D ^c C)ᵒᵖ) (c : C) : I ⇒ D :=
  -- proof
  -- functor.mk (λi, to_fun_ob (F i) c)
  --            (λi j f, natural_map (F f) c)
  --            abstract (λi, ap010 natural_map !respect_id c ⬝ proof idp qed) end
  --            abstract (λi j k g f, ap010 natural_map !respect_comp c) end
  -- qed

  @[hott] def functor_colimit_object
    [H : has_colimits_of_shape D I] (F : Iᵒᵖ ⇒ (D ^c C)ᵒᵖ) : C ⇒ D :=
  begin
  fapply functor.mk,
   { intro c, exact colimit_object (constant2_functor Fᵒᵖ' c)},
   { intros c d f, apply colimit_hom_colimit, apply constant2_functor_natural _ f},
   { exact abstract begin intro c, symmetry, apply eq_colimit_hom, intro i,
     rewrite [id_left,▸*,respect_id,id_right] end end},
   { intros a b c g f, symmetry, apply eq_colimit_hom, intro i, -- report: adding abstract fails here
     rewrite [▸*,respect_comp,-assoc,colimit_hom_commute,assoc,colimit_hom_commute,-assoc]}
  end

  @[hott] def functor_colimit_cone
    [H : has_colimits_of_shape D I] (F : Iᵒᵖ ⇒ (D ^c C)ᵒᵖ) : cone_obj F :=
  begin
  fapply cone_obj.mk,
  { exact functor_colimit_object F},
  { fapply nat_trans.mk,
    { intro i, esimp, fapply nat_trans.mk,
      { intro c, esimp, apply colimit_morphism},
      { intros c d f, apply colimit_hom_commute (constant2_functor Fᵒᵖ' c)}},
    { intros i j k, apply nat_trans_eq, intro c,
      rewrite [▸*,id_left], apply colimit_commute (constant2_functor Fᵒᵖ' c)}}
  end

  variables (D C I)
  @[hott] def has_colimits_of_shape_functor [instance] [H : has_colimits_of_shape D I]
    : has_colimits_of_shape (D ^c C) I :=
  begin
    intro F, fapply has_terminal_object.mk,
    { exact functor_colimit_cone F},
    { intro c, esimp at *, induction c with G η, induction η with η p, esimp at *,
      fapply is_contr.mk,
      { fapply cone_hom.mk,
        { fapply nat_trans.mk,
          { intro c, esimp, fapply colimit_hom,
            { intro i, esimp, exact η i c},
            { intros i j k, esimp, exact ap010 natural_map (p k) c ⬝ !id_left}},
          { intros c d f, esimp, fapply @colimit_cocone_unique,
            { intro i, esimp, exact η i d ∘ to_fun_hom (F i) f},
            { intros i j k, rewrite [▸*,-assoc,naturality,assoc,-compose_def,p k,▸*,id_left]},
            { intro i, rewrite [-assoc, colimit_hom_commute (constant2_functor Fᵒᵖ' c),
                                ▸*, naturality]},
            { intro i, rewrite [-assoc, colimit_hom_commute (constant2_functor Fᵒᵖ' c),▸*,assoc,
                                colimit_hom_commute (constant2_functor Fᵒᵖ' d)]}}},
        { intro i, apply nat_trans_eq, intro c,
          rewrite [▸*,colimit_hom_commute (constant2_functor Fᵒᵖ' c)]}},
      { intro h, induction h with f q, apply cone_hom_eq,
        apply nat_trans_eq, intro c, esimp at *, symmetry,
        apply eq_colimit_hom, intro i, exact ap010 natural_map (q i) c}}
  end

  local attribute has_limits_of_shape_op_op [instance] [priority 1]
  universe variables u v
  @[hott] def is_cocomplete_functor [instance] [H : is_cocomplete.{_ _ u v} D]
    : is_cocomplete.{_ _ u v} (D ^c C) :=
  λI, _

end category
