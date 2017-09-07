/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

colimit_functor ⊣ Δ ⊣ limit_functor
-/

import .colimits ..functor.adjoint

open eq functor category is_trunc prod nat_trans

namespace category

  @[hott] def limit_functor_adjoint (D I : Precategory) [H : has_limits_of_shape D I] :
    constant_diagram D I ⊣ limit_functor D I :=
  adjoint.mk'
  begin
    fapply natural_iso.MK,
    { intros dF η, induction dF with d F, esimp at *,
      fapply hom_limit,
      { exact natural_map η},
      { intros i j f, exact !naturality ⬝ !id_right}},
    { esimp, intros dF dF' fθ, induction dF with d F, induction dF' with d' F',
      induction fθ with f θ, esimp at *, apply eq_of_homotopy, intro η,
      apply eq_hom_limit, intro i,
      rewrite [assoc, limit_hom_limit_commute,
              -assoc, assoc (limit_morphism F i), hom_limit_commute]},
    { esimp, intros dF f, induction dF with d F, esimp at *,
      refine !limit_nat_trans ∘n constant_nat_trans I f},
    { esimp, intro dF, induction dF with d F, esimp, apply eq_of_homotopy, intro η,
      apply nat_trans_eq, intro i, esimp, apply hom_limit_commute},
    { esimp, intro dF, induction dF with d F, esimp, apply eq_of_homotopy, intro f,
      symmetry, apply eq_hom_limit, intro i, reflexivity}
  end

/-
  @[hott] def adjoint_colimit_functor (D I : Precategory)
    [H : has_colimits_of_shape D I] : colimit_functor D I ⊣ constant_diagram D I :=
  have H : colimit_functor D I ⊣ (constant_diagram Dᵒᵖ Iᵒᵖ)ᵒᵖ', from _,
  _
-/

end category
