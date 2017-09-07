/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Theorems about the universe
-/

-- see also init.ua

import .bool .trunc .lift .pullback

open is_trunc bool lift unit eq pi equiv sum sigma fiber prod pullback is_equiv sigma.ops
     pointed
namespace univ

  universe variables u v
  variables {A B : Type u} {a : A} {b : B}

  /- Pathovers -/

  @[hott] def eq_of_pathover_ua {f : A ≃ B} (p : a =[ua f] b) : f a = b :=
  !cast_ua⁻¹ ⬝ tr_eq_of_pathover p

  @[hott] def pathover_ua {f : A ≃ B} (p : f a = b) : a =[ua f] b :=
  pathover_of_tr_eq (!cast_ua ⬝ p)

  @[hott] def pathover_ua_equiv (f : A ≃ B) : (a =[ua f] b) ≃ (f a = b) :=
  equiv.MK eq_of_pathover_ua
           pathover_ua
           abstract begin
             intro p, unfold [pathover_ua,eq_of_pathover_ua],
             rewrite [to_right_inv !pathover_equiv_tr_eq, inv_con_cancel_left]
           end end
           abstract begin
             intro p, unfold [pathover_ua,eq_of_pathover_ua],
             rewrite [con_inv_cancel_left, to_left_inv !pathover_equiv_tr_eq]
           end end

  /- Properties which can be disproven for the universe -/

  @[hott] def not_is_set_type0 : ¬is_set Type :=
  assume H : is_set Type,
  absurd !is_set.elim eq_bnot_ne_idp

  @[hott] def not_is_set_type : ¬is_set Type u :=
  assume H : is_set Type _,
  absurd (is_trunc_is_embedding_closed lift !trunc_index.minus_one_le_succ) not_is_set_type0

  @[hott] def not_double_negation_elimination0 : ¬Π(A : Type), ¬¬A → A :=
  begin
    intro f,
    have u : ¬¬bool, by exact (λg, g tt),
    let H1 := apd f eq_bnot,
    note H2 := apo10 H1 u,
    have p : eq_bnot ▸ u = u, from !is_prop.elim,
    rewrite p at H2,
    note H3 := eq_of_pathover_ua H2, esimp at H3, --TODO: use apply ... at after #700
    exact absurd H3 (bnot_ne (f bool u)),
  end

  @[hott] def not_double_negation_elimination : ¬Π(A : Type _), ¬¬A → A :=
  begin
    intro f,
    apply not_double_negation_elimination0,
    intros A nna, refine down (f _ _),
    intro na,
    have ¬A, begin intro a, exact absurd (up a) na end,
    exact absurd this nna
  end

  @[hott] def not_excluded_middle : ¬Π(A : Type _), A + ¬A :=
  begin
    intro f,
    apply not_double_negation_elimination,
    intros A nna,
    induction (f A) with a na,
      exact a,
      exact absurd na nna
  end

  @[hott] def characteristic_map {B : Type u} (p : Σ(A : Type max u v), A → B)
    (b : B) : Type max u v :=
  by induction p with A f; exact fiber f b

  @[hott] def characteristic_map_inv {B : Type u} (P : B → Type max u v) :
    Σ(A : Type max u v), A → B :=
  ⟨(Σb, P b), pr1⟩

  @[hott] def sigma_arrow_equiv_arrow_univ (B : Type u) :
    (Σ(A : Type max u v), A → B) ≃ (B → Type max u v) :=
  begin
    fapply equiv.MK,
    { exact characteristic_map},
    { exact characteristic_map_inv},
    { intro P, apply eq_of_homotopy, intro b, esimp, apply ua, apply fiber_pr1},
    { intro p, induction p with A f, fapply sigma_eq: esimp,
      { apply ua, apply sigma_fiber_equiv },
      { apply arrow_pathover_constant_right, intro v,
        rewrite [-cast_def _ v, cast_ua_fn],
        esimp [sigma_fiber_equiv,equiv.trans,equiv.symm,sigma_comm_equiv,comm_equiv_unc],
        induction v with b w, induction w with a p, esimp, exact p⁻¹}}
  end

  @[hott] def is_object_classifier (f : A → B)
    : pullback_square (pointed_fiber f) (fiber f) f pType.carrier :=
  pullback_square.mk
    (λa, idp)
    (is_equiv_of_equiv_of_homotopy
      (calc
        A ≃ Σb, fiber f b                      : sigma_fiber_equiv
      ... ≃ Σb (v : ΣX, X = fiber f b), v.1    : sigma_equiv_sigma_right
                                                   (λb, !sigma_equiv_of_is_contr_left)
      ... ≃ Σb X (p : X = fiber f b), X        : sigma_equiv_sigma_right
                                                   (λb, !sigma_assoc_equiv)
      ... ≃ Σb X (x : X), X = fiber f b        : sigma_equiv_sigma_right
                                                   (λb, sigma_equiv_sigma_right
                                                   (λX, !comm_equiv_nondep))
      ... ≃ Σb (v : ΣX, X), v.1 = fiber f b    : sigma_equiv_sigma_right
                                                   (λb, !sigma_assoc_equiv⁻¹ᵉ)
      ... ≃ Σb (Y : Type*), Y = fiber f b      : sigma_equiv_sigma_right
                                     (λb, sigma_equiv_sigma (pType.sigma_char)⁻¹ᵉ
                                                            (λv, sigma.rec_on v (λx y, equiv.rfl)))
      ... ≃ Σ(Y : Type*) b, Y = fiber f b      : sigma_comm_equiv
      ... ≃ pullback pType.carrier (fiber f) : !pullback.sigma_char⁻¹ᵉ
        )
      proof λb, idp qed)

end univ
