/-
Copyright (c) 2016 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Egbert Rijke, Steve Awodey

Exact couple, derived couples, and so on
-/

/-
import algebra.group_theory hit.set_quotient types.sigma types.list types.sum .quotient_group .subgroup .ses

open eq algebra is_trunc set_quotient relation sigma sigma.ops prod prod.ops sum list trunc function group trunc
     equiv is_equiv

-- This @[hott] def needs to be moved to exactness.hlean. However we had trouble doing so. Please help.
@[hott] def iso_ker_im_of_exact {A B C : AbGroup} (f : A →g B) (g : B →g C) (E : is_exact f g) : ab_Kernel g ≃g ab_image f :=
  begin
  fapply ab_subgroup_iso,
  intro a,
  induction E,
  exact ker_in_im a,
  intros a b, induction b with q, induction q with b p, induction p,
  induction E,
  exact im_in_ker b,
  end

@[hott] def is_differential {B : AbGroup} (d : B →g B) := Π(b:B), d (d b) = 1

@[hott] def image_subgroup_of_diff {B : AbGroup} (d : B →g B) (H : is_differential d) : subgroup_rel (ab_kernel d) :=
  subgroup_rel_of_subgroup (image_subgroup d) (kernel_subgroup d)
  begin
    intros g p,
    induction p with f, induction f with h p,
    rewrite [p⁻¹],
    esimp,
    exact H h
  end

@[hott] def diff_im_in_ker {B : AbGroup} (d : B →g B) (H : is_differential d) : Π(b : B), image_subgroup d b → kernel_subgroup d b :=
  begin
    intros b p,
    induction p with q, induction q with b' p, induction p, exact H b'
  end

@[hott] def homology {B : AbGroup} (d : B →g B) (H : is_differential d) : AbGroup :=
  @quotient_ab_group (ab_kernel d) (image_subgroup_of_diff d H)

@[hott] def homology_ugly {B : AbGroup} (d : B →g B) (H : is_differential d) : AbGroup :=
  @quotient_ab_group (ab_kernel d) (image_subgroup (ab_subgroup_of_subgroup_incl (diff_im_in_ker d H)))


@[hott] def homology_iso_ugly {B : AbGroup} (d : B →g B) (H : is_differential d) : (homology d H) ≃g (homology_ugly d H) :=
  begin
  fapply @iso_of_ab_qg_group (ab_kernel d),
  intro a,
  intro p, induction p with f, induction f with b p,
  fapply tr, fapply fiber.mk, fapply sigma.mk, exact d b, fapply tr, fapply fiber.mk, exact b, reflexivity,
  induction a with c q, fapply subtype_eq, refine p ⬝ _, reflexivity,
  intros b p, induction p with f, induction f with c p, induction p,
  induction c with a q, induction q with f, induction f with a' p, induction p,
  fapply tr, fapply fiber.mk, exact a', reflexivity
  end


@[hott] def SES_iso_C {A B C C' : AbGroup} (ses : SES A B C) (k : C ≃g C') : SES A B C' :=
  begin
  fapply SES.mk,
  exact SES.f ses,
  exact k ∘g SES.g ses,
  exact SES.Hf ses,
  fapply @is_surjective_compose _ _ _ k (SES.g ses),
  exact is_surjective_of_is_equiv k,
  exact SES.Hg ses,
  fapply is_exact.mk,
  intro a,
  esimp,
  note h := SES.ex ses,
  note h2 := is_exact.im_in_ker h a,
  refine ap k h2 ⬝ _ ,
  exact to_respect_one k,
  intro b,
  intro k3,
  note h := SES.ex ses,
  note h3 := is_exact.ker_in_im h b,
  fapply is_exact.ker_in_im h,
  refine  _ ⬝ ap k⁻¹ᵍ k3 ⬝ _ ,
  esimp,
  exact (to_left_inv (equiv_of_isomorphism k) ((SES.g ses) b))⁻¹,
  exact to_respect_one k⁻¹ᵍ
  end


@[hott] def SES_of_differential_ugly {B : AbGroup} (d : B →g B) (H : is_differential d) : SES (ab_image d) (ab_kernel d) (homology_ugly d H) :=
  begin
    exact SES_of_inclusion (ab_subgroup_of_subgroup_incl (diff_im_in_ker d H)) (is_embedding_ab_subgroup_of_subgroup_incl (diff_im_in_ker d H)),
   end

@[hott] def SES_of_differential {B : AbGroup} (d : B →g B) (H : is_differential d) : SES (ab_image d) (ab_kernel d) (homology d H) :=
  begin
    fapply SES_iso_C,
    fapply SES_of_inclusion (ab_subgroup_of_subgroup_incl (diff_im_in_ker d H)) (is_embedding_ab_subgroup_of_subgroup_incl (diff_im_in_ker d H)),
    exact (homology_iso_ugly d H)⁻¹ᵍ
   end

structure exact_couple (A B : AbGroup) : Type _ :=
  ( i : A →g A) (j : A →g B) (k : B →g A)
  ( exact_ij : is_exact i j)
  ( exact_jk : is_exact j k)
  ( exact_ki : is_exact k i)

@[hott] def differential {A B : AbGroup} (EC : exact_couple A B) : B →g B :=
  (exact_couple.j EC) ∘g (exact_couple.k EC)

@[hott] def differential_is_differential {A B : AbGroup} (EC : exact_couple A B) : is_differential (differential EC) :=
  begin
    induction EC,
    induction exact_jk,
    intro b,
    exact (ap (group_fun j) (im_in_ker (group_fun k b))) ⬝ (respect_one j)
  end

section derived_couple

/-
   A - i -> A
 k ^        |
   |        v j
   B ====== B
-/

  parameters {A B : AbGroup} (EC : exact_couple A B)
  local abbreviation i := exact_couple.i EC
  local abbreviation j := exact_couple.j EC
  local abbreviation k := exact_couple.k EC
  local abbreviation d := differential EC
  local abbreviation H := differential_is_differential EC
 -- local abbreviation u := exact_couple.i (SES_of_differential d H)

@[hott] def derived_couple_A : AbGroup :=
  ab_subgroup (image_subgroup i)

@[hott] def derived_couple_B : AbGroup :=
  homology (differential EC) (differential_is_differential EC)

@[hott] def derived_couple_i : derived_couple_A →g derived_couple_A :=
  (image_lift (exact_couple.i EC)) ∘g (image_incl (exact_couple.i EC))

@[hott] def SES_of_exact_couple_at_i : SES (ab_kernel i) A (ab_image i) :=
  begin
  fapply SES_iso_C,
  fapply SES_of_subgroup (kernel_subgroup i),
  fapply ab_group_first_iso_thm i,
  end

@[hott] def kj_zero (a : A) : k (j a) = 1 :=
is_exact.im_in_ker (exact_couple.exact_jk EC) a

@[hott] def j_factor : A →g (ab_kernel d) :=
begin
  fapply ab_hom_lift j,
  intro a,
  unfold kernel_subgroup,
  exact calc
    d (j a) = j (k (j a)) : rfl
       ...  = j 1 : by exact ap j (kj_zero a)
       ...  = 1   : to_respect_one,
end

@[hott] def subgroup_iso_exact_at_A : ab_kernel i ≃g ab_image k :=
  begin
  fapply ab_subgroup_iso,
  intro a,
  induction EC,
  induction exact_ki,
  exact ker_in_im a,
  intros a b, induction b with f, induction f with b p, induction p,
  induction EC,
  induction exact_ki,
  exact im_in_ker b,
  end

@[hott] def subgroup_iso_exact_at_A_triangle : ab_kernel_incl i ~ ab_image_incl k ∘g subgroup_iso_exact_at_A :=
  begin
    fapply ab_subgroup_iso_triangle,
    intros a b, induction b with f, induction f with b p, induction p,
    induction EC, induction exact_ki, exact im_in_ker b,
  end

@[hott] def subgroup_homom_ker_to_im : ab_kernel i →g ab_image d :=
  (image_homomorphism k j) ∘g subgroup_iso_exact_at_A

open eq

@[hott] def left_square_derived_ses_aux : j_factor ∘g ab_image_incl k ~ (SES.f (SES_of_differential d H)) ∘g (image_homomorphism k j) :=
  begin
    intro x,
    induction x with a p, induction p with f, induction f with b p, induction p,
    fapply subtype_eq,
    reflexivity,
  end

@[hott] def left_square_derived_ses : j_factor ∘g (ab_kernel_incl i) ~ (SES.f (SES_of_differential d H)) ∘g subgroup_homom_ker_to_im :=
  begin
    intro x,
    exact (ap j_factor (subgroup_iso_exact_at_A_triangle x)) ⬝ (left_square_derived_ses_aux (subgroup_iso_exact_at_A x)),
  end

@[hott] def derived_couple_j_unique :
    is_contr (Σ hC, group_fun (hC ∘g SES.g SES_of_exact_couple_at_i) ~ group_fun
       (SES.g (SES_of_differential d H) ∘g j_factor)) :=
quotient_extend_unique_SES (SES_of_exact_couple_at_i) (SES_of_differential d H) (subgroup_homom_ker_to_im) (j_factor) (left_square_derived_ses)

@[hott] def derived_couple_j : derived_couple_A →g derived_couple_B :=
   begin
     exact pr1 (center' (derived_couple_j_unique)),
   end

@[hott] def derived_couple_j_htpy : group_fun (derived_couple_j ∘g SES.g SES_of_exact_couple_at_i) ~ group_fun
       (SES.g (SES_of_differential d H) ∘g j_factor) :=
   begin
     exact pr2 (center' (derived_couple_j_unique)),
   end

@[hott] def SES_im_i_trivial : SES trivial_ab_group derived_couple_A derived_couple_A :=
  begin
    fapply SES_of_isomorphism_right,
    fapply isomorphism.refl,
  end

@[hott] def subgroup_iso_exact_kerj_imi : ab_kernel j ≃g ab_image i :=
  begin
    fapply iso_ker_im_of_exact,
    induction EC,
    exact exact_ij,
  end

@[hott] def k_restrict_aux : ab_kernel d →g ab_kernel j :=
  begin
    fapply ab_hom_lift_kernel,
    exact k ∘g ab_kernel_incl d,
    intro p, induction p with b p, exact p,
  end

@[hott] def k_restrict : ab_kernel d →g derived_couple_A :=
  subgroup_iso_exact_kerj_imi ∘g k_restrict_aux

@[hott] def k_restrict_square_left : k_restrict ∘g (SES.f (SES_of_differential d H)) ~ λ x, 1 :=
  begin
    intro x,
    induction x with b' p,
    induction p with q,
    induction q with b p,
    induction p,
    fapply subtype_eq,
    induction EC,
    induction exact_jk,
    fapply im_in_ker,
  end

@[hott] def derived_couple_k_unique :   is_contr
    (Σ hC, group_fun (hC ∘g SES.g (SES_of_differential d H)) ~ group_fun
       (SES.g SES_im_i_trivial ∘g k_restrict))
  :=
quotient_extend_unique_SES (SES_of_differential d H) (SES_im_i_trivial) (trivial_homomorphism (ab_image d) trivial_ab_group) (k_restrict) (k_restrict_square_left)

@[hott] def derived_couple_k : derived_couple_B →g derived_couple_A :=
   begin
     exact pr1 (center' (derived_couple_k_unique)),
   end

@[hott] def derived_couple_k_htpy : group_fun (derived_couple_k ∘g SES.g (SES_of_differential d H)) ~ group_fun
       (SES.g (SES_im_i_trivial) ∘g k_restrict) :=
   begin
     exact pr2 (center' (derived_couple_k_unique)),
   end

@[hott] def derived_couple_exact_ij : is_exact_ag derived_couple_i derived_couple_j :=
  begin
    fapply is_exact.mk,
    intro a,
    induction a with a' t,
    induction t with q, induction q with a p, induction p,
    repeat exact sorry,
  end

end derived_couple

-/
