/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

homotopy groups of a pointed space
-/

import .trunc_group types.trunc .group_theory types.nat.hott

open nat eq pointed trunc is_trunc algebra group function equiv unit is_equiv nat

-- TODO: consistently make n an argument before A
-- TODO: rename cghomotopy_group to aghomotopy_group
-- TODO: rename homotopy_group_functor_compose to homotopy_group_functor_pcompose
namespace eq

  @[hott] def inf_pgroup_loop [instance] (A : Type*) : inf_pgroup (Ω A) :=
  inf_pgroup.mk concat con.assoc inverse idp_con con_idp con.left_inv

  @[hott] def inf_group_loop (A : Type*) : inf_group (Ω A) := _

  @[hott] def ab_inf_group_loop [instance] (A : Type*) : ab_inf_group (Ω (Ω A)) :=
  ⦃ab_inf_group, inf_group_loop _, mul_comm := eckmann_hilton⦄

  @[hott] def inf_group_loopn (n : ℕ) (A : Type*) [H : is_succ n] : inf_group (Ω[n] A) :=
  by induction H; exact _

  @[hott] def ab_inf_group_loopn (n : ℕ) (A : Type*) [H : is_at_least_two n] : ab_inf_group (Ω[n] A) :=
  by induction H; exact _

  @[hott] def gloop (A : Type*) : InfGroup :=
  InfGroup.mk (Ω A) (inf_group_loop A)

  @[hott] def homotopy_group [reducible] (n : ℕ) (A : Type*) : Set* :=
  ptrunc 0 (Ω[n] A)

  notation `π[`:95  n:0 `]`:0 := homotopy_group n

  section
  local attribute inf_group_loopn [instance]
  @[hott] def group_homotopy_group [instance] [reducible] (n : ℕ) [is_succ n] (A : Type*)
    : group (π[n] A) :=
  trunc_group (Ω[n] A)
  end

  @[hott] def group_homotopy_group2 [instance] (k : ℕ) (A : Type*) :
    group (carrier (ptrunctype.to_pType (π[k + 1] A))) :=
  group_homotopy_group (k+1) A

  section
  local attribute ab_inf_group_loopn [instance]
  @[hott] def ab_group_homotopy_group [reducible] (n : ℕ) [is_at_least_two n] (A : Type*)
    : ab_group (π[n] A) :=
  trunc_ab_group (Ω[n] A)
  end

  local attribute ab_group_homotopy_group [instance]

  @[hott] def ghomotopy_group (n : ℕ) [is_succ n] (A : Type*) : Group :=
  Group.mk (π[n] A) _

  @[hott] def cghomotopy_group (n : ℕ) [is_at_least_two n] (A : Type*) : AbGroup :=
  AbGroup.mk (π[n] A) _

  @[hott] def fundamental_group (A : Type*) : Group :=
  ghomotopy_group 1 A

  notation `πg[`:95  n:0 `]`:0 := ghomotopy_group n
  notation `πag[`:95 n:0 `]`:0 := cghomotopy_group n

  notation `π₁` := fundamental_group -- should this be notation for the group or pointed type?

  @[hott] def tr_mul_tr {n : ℕ} {A : Type*} (p q : Ω[n + 1] A) :
    tr p *[πg[n+1] A] tr q = tr (p ⬝ q) :=
  by reflexivity

  @[hott] def tr_mul_tr' {n : ℕ} {A : Type*} (p q : Ω[succ n] A)
    : tr p *[π[succ n] A] tr q = tr (p ⬝ q) :=
  idp

  @[hott] def homotopy_group_pequiv (n : ℕ) {A B : Type*} (H : A ≃* B)
    : π[n] A ≃* π[n] B :=
  ptrunc_pequiv_ptrunc 0 (loopn_pequiv_loopn n H)

  @[hott] def homotopy_group_pequiv_loop_ptrunc (k : ℕ) (A : Type*) :
    π[k] A ≃* Ω[k] (ptrunc k A) :=
  begin
    refine !loopn_ptrunc_pequiv⁻¹ᵉ* ⬝e* _,
    exact loopn_pequiv_loopn k (pequiv_of_eq begin rewrite [trunc_index.zero_add] end)
  end

  open trunc_index
  @[hott] def homotopy_group_ptrunc_of_le {k n : ℕ} (H : k ≤ n) (A : Type*) :
    π[k] (ptrunc n A) ≃* π[k] A :=
  calc
    π[k] (ptrunc n A) ≃* Ω[k] (ptrunc k (ptrunc n A))
             : homotopy_group_pequiv_loop_ptrunc k (ptrunc n A)
      ... ≃* Ω[k] (ptrunc k A)
             : loopn_pequiv_loopn k (ptrunc_ptrunc_pequiv_left A (of_nat_le_of_nat H))
      ... ≃* π[k] A : (homotopy_group_pequiv_loop_ptrunc k A)⁻¹ᵉ*

  @[hott] def homotopy_group_ptrunc (k : ℕ) (A : Type*) :
    π[k] (ptrunc k A) ≃* π[k] A :=
  homotopy_group_ptrunc_of_le (le.refl k) A

  @[hott] theorem trivial_homotopy_of_is_set (A : Type*) [H : is_set A] (n : ℕ) : πg[n+1] A ≃g G0 :=
  begin
    apply trivial_group_of_is_contr,
    apply is_trunc_trunc_of_is_trunc,
    apply is_contr_loop_of_is_trunc,
    apply is_trunc_succ_succ_of_is_set
  end

  @[hott] def homotopy_group_succ_out (A : Type*) (n : ℕ) : π[n + 1] A = π₁ (Ω[n] A) := idp

  @[hott] def homotopy_group_succ_in (A : Type*) (n : ℕ) : π[n + 1] A ≃* π[n] (Ω A) :=
  ptrunc_pequiv_ptrunc 0 (loopn_succ_in A n)

  @[hott] def ghomotopy_group_succ_out (A : Type*) (n : ℕ) : πg[n + 1] A = π₁ (Ω[n] A) := idp

  @[hott] def homotopy_group_succ_in_con {A : Type*} {n : ℕ} (g h : πg[n + 2] A) :
    homotopy_group_succ_in A (succ n) (g * h) =
    homotopy_group_succ_in A (succ n) g * homotopy_group_succ_in A (succ n) h :=
  begin
    induction g with p, induction h with q, esimp,
    apply ap tr, apply loopn_succ_in_con
  end

  @[hott] def ghomotopy_group_succ_in (A : Type*) (n : ℕ) :
    πg[n + 2] A ≃g πg[n + 1] (Ω A) :=
  begin
    fapply isomorphism_of_equiv,
    { exact homotopy_group_succ_in A (succ n)},
    { exact homotopy_group_succ_in_con},
  end

  @[hott] def is_contr_homotopy_group_of_is_contr (A : Type*) (n : ℕ) [is_contr A] : is_contr (π[n] A) :=
  begin
    apply is_trunc_trunc_of_is_trunc,
    apply is_contr_loop_of_is_trunc,
    apply is_trunc_of_is_contr
  end

  @[hott] def homotopy_group_functor (n : ℕ) {A B : Type*} (f : A →* B)
    : π[n] A →* π[n] B :=
  ptrunc_functor 0 (apn n f)

  notation `π→[`:95  n:0 `]`:0 := homotopy_group_functor n

  @[hott] def homotopy_group_functor_phomotopy (n : ℕ) {A B : Type*} {f g : A →* B}
    (p : f ~* g) : π→[n] f ~* π→[n] g :=
  ptrunc_functor_phomotopy 0 (apn_phomotopy n p)

  @[hott] def homotopy_group_functor_pid (n : ℕ) (A : Type*) : π→[n] (pid A) ~* pid (π[n] A) :=
  ptrunc_functor_phomotopy 0 !apn_pid ⬝* !ptrunc_functor_pid

  @[hott] def homotopy_group_functor_compose (n : ℕ) {A B C : Type*} (g : B →* C)
    (f : A →* B) : π→[n] (g ∘* f) ~* π→[n] g ∘* π→[n] f :=
  ptrunc_functor_phomotopy 0 !apn_pcompose ⬝* !ptrunc_functor_pcompose

  @[hott] def is_equiv_homotopy_group_functor (n : ℕ) {A B : Type*} (f : A →* B)
    [is_equiv f] : is_equiv (π→[n] f) :=
  @(is_equiv_trunc_functor 0 _) !is_equiv_apn

  @[hott] def homotopy_group_functor_succ_phomotopy_in (n : ℕ) {A B : Type*} (f : A →* B) :
    homotopy_group_succ_in B n ∘* π→[n + 1] f ~*
    π→[n] (Ω→ f) ∘* homotopy_group_succ_in A n :=
  begin
    refine !ptrunc_functor_pcompose⁻¹* ⬝* _ ⬝* !ptrunc_functor_pcompose,
    exact ptrunc_functor_phomotopy 0 (apn_succ_phomotopy_in n f)
  end

  @[hott] def is_equiv_homotopy_group_functor_ap1 (n : ℕ) {A B : Type*} (f : A →* B)
    [is_equiv (π→[n + 1] f)] : is_equiv (π→[n] (Ω→ f)) :=
  have is_equiv (π→[n] (Ω→ f) ∘ homotopy_group_succ_in A n),
  from is_equiv_of_equiv_of_homotopy (equiv.mk (π→[n+1] f) _ ⬝e homotopy_group_succ_in B n)
                                     (homotopy_group_functor_succ_phomotopy_in n f),
  is_equiv.cancel_right (homotopy_group_succ_in A n) _

  @[hott] def tinverse {X : Type*} : π[1] X →* π[1] X :=
  ptrunc_functor 0 pinverse

  @[hott] def is_equiv_tinverse (A : Type*) : is_equiv (@tinverse A) :=
  by apply @is_equiv_trunc_functor; apply is_equiv_eq_inverse

  @[hott] def ptrunc_functor_pinverse {X : Type*}
    : ptrunc_functor 0 (@pinverse X) ~* @tinverse X :=
  begin
    fapply phomotopy.mk,
    { reflexivity},
    { reflexivity}
  end

  @[hott] def homotopy_group_functor_mul (n : ℕ) {A B : Type*} (g : A →* B)
    (p q : πg[n+1] A) :
    (π→[n + 1] g) (p *[πg[n+1] A] q) = (π→[n+1] g) p *[πg[n+1] B] (π→[n + 1] g) q :=
  begin
    unfold [ghomotopy_group, homotopy_group] at *,
    refine @trunc.rec _ _ _ (λq, !is_trunc_eq) _ p, clear p, intro p,
    refine @trunc.rec _ _ _ (λq, !is_trunc_eq) _ q, clear q, intro q,
    apply ap tr, apply apn_con
  end

  @[hott] def homotopy_group_homomorphism (n : ℕ) [H : is_succ n] {A B : Type*}
    (f : A →* B) : πg[n] A →g πg[n] B :=
  begin
    induction H with n, fconstructor,
    { exact homotopy_group_functor (n+1) f},
    { apply homotopy_group_functor_mul}
  end

  notation `π→g[`:95 n:0 `]`:0 := homotopy_group_homomorphism n

  @[hott] def homotopy_group_homomorphism_pcompose (n : ℕ) [H : is_succ n] {A B C : Type*} (g : B →* C)
    (f : A →* B) : π→g[n] (g ∘* f) ~ π→g[n] g ∘ π→g[n] f :=
  begin
    induction H with n, exact to_homotopy (homotopy_group_functor_compose (succ n) g f)
  end

  @[hott] def homotopy_group_isomorphism_of_pequiv (n : ℕ) {A B : Type*} (f : A ≃* B)
    : πg[n+1] A ≃g πg[n+1] B :=
  begin
    apply isomorphism.mk (homotopy_group_homomorphism (succ n) f),
    esimp, apply is_equiv_trunc_functor, apply is_equiv_apn,
  end

  @[hott] def homotopy_group_add (A : Type*) (n m : ℕ) :
    πg[n+m+1] A ≃g πg[n+1] (Ω[m] A) :=
  begin
    revert A, induction m with m IH: intro A,
    { reflexivity},
    { esimp [loopn, nat.add], refine !ghomotopy_group_succ_in ⬝g _, refine !IH ⬝g _,
      apply homotopy_group_isomorphism_of_pequiv,
      exact !loopn_succ_in⁻¹ᵉ*}
  end

  @[hott] theorem trivial_homotopy_add_of_is_set_loopn {A : Type*} {n : ℕ} (m : ℕ)
    (H : is_set (Ω[n] A)) : πg[m+n+1] A ≃g G0 :=
  !homotopy_group_add ⬝g !trivial_homotopy_of_is_set

  @[hott] theorem trivial_homotopy_le_of_is_set_loopn {A : Type*} {n : ℕ} (m : ℕ) (H1 : n ≤ m)
    (H2 : is_set (Ω[n] A)) : πg[m+1] A ≃g G0 :=
  obtain (k : ℕ) (p : n + k = m), from le.elim H1,
  isomorphism_of_eq (ap (λx, πg[x+1] A) (p⁻¹ ⬝ add.comm n k)) ⬝g
  trivial_homotopy_add_of_is_set_loopn k H2

  @[hott] def homotopy_group_pequiv_loop_ptrunc_con {k : ℕ} {A : Type*} (p q : πg[k +1] A) :
    homotopy_group_pequiv_loop_ptrunc (succ k) A (p * q) =
    homotopy_group_pequiv_loop_ptrunc (succ k) A p ⬝
    homotopy_group_pequiv_loop_ptrunc (succ k) A q :=
  begin
    refine _ ⬝ !loopn_pequiv_loopn_con,
    exact ap (loopn_pequiv_loopn _ _) !loopn_ptrunc_pequiv_inv_con
  end

  @[hott] def homotopy_group_pequiv_loop_ptrunc_inv_con {k : ℕ} {A : Type*}
    (p q : Ω[succ k] (ptrunc (succ k) A)) :
    (homotopy_group_pequiv_loop_ptrunc (succ k) A)⁻¹ᵉ* (p ⬝ q) =
    (homotopy_group_pequiv_loop_ptrunc (succ k) A)⁻¹ᵉ* p *
    (homotopy_group_pequiv_loop_ptrunc (succ k) A)⁻¹ᵉ* q :=
  inv_preserve_binary (homotopy_group_pequiv_loop_ptrunc (succ k) A) mul concat
    (@homotopy_group_pequiv_loop_ptrunc_con k A) p q

  @[hott] def ghomotopy_group_ptrunc_of_le {k n : ℕ} (H : k ≤ n) [Hk : is_succ k] (A : Type*) :
    πg[k] (ptrunc n A) ≃g πg[k] A :=
  begin
    fapply isomorphism_of_equiv,
    { exact homotopy_group_ptrunc_of_le H A},
    { intros g₁ g₂, induction Hk with k,
      refine _ ⬝ !homotopy_group_pequiv_loop_ptrunc_inv_con,
      apply ap ((homotopy_group_pequiv_loop_ptrunc (k+1) A)⁻¹ᵉ*),
      refine _ ⬝ !loopn_pequiv_loopn_con ,
      apply ap (loopn_pequiv_loopn (k+1) _),
      apply homotopy_group_pequiv_loop_ptrunc_con}
  end

  @[hott] def ghomotopy_group_ptrunc (k : ℕ) [is_succ k] (A : Type*) :
    πg[k] (ptrunc k A) ≃g πg[k] A :=
  ghomotopy_group_ptrunc_of_le (le.refl k) A

  /- some homomorphisms -/

  -- @[hott] def is_homomorphism_cast_loopn_succ_eq_in {A : Type*} (n : ℕ) :
  --   is_homomorphism (loopn_succ_in A (succ n) : πg[n+1+1] A → πg[n+1] (Ω A)) :=
  -- begin
  --   intros g h, induction g with g, induction h with h,
  --   xrewrite [tr_mul_tr, - + fn_cast_eq_cast_fn _ (λn, tr), tr_mul_tr, ↑cast, -tr_compose,
  --             loopn_succ_eq_in_concat, - + tr_compose],
  -- end

  @[hott] def is_mul_hom_inverse (A : Type*) (n : ℕ)
    : is_mul_hom (λp, p⁻¹ : (πag[n+2] A) → (πag[n+2] A)) :=
  begin
    intros g h, exact ap inv (mul.comm g h) ⬝ mul_inv h g,
  end

end eq
