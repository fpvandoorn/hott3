/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

The Freudenthal Suspension Theorem
-/

import homotopy.wedge homotopy.circle

open eq is_conn is_trunc pointed susp nat pi equiv is_equiv trunc fiber trunc_index

namespace freudenthal section

  parameters {A : Type*} {n : ℕ} [is_conn n A]

  /-
    This proof is ported from Agda
    This is the 95% version of the Freudenthal Suspension Theorem, which means that we don't
    prove that loop_susp_unit : A →* Ω(susp A) is 2n-connected (if A is n-connected),
    but instead we only prove that it induces an equivalence on the first 2n homotopy groups.
  -/

  private @[hott] def up (a : A) : north = north :> susp A :=
  loop_susp_unit A a

  @[hott] def code_merid : A → ptrunc (n + n) A → ptrunc (n + n) A :=
  begin
    have is_conn n (ptrunc (n + n) A), from !is_conn_trunc,
    refine @wedge_extension.ext _ _ n n _ _ (λ x y, ttrunc (n + n) A) _ _ _ _,
    { intros, apply is_trunc_trunc}, -- this subgoal might become unnecessary if
                                     -- type class inference catches it
    { exact tr},
    { exact id},
    { reflexivity}
  end

  @[hott] def code_merid_β_left (a : A) : code_merid a pt = tr a :=
  by apply wedge_extension.β_left

  @[hott] def code_merid_β_right (b : ptrunc (n + n) A) : code_merid pt b = b :=
  by apply wedge_extension.β_right

  @[hott] def code_merid_coh : code_merid_β_left pt = code_merid_β_right pt :=
  begin
    symmetry, apply eq_of_inv_con_eq_idp, apply wedge_extension.coh
  end

  @[hott] def is_equiv_code_merid (a : A) : is_equiv (code_merid a) :=
  begin
    have Πa, is_trunc n.-2.+1 (is_equiv (code_merid a)),
      from λa, is_trunc_of_le _ !minus_one_le_succ,
    refine is_conn.elim (n.-1) _ _ a,
    { esimp, exact homotopy_closed id (homotopy.symm (code_merid_β_right))}
  end

  @[hott] def code_merid_equiv (a : A) : trunc (n + n) A ≃ trunc (n + n) A :=
  equiv.mk _ (is_equiv_code_merid a)

  @[hott] def code_merid_inv_pt (x : trunc (n + n) A) : (code_merid_equiv pt)⁻¹ x = x :=
  begin
    refine ap010 @(is_equiv.inv _) _ x ⬝ _,
    { exact homotopy_closed id (homotopy.symm code_merid_β_right)},
    { apply is_conn.elim_β},
    { reflexivity}
  end

  @[hott] def code : susp A → Type _ :=
  susp.elim_type (trunc (n + n) A) (trunc (n + n) A) code_merid_equiv

  @[hott] def is_trunc_code (x : susp A) : is_trunc (n + n) (code x) :=
  begin
    induction x with a: esimp,
    { exact _},
    { exact _},
    { apply is_prop.elimo}
  end
  local attribute is_trunc_code [instance]

  @[hott] def decode_north : code north → trunc (n + n) (north = north :> susp A) :=
  trunc_functor (n + n) up

  @[hott] def decode_north_pt : decode_north (tr pt) = tr idp :=
  ap tr !con.right_inv

  @[hott] def decode_south : code south → trunc (n + n) (north = south :> susp A) :=
  trunc_functor (n + n) merid

  @[hott] def encode' {x : susp A} (p : north = x) : code x :=
  transport code p (tr pt)

  @[hott] def encode {x : susp A} (p : trunc (n + n) (north = x)) : code x :=
  begin
    induction p with p,
    exact transport code p (tr pt)
  end

  @[hott] theorem encode_decode_north (c : code north) : encode (decode_north c) = c :=
  begin
    have H : Πc, is_trunc (n + n) (encode (decode_north c) = c), from _,
    esimp at *,
    induction c with a,
    rewrite [↑[encode, decode_north, up, code], con_tr, elim_type_merid, ▸*,
             code_merid_β_left, elim_type_merid_inv, ▸*, code_merid_inv_pt]
  end

  @[hott] def decode_coh_f (a : A) : tr (up pt) =[merid a] decode_south (code_merid a (tr pt)) :=
  begin
    refine _ ⬝op ap decode_south (code_merid_β_left a)⁻¹,
    apply trunc_pathover,
    apply eq_pathover_constant_left_id_right,
    apply square_of_eq,
    exact whisker_right (merid a) !con.right_inv
  end

  @[hott] def decode_coh_g (a' : A) : tr (up a') =[merid pt] decode_south (code_merid pt (tr a')) :=
  begin
    refine _ ⬝op ap decode_south (code_merid_β_right (tr a'))⁻¹,
    apply trunc_pathover,
    apply eq_pathover_constant_left_id_right,
    apply square_of_eq, refine !inv_con_cancel_right ⬝ !idp_con⁻¹
  end

  @[hott] def decode_coh_lem {A : Type _} {a a' : A} (p : a = a')
    : whisker_right p (con.right_inv p) = inv_con_cancel_right p p ⬝ (idp_con p)⁻¹ :=
  by induction p; reflexivity

  @[hott] theorem decode_coh (a : A) : decode_north =[merid a] decode_south :=
  begin
    apply arrow_pathover_left, intro c,
    induction c with a',
    rewrite [↑code, elim_type_merid],
    refine @wedge_extension.ext _ _ n n _ _ (λ a a', tr (up a') =[merid a] decode_south
    (to_fun (code_merid_equiv a) (tr a'))) _ _ _ _ a a',
    { intros, apply is_trunc_pathover, apply is_trunc_succ, apply is_trunc_trunc},
    { exact decode_coh_f},
    { exact decode_coh_g},
    { clear a a', unfold [decode_coh_f, decode_coh_g], refine ap011 concato_eq _ _,
      { refine ap (λp, trunc_pathover (eq_pathover_constant_left_id_right (square_of_eq p))) _,
        apply decode_coh_lem},
      { apply ap (λp, ap decode_south p⁻¹), apply code_merid_coh}}
  end

  @[hott] def decode {x : susp A} (c : code x) : trunc (n + n) (north = x) :=
  begin
    induction x with a,
    { exact decode_north c},
    { exact decode_south c},
    { exact decode_coh a}
  end

  @[hott] theorem decode_encode {x : susp A} (p : trunc (n + n) (north = x)) : decode (encode p) = p :=
  begin
    induction p with p, induction p, esimp, apply decode_north_pt
  end

  parameters (A n)
  @[hott] def equiv' : trunc (n + n) A ≃ trunc (n + n) (Ω (susp A)) :=
  equiv.MK decode_north encode decode_encode encode_decode_north

  @[hott] def pequiv' : ptrunc (n + n) A ≃* ptrunc (n + n) (Ω (susp A)) :=
  pequiv_of_equiv equiv' decode_north_pt

  -- We don't prove this:
  -- @[hott] theorem freudenthal_suspension : is_conn_fun (n+n) (loop_susp_unit A) := sorry

end end freudenthal

open algebra group
@[hott] def freudenthal_pequiv (A : Type*) {n k : ℕ} [is_conn n A] (H : k ≤ 2 * n)
  : ptrunc k A ≃* ptrunc k (Ω (susp A)) :=
have H' : k ≤[ℕ₋₂] n + n,
  by rewrite [mul.comm at H, -algebra.zero_add n at {1}]; exact of_nat_le_of_nat H,
ptrunc_pequiv_ptrunc_of_le H' (freudenthal.pequiv' A n)

@[hott] def freudenthal_equiv {A : Type*} {n k : ℕ} [is_conn n A] (H : k ≤ 2 * n)
  : trunc k A ≃ trunc k (Ω (susp A)) :=
freudenthal_pequiv A H

@[hott] def freudenthal_homotopy_group_pequiv (A : Type*) {n k : ℕ} [is_conn n A] (H : k ≤ 2 * n)
  : π[k + 1] (susp A) ≃* π[k] A  :=
calc
  π[k + 1] (susp A) ≃* π[k] (Ω (susp A)) : homotopy_group_succ_in (susp A) k
    ... ≃* Ω[k] (ptrunc k (Ω (susp A)))  : homotopy_group_pequiv_loop_ptrunc k (Ω (susp A))
    ... ≃* Ω[k] (ptrunc k A)             : loopn_pequiv_loopn k (freudenthal_pequiv A H)
    ... ≃* π[k] A                        : (homotopy_group_pequiv_loop_ptrunc k A)⁻¹ᵉ*

@[hott] def freudenthal_homotopy_group_isomorphism (A : Type*) {n k : ℕ} [is_conn n A]
  (H : k + 1 ≤ 2 * n) : πg[k+2] (susp A) ≃g πg[k + 1] A :=
begin
  fapply isomorphism_of_equiv,
  { exact equiv_of_pequiv (freudenthal_homotopy_group_pequiv A H)},
  { intros g h,
    refine _ ⬝ !homotopy_group_pequiv_loop_ptrunc_inv_con,
    apply ap !homotopy_group_pequiv_loop_ptrunc⁻¹ᵉ*,
    refine ap (loopn_pequiv_loopn _ _) _ ⬝ !loopn_pequiv_loopn_con,
    refine ap !homotopy_group_pequiv_loop_ptrunc _ ⬝ !homotopy_group_pequiv_loop_ptrunc_con,
    apply homotopy_group_succ_in_con}
end

  @[hott] def to_pmap_freudenthal_pequiv {A : Type*} (n k : ℕ) [is_conn n A] (H : k ≤ 2 * n)
    : freudenthal_pequiv A H ~* ptrunc_functor k (loop_susp_unit A) :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x with a, reflexivity },
    { refine !idp_con ⬝ _, refine _ ⬝ ap02 _ !idp_con⁻¹, refine _ ⬝ !ap_compose, apply ap_compose }
  end

  @[hott] def ptrunc_elim_freudenthal_pequiv {A B : Type*} (n k : ℕ) [is_conn n A] (H : k ≤ 2 * n)
    (f : A →* Ω B) [is_trunc (k.+1) (B)] :
    ptrunc.elim k (Ω→ (susp_elim f)) ∘* freudenthal_pequiv A H ~* ptrunc.elim k f :=
  begin
    refine pwhisker_left _ !to_pmap_freudenthal_pequiv ⬝* _,
    refine !ptrunc_elim_ptrunc_functor ⬝* _,
    exact ptrunc_elim_phomotopy k !ap1_susp_elim,
  end

namespace susp

  @[hott] def iterate_susp_stability_pequiv_of_is_conn_0 (A : Type*) {k n : ℕ} [is_conn 0 A]
    (H : k ≤ 2 * n) : π[k + 1] (iterate_susp (n + 1) A) ≃* π[k] (iterate_susp n A) :=
  have is_conn n (iterate_susp n A), by rewrite [-zero_add n]; exact _,
  freudenthal_homotopy_group_pequiv (iterate_susp n A) H

  @[hott] def iterate_susp_stability_isomorphism_of_is_conn_0 (A : Type*) {k n : ℕ} [is_conn 0 A]
    (H : k + 1 ≤ 2 * n) : πg[k+2] (iterate_susp (n + 1) A) ≃g πg[k+1] (iterate_susp n A) :=
  have is_conn n (iterate_susp n A), by rewrite [-zero_add n]; exact _,
  freudenthal_homotopy_group_isomorphism (iterate_susp n A) H

  @[hott] def stability_helper1 {k n : ℕ} (H : k + 2 ≤ 2 * n) : k ≤ 2 * pred n :=
  begin
    rewrite [mul_pred_right], change pred (pred (k + 2)) ≤ pred (pred (2 * n)),
    apply pred_le_pred, apply pred_le_pred, exact H
  end

  @[hott] def stability_helper2 (A : Type*) {k n : ℕ} (H : k + 2 ≤ 2 * n) :
    is_conn (pred n) (iterate_susp n A) :=
  have Π(n : ℕ), n = -1 + (n + 1),
  begin intro n, induction n with n IH, reflexivity, exact ap succ IH end,
  begin
    cases n with n,
    { exfalso, exact not_succ_le_zero _ H },
    { esimp, rewrite [this n], exact is_conn_iterate_susp -1 _ A }
  end

  @[hott] def iterate_susp_stability_pequiv (A : Type*) {k n : ℕ}
    (H : k + 2 ≤ 2 * n) : π[k + 1] (iterate_susp (n + 1) A) ≃* π[k] (iterate_susp n A) :=
  have is_conn (pred n) (iterate_susp n A), from stability_helper2 A H,
  freudenthal_homotopy_group_pequiv (iterate_susp n A) (stability_helper1 H)

  @[hott] def iterate_susp_stability_isomorphism (A : Type*) {k n : ℕ}
    (H : k + 3 ≤ 2 * n) : πg[k+2] (iterate_susp (n + 1) A) ≃g πg[k+1] (iterate_susp n A) :=
  have is_conn (pred n) (iterate_susp n A), from @stability_helper2 A (k+1) n H,
  freudenthal_homotopy_group_isomorphism (iterate_susp n A) (stability_helper1 H)

  @[hott] def iterated_freudenthal_pequiv (A : Type*) {n k m : ℕ} [HA : is_conn n A] (H : k ≤ 2 * n)
    : ptrunc k A ≃* ptrunc k (Ω[m] (iterate_susp m A)) :=
  begin
    revert A n k HA H, induction m with m IH: intros A n k HA H,
    { reflexivity },
    { have H2 : succ k ≤ 2 * succ n,
      from calc
        succ k ≤ succ (2 * n) : succ_le_succ H
           ... ≤ 2 * succ n   : self_le_succ,
      exact calc
        ptrunc k A ≃* ptrunc k (Ω (susp A))   : freudenthal_pequiv A H
          ... ≃* Ω (ptrunc (succ k) (susp A)) : loop_ptrunc_pequiv
          ... ≃* Ω (ptrunc (succ k) (Ω[m] (iterate_susp m (susp A)))) :
                   loop_pequiv_loop (IH (susp A) (succ n) (succ k) _ H2)
          ... ≃* ptrunc k (Ω[succ m] (iterate_susp m (susp A))) : loop_ptrunc_pequiv
          ... ≃* ptrunc k (Ω[succ m] (iterate_susp (succ m) A)) :
                   ptrunc_pequiv_ptrunc _ (loopn_pequiv_loopn _ !iterate_susp_succ_in)}
  end

end susp
