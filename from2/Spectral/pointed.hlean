/- equalities between pointed homotopies and other facts about pointed types/functions/homotopies -/

-- Author: Floris van Doorn

import types.pointed2 .move_to_lib

open pointed eq equiv function is_equiv unit is_trunc trunc nat algebra sigma group lift option

namespace pointed

  -- /- the pointed type of (unpointed) dependent maps -/
  -- @[hott] def pupi {A : Type _} (P : A → Type*) : Type* :=
  -- pointed.mk' (Πa, P a)

  -- @[hott] def loop_pupi_commute {A : Type _} (B : A → Type*) : Ω(pupi B) ≃* pupi (λa, Ω (B a)) :=
  -- pequiv_of_equiv eq_equiv_homotopy rfl

  -- @[hott] def equiv_pupi_right {A : Type _} {P Q : A → Type*} (g : Πa, P a ≃* Q a)
  --   : pupi P ≃* pupi Q :=
  -- pequiv_of_equiv (pi_equiv_pi_right g)
  --   begin esimp, apply eq_of_homotopy, intros a, esimp, exact (respect_pt (g a)) end


  -- @[hott] def pmap_eq_equiv {X Y : Type*} (f g : X →* Y) : (f = g) ≃ (f ~* g) :=
  -- begin
  --   refine eq_equiv_fn_eq_of_equiv (@pmap.sigma_char X Y) f g ⬝e _,
  --   refine !sigma_eq_equiv ⬝e _,
  --   refine _ ⬝e (phomotopy.sigma_char f g)⁻¹ᵉ,
  --   fapply sigma_equiv_sigma,
  --   { esimp, apply eq_equiv_homotopy },
  --   { induction g with g gp, induction Y with Y y0, esimp, intro p, induction p, esimp at *,
  --     refine !pathover_idp ⬝e _, refine _ ⬝e !eq_equiv_eq_symm,
  --     apply equiv_eq_closed_right, exact !idp_con⁻¹ }
  -- end

  /- remove some duplicates: loop_ppmap_commute, loop_ppmap_pequiv, loop_ppmap_pequiv', pfunext -/
  @[hott] def pfunext (X Y : Type*) : ppmap X (Ω Y) ≃* Ω (ppmap X Y) :=
  (loop_ppmap_commute X Y)⁻¹ᵉ*

  @[hott] def loop_phomotopy {A B : Type*} (f : A →* B) : Type* :=
  pointed.MK (f ~* f) phomotopy.rfl

  @[hott] def ppcompose_left_loop_phomotopy {A B C : Type*} (g : B →* C) {f : A →* B}
    {h : A →* C} (p : g ∘* f ~* h) : loop_phomotopy f →* loop_phomotopy h :=
  pmap.mk (λq, p⁻¹* ⬝* pwhisker_left g q ⬝* p)
    (idp ◾** !pwhisker_left_refl ◾** idp ⬝ !trans_refl ◾** idp ⬝ !trans_left_inv)

  @[hott] def ppcompose_left_loop_phomotopy' {A B C : Type*} (g : B →* C) (f : A →* B)
    : loop_phomotopy f →* loop_phomotopy (g ∘* f) :=
  pmap.mk (λq, pwhisker_left g q) !pwhisker_left_refl

  @[hott] def loop_ppmap_pequiv' (A B : Type*) :
    Ω(ppmap A B) ≃* loop_phomotopy (pconst A B) :=
  pequiv_of_equiv (pmap_eq_equiv _ _) idp

  @[hott] def ppmap_loop_pequiv' (A B : Type*) :
    loop_phomotopy (pconst A B) ≃* ppmap A (Ω B) :=
  pequiv_of_equiv (!phomotopy.sigma_char ⬝e !pmap.sigma_char⁻¹ᵉ) idp

  @[hott] def loop_ppmap_pequiv (A B : Type*) : Ω(ppmap A B) ≃* ppmap A (Ω B) :=
  loop_ppmap_pequiv' A B ⬝e* ppmap_loop_pequiv' A B

  @[hott] def loop_ppmap_pequiv'_natural_right' {X X' : Type _} (x₀ : X) (A : Type*) (f : X → X') :
    psquare (loop_ppmap_pequiv' A _) (loop_ppmap_pequiv' A _)
            (Ω→ (ppcompose_left (pmap_of_map f x₀)))
            (ppcompose_left_loop_phomotopy' (pmap_of_map f x₀) !pconst) :=
  begin
    fapply phomotopy.mk,
    { esimp, intro p,
     refine _ ⬝ ap011 (λx y, phomotopy_of_eq (ap1_gen _ x y _))
                 proof !eq_of_phomotopy_refl⁻¹ qed proof !eq_of_phomotopy_refl⁻¹ qed,
     refine _ ⬝ ap phomotopy_of_eq !ap1_gen_idp_left⁻¹,
     exact !phomotopy_of_eq_pcompose_left⁻¹ },
    { refine _ ⬝ !idp_con⁻¹, exact sorry }
  end

  @[hott] def loop_ppmap_pequiv'_natural_right {X X' : Type*} (A : Type*) (f : X →* X') :
    psquare (loop_ppmap_pequiv' A X) (loop_ppmap_pequiv' A X')
            (Ω→ (ppcompose_left f)) (ppcompose_left_loop_phomotopy f !pcompose_pconst) :=
  begin
    induction X' with X' x₀', induction f with f f₀, esimp at f, esimp at f₀, induction f₀,
    apply psquare_of_phomotopy,
    exact sorry
  end

  @[hott] def ppmap_loop_pequiv'_natural_right {X X' : Type*} (A : Type*) (f : X →* X') :
    psquare (ppmap_loop_pequiv' A X) (ppmap_loop_pequiv' A X')
            (ppcompose_left_loop_phomotopy f !pcompose_pconst) (ppcompose_left (Ω→ f)) :=
  begin
    exact sorry
  end

  @[hott] def loop_pmap_commute_natural_right_direct {X X' : Type*} (A : Type*) (f : X →* X') :
    psquare (loop_ppmap_pequiv A X) (loop_ppmap_pequiv A X')
            (Ω→ (ppcompose_left f)) (ppcompose_left (Ω→ f)) :=
  begin
    induction X' with X' x₀', induction f with f f₀, esimp at f, esimp at f₀, induction f₀,
--    refine _ ⬝* _ ◾* _, rotate 4,
    fapply phomotopy.mk,
    { intro p, esimp, esimp [pmap_eq_equiv, pcompose_pconst], exact sorry },
    { exact sorry }
  end

  @[hott] def loop_pmap_commute_natural_left {A A' : Type*} (X : Type*) (f : A' →* A) :
    psquare (loop_ppmap_commute A X) (loop_ppmap_commute A' X)
            (Ω→ (ppcompose_right f)) (ppcompose_right f) :=
  sorry

  @[hott] def loop_pmap_commute_natural_right {X X' : Type*} (A : Type*) (f : X →* X') :
    psquare (loop_ppmap_commute A X) (loop_ppmap_commute A X')
            (Ω→ (ppcompose_left f)) (ppcompose_left (Ω→ f)) :=
  loop_ppmap_pequiv'_natural_right A f ⬝h* ppmap_loop_pequiv'_natural_right A f

  /-
    Do we want to use a structure of homotopies between pointed homotopies? Or are equalities fine?
    If we set up things more generally, we could define this as
    "pointed homotopies between the dependent pointed maps p and q"
  -/
  structure phomotopy2 {A B : Type*} {f g : A →* B} (p q : f ~* g) : Type _ :=
    (homotopy_eq : p ~ q)
    (homotopy_pt_eq : whisker_right (respect_pt g) (homotopy_eq pt) ⬝ to_homotopy_pt q =
      to_homotopy_pt p)

  /- this sets it up more generally, for illustrative purposes -/
  structure ppi' (A : Type*) (P : A → Type _) (p : P pt) :=
    (to_fun : Π a : A, P a)
    (resp_pt : to_fun (Point A) = p)
  attribute ppi'.to_fun [coercion]
  @[hott] def phomotopy' {A : Type*} {P : A → Type _} {x : P pt} (f g : ppi' A P x) : Type _ :=
  ppi' A (λa, f a = g a) (ppi'.resp_pt f ⬝ (ppi'.resp_pt g)⁻¹)
  @[hott] def phomotopy2' {A : Type*} {P : A → Type _} {x : P pt} {f g : ppi' A P x}
    (p q : phomotopy' f g) : Type _ :=
  phomotopy' p q

  -- infix ` ~*2 `:50 := phomotopy2

  -- variables {A B : Type*} {f g : A →* B} (p q : f ~* g)

  -- @[hott] def phomotopy_eq_equiv_phomotopy2 : p = q ≃ p ~*2 q :=
  -- sorry

/- Homotopy between a function and its eta expansion -/

  @[hott] def pmap_eta {X Y : Type*} (f : X →* Y) : f ~* pmap.mk f (respect_pt f) :=
  begin
    fapply phomotopy.mk,
    reflexivity,
    esimp, exact !idp_con
  end

  -- this should replace pnatural_square
  @[hott] def pnatural_square2 {A B : Type _} (X : B → Type*) (Y : B → Type*) {f g : A → B}
    (h : Πa, X (f a) →* Y (g a)) {a a' : A} (p : a = a') :
    h a' ∘* ptransport X (ap f p) ~* ptransport Y (ap g p) ∘* h a :=
  by induction p; exact !pcompose_pid ⬝* !pid_pcompose⁻¹*

  @[hott] def ptransport_ap {A B : Type _} (X : B → Type*) (f : A → B) {a a' : A} (p : a = a') :
    ptransport X (ap f p) ~* ptransport (X ∘ f) p :=
  by induction p; reflexivity

  @[hott] def ptransport_constant (A : Type _) (B : Type*) {a a' : A} (p : a = a') :
    ptransport (λ(a : A), B) p ~* pid B :=
  by induction p; reflexivity

  @[hott] def ptransport_natural {A : Type _} (X : A → Type*) (Y : A → Type*)
    (h : Πa, X a →* Y a) {a a' : A} (p : a = a') :
    h a' ∘* ptransport X p ~* ptransport Y p ∘* h a :=
  by induction p; exact !pcompose_pid ⬝* !pid_pcompose⁻¹*

  section psquare
  variables {A A' A₀₀ A₂₀ A₄₀ A₀₂ A₂₂ A₄₂ A₀₄ A₂₄ A₄₄ : Type*}
            {f₁₀ f₁₀' : A₀₀ →* A₂₀} {f₃₀ : A₂₀ →* A₄₀}
            {f₀₁ f₀₁' : A₀₀ →* A₀₂} {f₂₁ f₂₁' : A₂₀ →* A₂₂} {f₄₁ : A₄₀ →* A₄₂}
            {f₁₂ f₁₂' : A₀₂ →* A₂₂} {f₃₂ : A₂₂ →* A₄₂}
            {f₀₃ : A₀₂ →* A₀₄} {f₂₃ : A₂₂ →* A₂₄} {f₄₃ : A₄₂ →* A₄₄}
            {f₁₄ : A₀₄ →* A₂₄} {f₃₄ : A₂₄ →* A₄₄}

  @[hott] def ptranspose (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : psquare f₀₁ f₂₁ f₁₀ f₁₂ :=
  p⁻¹*

  @[hott] def hsquare_of_psquare (p : psquare f₁₀ f₁₂ f₀₁ f₂₁) : hsquare f₁₀ f₁₂ f₀₁ f₂₁ :=
  p

  @[hott] def homotopy_group_functor_hsquare (n : ℕ) (h : psquare f₁₀ f₁₂ f₀₁ f₂₁) :
    psquare (π→[n] f₁₀) (π→[n] f₁₂)
            (π→[n] f₀₁) (π→[n] f₂₁) :=
  sorry

  end psquare

  @[hott] def ap1_pequiv_ap {A : Type _} (B : A → Type*) {a a' : A} (p : a = a') :
    Ω→ (pequiv_ap B p) ~* pequiv_ap (Ω ∘ B) p :=
  begin induction p, apply ap1_pid end

  @[hott] def pequiv_ap_natural {A : Type _} (B C : A → Type*) {a a' : A} (p : a = a')
    (f : Πa, B a →* C a) :
    psquare (pequiv_ap B p) (pequiv_ap C p) (f a) (f a') :=
  begin induction p, exact phrfl end

  @[hott] def is_contr_loop (A : Type*) [is_set A] : is_contr (Ω A) :=
  is_contr.mk idp (λa, !is_prop.elim)

  @[hott] def is_contr_loop_of_is_contr {A : Type*} (H : is_contr A) : is_contr (Ω A) :=
  is_contr_loop A

  @[hott] def is_contr_punit [instance] : is_contr punit :=
  is_contr_unit

  @[hott] def pequiv_of_is_contr (A B : Type*) (HA : is_contr A) (HB : is_contr B) : A ≃* B :=
  pequiv_punit_of_is_contr A _ ⬝e* (pequiv_punit_of_is_contr B _)⁻¹ᵉ*

  @[hott] def loop_pequiv_punit_of_is_set (X : Type*) [is_set X] : Ω X ≃* punit :=
  pequiv_punit_of_is_contr _ (is_contr_loop X)

  @[hott] def loop_punit : Ω punit ≃* punit :=
  loop_pequiv_punit_of_is_set punit

  @[hott] def add_point_over {A : Type _} (B : A → Type*) : A₊ → Type*
  | (some a) := B a
  | none     := plift punit

  @[hott] def add_point_over_pequiv {A : Type _} {B B' : A → Type*} (e : Πa, B a ≃* B' a) :
    Π(a : A₊), add_point_over B a ≃* add_point_over B' a
  | (some a) := e a
  | none     := pequiv.rfl

  @[hott] def phomotopy_group_plift_punit.{u} (n : ℕ) [H : is_at_least_two n] :
    πag[n] (plift.{0 u} punit) ≃g trivial_ab_group_lift.{u} :=
  begin
    induction H with n,
    have H : 0 <[ℕ] n+2, from !zero_lt_succ,
    have is_set unit, from _,
    have is_trunc (trunc_index.of_nat 0) punit, from this,
    exact isomorphism_of_is_contr (@trivial_homotopy_group_of_is_trunc _ _ _ !is_trunc_lift H)
      !is_trunc_lift
  end

  @[hott] def pmap_of_map_pt {A : Type*} {B : Type _} (f : A → B) :
    A →* pointed.MK B (f pt) :=
  pmap.mk f idp

  /- TODO: computation rule -/
  open pi
  @[hott] def fiberwise_pointed_map_rec {A : Type _} {B : A → Type*}
    (P : Π(C : A → Type*) (g : Πa, B a →* C a), Type _)
    (H : Π(C : A → Type _) (g : Πa, B a → C a), P _ (λa, pmap_of_map_pt (g a))) :
    Π⦃C : A → Type*⦄ (g : Πa, B a →* C a), P C g :=
  begin
    refine equiv_rect (!sigma_pi_equiv_pi_sigma ⬝e
             arrow_equiv_arrow_right A !pType.sigma_char⁻¹ᵉ) _ _,
    intro R, cases R with R r₀,
    refine equiv_rect (!sigma_pi_equiv_pi_sigma ⬝e
            pi_equiv_pi_right (λa, !pmap.sigma_char⁻¹ᵉ)) _ _,
    intro g, cases g with g g₀, esimp at (g, g₀),
    revert g₀, change (Π(g : (λa, g a (Point (B a))) ~ r₀), _),
    refine homotopy.rec_idp _ _, esimp,
    apply H
  end

@[hott] def ap1_gen_idp_eq {A B : Type _} (f : A → B) {a : A} (q : f a = f a) (r : q = idp) :
  ap1_gen_idp f q = ap (λx, ap1_gen f x x idp) r :=
begin cases r, reflexivity end


end pointed
