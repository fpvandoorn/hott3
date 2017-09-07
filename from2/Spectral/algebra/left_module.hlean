/-
Copyright (c) 2015 Nathaniel Thomas. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Nathaniel Thomas, Jeremy Avigad, Floris van Doorn

Modules prod vector spaces over a ring.

(We use "left_module," which is more precise, because "module" is a keyword.)
-/
import algebra.field ..move_to_lib .exactness algebra.group_power
open is_trunc pointed function sigma eq algebra prod is_equiv equiv group

structure has_scalar [class] (F V : Type _) :=
(smul : F → V → V)

infixl ` • `:73 := has_scalar.smul

/- modules over a ring -/

namespace left_module

structure left_module (R M : Type _) [ringR : ring R] extends has_scalar R M, ab_group M renaming
  mul → add mul_assoc → add_assoc one → zero one_mul → zero_add mul_one → add_zero inv → neg
  mul_left_inv → add_left_inv mul_comm → add_comm :=
(smul_left_distrib : Π (r : R) (x y : M), smul r (add x y) = (add (smul r x) (smul r y)))
(smul_right_distrib : Π (r s : R) (x : M), smul (ring.add _ r s) x = (add (smul r x) (smul s x)))
(mul_smul : Π r s x, smul (mul r s) x = smul r (smul s x))
(one_smul : Π x, smul one x = x)

/- we make it a class now (and not as part of the structure) to avoid
  left_module.to_ab_group to be an instance -/
attribute left_module [class]

@[hott] def add_ab_group_of_left_module [reducible] [trans_instance] (R M : Type _) [K : ring R]
  [H : left_module R M] : add_ab_group M :=
@left_module.to_ab_group R M K H

@[hott] def has_scalar_of_left_module [reducible] [trans_instance] (R M : Type _) [K : ring R]
  [H : left_module R M] : has_scalar R M :=
@left_module.to_has_scalar R M K H

section left_module
  variables {R M : Type _}
  variable  [ringR : ring R]
  variable  [moduleRM : left_module R M]
  include   ringR moduleRM

  -- Note: the anonymous include does not work in the propositions below.

  @[hott] proposition smul_left_distrib (a : R) (u v : M) : a • (u + v) = a • u + a • v :=
  !left_module.smul_left_distrib

  @[hott] proposition smul_right_distrib (a b : R) (u : M) : (a + b) • u = a • u + b • u :=
  !left_module.smul_right_distrib

  @[hott] proposition mul_smul (a : R) (b : R) (u : M) : (a * b) • u = a • (b • u) :=
  !left_module.mul_smul

  @[hott] proposition one_smul (u : M) : (1 : R) • u = u := !left_module.one_smul

  @[hott] proposition zero_smul (u : M) : (0 : R) • u = 0 :=
  have (0 : R) • u + 0 • u = 0 • u + 0, by rewrite [-smul_right_distrib, *add_zero],
  !add.left_cancel this

  @[hott] proposition smul_zero (a : R) : a • (0 : M) = 0 :=
  have a • (0:M) + a • 0 = a • 0 + 0, by rewrite [-smul_left_distrib, *add_zero],
  !add.left_cancel this

  @[hott] proposition neg_smul (a : R) (u : M) : (-a) • u = - (a • u) :=
  eq_neg_of_add_eq_zero (by rewrite [-smul_right_distrib, add.left_inv, zero_smul])

  @[hott] proposition neg_one_smul (u : M) : -(1 : R) • u = -u :=
  by rewrite [neg_smul, one_smul]

  @[hott] proposition smul_neg (a : R) (u : M) : a • (-u) = -(a • u) :=
  by rewrite [-neg_one_smul, -mul_smul, mul_neg_one_eq_neg, neg_smul]

  @[hott] proposition smul_sub_left_distrib (a : R) (u v : M) : a • (u - v) = a • u - a • v :=
  by rewrite [sub_eq_add_neg, smul_left_distrib, smul_neg]

  @[hott] proposition sub_smul_right_distrib (a b : R) (v : M) : (a - b) • v = a • v - b • v :=
  by rewrite [sub_eq_add_neg, smul_right_distrib, neg_smul]

end left_module

/- vector spaces -/

structure vector_space [class] (F V : Type _) [fieldF : field F]
  extends left_module F V

/- homomorphisms -/

@[hott] def is_smul_hom [class] (R : Type _) {M₁ M₂ : Type _} [has_scalar R M₁] [has_scalar R M₂]
  (f : M₁ → M₂) : Type _ :=
∀ r : R, ∀ a : M₁, f (r • a) = r • f a

@[hott] def is_prop_is_smul_hom [instance] (R : Type _) {M₁ M₂ : Type _} [is_set M₂]
  [has_scalar R M₁] [has_scalar R M₂] (f : M₁ → M₂) : is_prop (is_smul_hom R f) :=
begin unfold is_smul_hom, apply _ end

@[hott] def respect_smul (R : Type _) {M₁ M₂ : Type _} [has_scalar R M₁] [has_scalar R M₂]
    (f : M₁ → M₂) [H : is_smul_hom R f] :
  ∀ r : R, ∀ a : M₁, f (r • a) = r • f a :=
H

@[hott] def is_module_hom [class] (R : Type _) {M₁ M₂ : Type _}
  [has_scalar R M₁] [has_scalar R M₂] [add_group M₁] [add_group M₂]
  (f : M₁ → M₂) :=
is_add_hom f × is_smul_hom R f

@[hott] def is_add_hom_of_is_module_hom [instance] (R : Type _) {M₁ M₂ : Type _}
  [has_scalar R M₁] [has_scalar R M₂] [add_group M₁] [add_group M₂]
  (f : M₁ → M₂) [H : is_module_hom R f] : is_add_hom f :=
prod.pr1 H

@[hott] def is_smul_hom_of_is_module_hom [instance] {R : Type _} {M₁ M₂ : Type _}
  [has_scalar R M₁] [has_scalar R M₂] [add_group M₁] [add_group M₂]
  (f : M₁ → M₂) [H : is_module_hom R f] : is_smul_hom R f :=
prod.pr2 H

-- Why do we have to give the instance explicitly?
@[hott] def is_prop_is_module_hom [instance] (R : Type _) {M₁ M₂ : Type _}
  [has_scalar R M₁] [has_scalar R M₂] [add_group M₁] [add_group M₂]
  (f : M₁ → M₂) : is_prop (is_module_hom R f) :=
have h₁ : is_prop (is_add_hom f), from is_prop_is_add_hom f,
begin unfold is_module_hom, apply _ end

section module_hom
  variables {R : Type _} {M₁ M₂ M₃ : Type _}
  variables [has_scalar R M₁] [has_scalar R M₂] [has_scalar R M₃]
  variables [add_group M₁] [add_group M₂] [add_group M₃]
  variables (g : M₂ → M₃) (f : M₁ → M₂) [is_module_hom R g] [is_module_hom R f]

  @[hott] proposition is_module_hom_id : is_module_hom R (@id M₁) :=
  pair (λ a₁ a₂, rfl) (λ r a, rfl)

  @[hott] proposition is_module_hom_comp : is_module_hom R (g ∘ f) :=
  pair
    (take a₁ a₂, begin esimp, rewrite [respect_add f, respect_add g] end)
    (take r a, by esimp; rewrite [respect_smul R f, respect_smul R g])

  @[hott] proposition respect_smul_add_smul (a b : R) (u v : M₁) : f (a • u + b • v) = a • f u + b • f v :=
  by rewrite [respect_add f, +respect_smul R f]

end module_hom

section hom_constant
  variables {R : Type _} {M₁ M₂ : Type _}
  variables [ring R] [has_scalar R M₁] [add_group M₁] [left_module R M₂]
  @[hott] proposition is_module_hom_constant : is_module_hom R (const M₁ (0 : M₂)) :=
  (λm₁ m₂, !add_zero⁻¹, λr m, (smul_zero r)⁻¹ᵖ)

end hom_constant

structure LeftModule (R : Ring) :=
(carrier : Type _) (struct : left_module R carrier)

attribute LeftModule.struct [instance]

section
local attribute LeftModule.carrier [coercion]

@[hott] def AddAbGroup_of_LeftModule [coercion] {R : Ring} (M : LeftModule R) : AddAbGroup :=
AddAbGroup.mk M (LeftModule.struct M)
end

@[hott] def LeftModule.struct2 [instance] {R : Ring} (M : LeftModule R) : left_module R M :=
LeftModule.struct M

-- @[hott] def LeftModule.struct3 [instance] {R : Ring} (M : LeftModule R) :
--   left_module R (AddAbGroup_of_LeftModule M) :=
-- _


@[hott] def pointed_LeftModule_carrier [instance] {R : Ring} (M : LeftModule R) :
  pointed (LeftModule.carrier M) :=
pointed.mk zero

@[hott] def pSet_of_LeftModule {R : Ring} (M : LeftModule R) : Set* :=
pSet.mk' (LeftModule.carrier M)

@[hott] def left_module_AddAbGroup_of_LeftModule [instance] {R : Ring} (M : LeftModule R) :
  left_module R (AddAbGroup_of_LeftModule M) :=
LeftModule.struct M

@[hott] def left_module_of_ab_group {G : Type _} [gG : add_ab_group G] {R : Type _} [ring R]
  (smul : R → G → G)
  (h1 : Π (r : R) (x y : G), smul r (x + y) = (smul r x + smul r y))
  (h2 : Π (r s : R) (x : G), smul (r + s) x = (smul r x + smul s x))
  (h3 : Π r s x, smul (r * s) x = smul r (smul s x))
  (h4 : Π x, smul 1 x = x) : left_module R G  :=
left_module.mk smul _ add add.assoc 0 zero_add add_zero neg add.left_inv add.comm h1 h2 h3 h4

@[hott] def LeftModule_of_AddAbGroup {R : Ring} (G : AddAbGroup) (smul : R → G → G)
  (h1 h2 h3 h4) : LeftModule R :=
LeftModule.mk G (left_module_of_ab_group smul h1 h2 h3 h4)

section
  variables {R : Ring} {M M₁ M₂ M₃ : LeftModule R}

  @[hott] def smul_homomorphism (M : LeftModule R) (r : R) : M →a M :=
  add_homomorphism.mk (λg, r • g) (smul_left_distrib r)

  @[hott] proposition to_smul_left_distrib (a : R) (u v : M) : a • (u + v) = a • u + a • v :=
  !smul_left_distrib

  @[hott] proposition to_smul_right_distrib (a b : R) (u : M) : (a + b) • u = a • u + b • u :=
  !smul_right_distrib

  @[hott] proposition to_mul_smul (a : R) (b : R) (u : M) : (a * b) • u = a • (b • u) :=
  !mul_smul

  @[hott] proposition to_one_smul (u : M) : (1 : R) • u = u := !one_smul

  structure homomorphism (M₁ M₂ : LeftModule R) : Type _ :=
    (fn : LeftModule.carrier M₁ → LeftModule.carrier M₂)
    (p : is_module_hom R fn)

  infix ` →lm `:55 := homomorphism

  @[hott] def homomorphism_fn [coercion] := @homomorphism.fn

  @[hott] def is_module_hom_of_homomorphism [instance] [priority 900]
      {M₁ M₂ : LeftModule R} (φ : M₁ →lm M₂) : is_module_hom R φ :=
  homomorphism.p φ

  section

    variable (φ : M₁ →lm M₂)

    @[hott] def to_respect_add (x y : M₁) : φ (x + y) = φ x + φ y :=
    respect_add φ x y

    @[hott] def to_respect_smul (a : R) (x : M₁) : φ (a • x) = a • (φ x) :=
    respect_smul R φ a x

    @[hott] def to_respect_sub (x y : M₁) : φ (x - y) = φ x - φ y :=
    respect_sub φ x y

    @[hott] def is_embedding_of_homomorphism /- φ -/ (H : Π{x}, φ x = 0 → x = 0) : is_embedding φ :=
    is_embedding_of_is_add_hom φ @H

    variables (M₁ M₂)
    @[hott] def is_set_homomorphism [instance] : is_set (M₁ →lm M₂) :=
    begin
      have H : M₁ →lm M₂ ≃ Σ(f : LeftModule.carrier M₁ → LeftModule.carrier M₂),
        is_module_hom (Ring.carrier R) f,
      begin
        fapply equiv.MK,
        { intro φ, induction φ, constructor, exact p},
        { intro v, induction v with f H, constructor, exact H},
        { intro v, induction v, reflexivity},
        { intro φ, induction φ, reflexivity}
      end,
    have ∀ f : LeftModule.carrier M₁ → LeftModule.carrier M₂,
      is_set (is_module_hom (Ring.carrier R) f), from _,
    apply is_trunc_equiv_closed_rev, exact H
  end

  variables {M₁ M₂}
  @[hott] def pmap_of_homomorphism /- φ -/ :
    pSet_of_LeftModule M₁ →* pSet_of_LeftModule M₂ :=
  have H : φ 0 = 0, from respect_zero φ,
  pmap.mk φ begin esimp, exact H end

  @[hott] def homomorphism_change_fun
    (φ : M₁ →lm M₂) (f : M₁ → M₂) (p : φ ~ f) : M₁ →lm M₂ :=
  homomorphism.mk f
    (prod.mk
      (λx₁ x₂, (p (x₁ + x₂))⁻¹ ⬝ to_respect_add φ x₁ x₂ ⬝ ap011 _ (p x₁) (p x₂))
      (λ a x, (p (a • x))⁻¹ ⬝ to_respect_smul φ a x ⬝ ap01 _ (p x)))

  @[hott] def homomorphism_eq (φ₁ φ₂ : M₁ →lm M₂) (p : φ₁ ~ φ₂) : φ₁ = φ₂ :=
  begin
    induction φ₁ with φ₁ q₁, induction φ₂ with φ₂ q₂, esimp at p, induction p,
    exact ap (homomorphism.mk φ₁) !is_prop.elim
  end
end

  section

  @[hott] def homomorphism.mk' (φ : M₁ → M₂)
    (p : Π(g₁ g₂ : M₁), φ (g₁ + g₂) = φ g₁ + φ g₂)
    (q : Π(r : R) x, φ (r • x) = r • φ x) : M₁ →lm M₂ :=
  homomorphism.mk φ (p, q)

  @[hott] def to_respect_zero (φ : M₁ →lm M₂) : φ 0 = 0 :=
  respect_zero φ

  @[hott] def homomorphism_compose [reducible] (f' : M₂ →lm M₃) (f : M₁ →lm M₂) :
    M₁ →lm M₃ :=
  homomorphism.mk (f' ∘ f) !is_module_hom_comp

  variable (M)
  @[hott] def homomorphism_id [reducible] [refl] : M →lm M :=
  homomorphism.mk (@id M) !is_module_hom_id
  variable {M}

  abbreviation lmid := homomorphism_id M
  infixr ` ∘lm `:75 := homomorphism_compose

  @[hott] def lm_constant (M₁ M₂ : LeftModule R) : M₁ →lm M₂ :=
  homomorphism.mk (const M₁ 0) !is_module_hom_constant

  structure isomorphism (M₁ M₂ : LeftModule R) :=
    (to_hom : M₁ →lm M₂)
    (is_equiv_to_hom : is_equiv to_hom)

  infix ` ≃lm `:25 := isomorphism
  attribute isomorphism.to_hom [coercion]
  attribute isomorphism.is_equiv_to_hom [instance]
  attribute isomorphism._trans_of_to_hom

  @[hott] def equiv_of_isomorphism (φ : M₁ ≃lm M₂) : M₁ ≃ M₂ :=
  equiv.mk φ !isomorphism.is_equiv_to_hom

  section
  local attribute pSet_of_LeftModule [coercion]
  @[hott] def pequiv_of_isomorphism (φ : M₁ ≃lm M₂) : M₁ ≃* M₂ :=
  pequiv_of_equiv (equiv_of_isomorphism φ) (to_respect_zero φ)
  end

  @[hott] def isomorphism_of_equiv (φ : M₁ ≃ M₂)
    (p : Π(g₁ g₂ : M₁), φ (g₁ + g₂) = φ g₁ + φ g₂)
    (q : Πr x, φ (r • x) = r • φ x) : M₁ ≃lm M₂ :=
  isomorphism.mk (homomorphism.mk φ (p, q)) !to_is_equiv

  @[hott] def isomorphism_of_eq {M₁ M₂ : LeftModule R} (p : M₁ = M₂ :> LeftModule R)
    : M₁ ≃lm M₂ :=
  isomorphism_of_equiv (equiv_of_eq (ap LeftModule.carrier p))
    begin intros, induction p, reflexivity end
    begin intros, induction p, reflexivity end

  -- @[hott] def pequiv_of_isomorphism_of_eq {M₁ M₂ : LeftModule R} (p : M₁ = M₂ :> LeftModule R) :
  --   pequiv_of_isomorphism (isomorphism_of_eq p) = pequiv_of_eq (ap pType_of_LeftModule p) :=
  -- begin
  --   induction p,
  --   apply pequiv_eq,
  --   fapply pmap_eq,
  --   { intro g, reflexivity},
  --   { apply is_prop.elim}
  -- end

  @[hott] def to_lminv (φ : M₁ ≃lm M₂) : M₂ →lm M₁ :=
  homomorphism.mk φ⁻¹
    abstract begin
    split,
      intros g₁ g₂, apply eq_of_fn_eq_fn' φ,
      rewrite [respect_add φ, +right_inv φ],
      intros r x, apply eq_of_fn_eq_fn' φ,
      rewrite [to_respect_smul φ, +right_inv φ],
    end end

  variable (M)
  @[hott] def isomorphism.refl [refl] : M ≃lm M :=
  isomorphism.mk lmid !is_equiv_id
  variable {M}

  @[hott] def isomorphism.rfl [refl] : M ≃lm M := isomorphism.refl M

  @[hott] def isomorphism.symm [symm] (φ : M₁ ≃lm M₂) : M₂ ≃lm M₁ :=
  isomorphism.mk (to_lminv φ) !is_equiv_inv

  @[hott] def isomorphism.trans [trans] (φ : M₁ ≃lm M₂) (ψ : M₂ ≃lm M₃) : M₁ ≃lm M₃ :=
  isomorphism.mk (ψ ∘lm φ) !is_equiv_compose

  @[hott] def isomorphism.eq_trans [trans]
     {M₁ M₂ : LeftModule R} {M₃ : LeftModule R} (φ : M₁ = M₂) (ψ : M₂ ≃lm M₃) : M₁ ≃lm M₃ :=
  proof isomorphism.trans (isomorphism_of_eq φ) ψ qed

  @[hott] def isomorphism.trans_eq [trans]
    {M₁ : LeftModule R} {M₂ M₃ : LeftModule R} (φ : M₁ ≃lm M₂) (ψ : M₂ = M₃) : M₁ ≃lm M₃ :=
  isomorphism.trans φ (isomorphism_of_eq ψ)

  postfix `⁻¹ˡᵐ`:(max + 1) := isomorphism.symm
  infixl ` ⬝lm `:75 := isomorphism.trans
  infixl ` ⬝lmp `:75 := isomorphism.trans_eq
  infixl ` ⬝plm `:75 := isomorphism.eq_trans

  @[hott] def homomorphism_of_eq {M₁ M₂ : LeftModule R} (p : M₁ = M₂ :> LeftModule R)
    : M₁ →lm M₂ :=
  isomorphism_of_eq p

  @[hott] def group_homomorphism_of_lm_homomorphism {M₁ M₂ : LeftModule R}
    (φ : M₁ →lm M₂) : M₁ →a M₂ :=
  add_homomorphism.mk φ (to_respect_add φ)

  @[hott] def lm_homomorphism_of_group_homomorphism {M₁ M₂ : LeftModule R}
    (φ : M₁ →a M₂) (h : Π(r : R) g, φ (r • g) = r • φ g) : M₁ →lm M₂ :=
  homomorphism.mk' φ (group.to_respect_add φ) h

  section
  local attribute pSet_of_LeftModule [coercion]
  @[hott] def is_exact_mod (f : M₁ →lm M₂) (f' : M₂ →lm M₃) : Type _ :=
  @is_exact M₁ M₂ M₃ (homomorphism_fn f) (homomorphism_fn f')

  @[hott] def is_exact_mod.mk {f : M₁ →lm M₂} {f' : M₂ →lm M₃}
    (h₁ : Πm, f' (f m) = 0) (h₂ : Πm, f' m = 0 → image f m) : is_exact_mod f f' :=
  is_exact.mk h₁ h₂

  structure short_exact_mod (A B C : LeftModule R) :=
    (f : A →lm B)
    (g : B →lm C)
    (h : @is_short_exact A B C f g)

  local abbreviation g_of_lm := @group_homomorphism_of_lm_homomorphism
  @[hott] def short_exact_mod_of_is_exact {X A B C Y : LeftModule R}
    (k : X →lm A) (f : A →lm B) (g : B →lm C) (l : C →lm Y)
    (hX : is_contr X) (hY : is_contr Y)
    (kf : is_exact_mod k f) (fg : is_exact_mod f g) (gl : is_exact_mod g l) :
    short_exact_mod A B C :=
  short_exact_mod.mk f g
    (is_short_exact_of_is_exact (g_of_lm k) (g_of_lm f) (g_of_lm g) (g_of_lm l) hX hY kf fg gl)

  @[hott] def short_exact_mod_isomorphism {A B A' B' C C' : LeftModule R}
    (eA : A ≃lm A') (eB : B ≃lm B') (eC : C ≃lm C')
    (H : short_exact_mod A' B' C') : short_exact_mod A B C :=
  short_exact_mod.mk (eB⁻¹ˡᵐ ∘lm short_exact_mod.f H ∘lm eA) (eC⁻¹ˡᵐ ∘lm short_exact_mod.g H ∘lm eB)
    (is_short_exact_equiv _ _
      (equiv_of_isomorphism eA) (equiv_of_isomorphism eB) (pequiv_of_isomorphism eC)
      (λa, to_right_inv (equiv_of_isomorphism eB) _) (λb, to_right_inv (equiv_of_isomorphism eC) _)
      (short_exact_mod.h H))

  @[hott] def is_contr_middle_of_short_exact_mod {A B C : LeftModule R} (H : short_exact_mod A B C)
    (HA : is_contr A) (HC : is_contr C) : is_contr B :=
  is_contr_middle_of_is_exact (is_exact_of_is_short_exact (short_exact_mod.h H))

  end

  end

end

section int
open int
@[hott] def left_module_int_of_ab_group (A : Type _) [add_ab_group A] : left_module rℤ A :=
left_module_of_ab_group imul imul_add add_imul mul_imul one_imul

@[hott] def LeftModule_int_of_AbGroup (A : AddAbGroup) : LeftModule rℤ :=
LeftModule.mk A (left_module_int_of_ab_group A)

@[hott] def lm_hom_int.mk {A B : AbGroup} (φ : A →g B) :
  LeftModule_int_of_AbGroup A →lm LeftModule_int_of_AbGroup B :=
lm_homomorphism_of_group_homomorphism φ (to_respect_imul φ)

@[hott] def lm_iso_int.mk {A B : AbGroup} (φ : A ≃g B) :
  LeftModule_int_of_AbGroup A ≃lm LeftModule_int_of_AbGroup B :=
isomorphism.mk (lm_hom_int.mk φ) (group.isomorphism.is_equiv_to_hom φ)
end int

end left_module
