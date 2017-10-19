/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Basic group theory
-/

import algebra.category.category algebra.bundled .homomorphism

open eq algebra pointed function is_trunc pi equiv is_equiv
set_option class.force_new true

namespace group
  @[hott] def pointed_Group [instance] (G : Group) : pointed G :=
  pointed.mk 1

  @[hott] def Group.struct' [instance] [reducible] (G : Group) : group G :=
  Group.struct G

  @[hott] def ab_group_pSet_of_Group [instance] (G : AbGroup) : ab_group (pSet_of_Group G) :=
  AbGroup.struct G

  @[hott] def group_pSet_of_Group [instance] [priority 900] (G : Group) :
    group (pSet_of_Group G) :=
  Group.struct G

  /- left and right actions -/
  @[hott] def is_equiv_mul_right {A : Group} (a : A) : is_equiv (λb, b * a) :=
  adjointify _ (λb : A, b * a⁻¹) (λb, !inv_mul_cancel_right) (λb, !mul_inv_cancel_right)

  @[hott] def right_action {A : Group} (a : A) : A ≃ A :=
  equiv.mk _ (is_equiv_mul_right a)

  @[hott] def is_equiv_add_right {A : AddGroup} (a : A) : is_equiv (λb, b + a) :=
  adjointify _ (λb : A, b - a) (λb, !neg_add_cancel_right) (λb, !add_neg_cancel_right)

  @[hott] def add_right_action {A : AddGroup} (a : A) : A ≃ A :=
  equiv.mk _ (is_equiv_add_right a)

  /- homomorphisms -/

  structure homomorphism (G₁ G₂ : Group) : Type _ :=
    (φ : G₁ → G₂)
    (p : is_mul_hom φ)

  infix ` →g `:55 := homomorphism

  abbreviation group_fun [coercion] [reducible] := @homomorphism.φ
  @[hott] def homomorphism.struct [instance] [priority 900] {G₁ G₂ : Group}
    (φ : G₁ →g G₂) : is_mul_hom φ :=
  homomorphism.p φ

  @[hott] def homomorphism.mulstruct [instance] [priority 2000] {G₁ G₂ : Group} (φ : G₁ →g G₂)
    : is_mul_hom φ :=
  homomorphism.p φ

  @[hott] def homomorphism.addstruct [instance] [priority 2000] {G₁ G₂ : AddGroup} (φ : G₁ →g G₂)
    : is_add_hom φ :=
  homomorphism.p φ

  variables {G G₁ G₂ G₃ : Group} {g h : G₁} {ψ : G₂ →g G₃} {φ₁ φ₂ : G₁ →g G₂} (φ : G₁ →g G₂)

  @[hott] def to_respect_mul /- φ -/ (g h : G₁) : φ (g * h) = φ g * φ h :=
  respect_mul φ g h

  @[hott] theorem to_respect_one /- φ -/ : φ 1 = 1 :=
  respect_one φ

  @[hott] theorem to_respect_inv /- φ -/ (g : G₁) : φ g⁻¹ = (φ g)⁻¹ :=
  respect_inv φ g

  @[hott] def to_is_embedding_homomorphism /- φ -/ (H : Π{g}, φ g = 1 → g = 1) : is_embedding φ :=
  is_embedding_of_is_mul_hom φ @H

  variables (G₁ G₂)
  @[hott] def is_set_homomorphism [instance] : is_set (G₁ →g G₂) :=
  begin
    have H : G₁ →g G₂ ≃ Σ(f : G₁ → G₂), Π(g₁ g₂ : G₁), f (g₁ * g₂) = f g₁ * f g₂,
    begin
      fapply equiv.MK,
      { intro φ, induction φ, constructor, exact (respect_mul φ)},
      { intro v, induction v with f H, constructor, exact H},
      { intro v, induction v, reflexivity},
      { intro φ, induction φ, reflexivity}
    end,
    apply is_trunc_equiv_closed_rev, exact H
  end

  variables {G₁ G₂}
  @[hott] def pmap_of_homomorphism /- φ -/ : G₁ →* G₂ :=
  pmap.mk φ begin esimp, exact respect_one φ end

  @[hott] def homomorphism_change_fun {G₁ G₂ : Group}
    (φ : G₁ →g G₂) (f : G₁ → G₂) (p : φ ~ f) : G₁ →g G₂ :=
  homomorphism.mk f
    (λg h, (p (g * h))⁻¹ ⬝ to_respect_mul φ g h ⬝ ap011 mul (p g) (p h))

  @[hott] def homomorphism_eq (p : φ₁ ~ φ₂) : φ₁ = φ₂ :=
  begin
    induction φ₁ with φ₁ q₁, induction φ₂ with φ₂ q₂, esimp at p, induction p,
    exact ap (homomorphism.mk φ₁) !is_prop.elim
  end

  section additive
  variables {H₁ H₂ : AddGroup} (χ : H₁ →g H₂)
  @[hott] def to_respect_add /- χ -/ (g h : H₁) : χ (g + h) = χ g + χ h :=
  respect_add χ g h

  @[hott] theorem to_respect_zero /- χ -/ : χ 0 = 0 :=
  respect_zero χ

  @[hott] theorem to_respect_neg /- χ -/ (g : H₁) : χ (-g) = -(χ g) :=
  respect_neg χ g

  end additive

  section add_mul
  variables {H₁ : AddGroup} {H₂ : Group} (χ : H₁ →g H₂)
  @[hott] def to_respect_add_mul /- χ -/ (g h : H₁) : χ (g + h) = χ g * χ h :=
  to_respect_mul χ g h

  @[hott] theorem to_respect_zero_one /- χ -/ : χ 0 = 1 :=
  to_respect_one χ

  @[hott] theorem to_respect_neg_inv /- χ -/ (g : H₁) : χ (-g) = (χ g)⁻¹ :=
  to_respect_inv χ g

  end add_mul

  section mul_add
  variables  {H₁ : Group} {H₂ : AddGroup} (χ : H₁ →g H₂)
  @[hott] def to_respect_mul_add /- χ -/ (g h : H₁) : χ (g * h) = χ g + χ h :=
  to_respect_mul χ g h

  @[hott] theorem to_respect_one_zero /- χ -/ : χ 1 = 0 :=
  to_respect_one χ

  @[hott] theorem to_respect_inv_neg /- χ -/ (g : H₁) : χ g⁻¹ = -(χ g) :=
  to_respect_inv χ g

  end mul_add

  /- categorical structure of groups + homomorphisms -/

  @[hott] def homomorphism_compose [trans] [reducible] (ψ : G₂ →g G₃) (φ : G₁ →g G₂) : G₁ →g G₃ :=
  homomorphism.mk (ψ ∘ φ) (is_mul_hom_compose _ _)

  variable (G)
  @[hott] def homomorphism_id [refl] : G →g G :=
  homomorphism.mk (@id G) (is_mul_hom_id G)
  variable {G}

  abbreviation gid := @homomorphism_id
  infixr ` ∘g `:75 := homomorphism_compose
  notation 1       := homomorphism_id _

  structure isomorphism (A B : Group) :=
    (to_hom : A →g B)
    (is_equiv_to_hom : is_equiv to_hom)

  infix ` ≃g `:25 := isomorphism
  attribute isomorphism.to_hom [coercion]
  attribute isomorphism.is_equiv_to_hom [instance]
  attribute isomorphism._trans_of_to_hom

  @[hott] def equiv_of_isomorphism (φ : G₁ ≃g G₂) : G₁ ≃ G₂ :=
  equiv.mk φ _

  @[hott] def pequiv_of_isomorphism (φ : G₁ ≃g G₂) :
    G₁ ≃* G₂ :=
  pequiv.mk φ begin esimp, exact _ end begin esimp, exact respect_one φ end

  @[hott] def isomorphism_of_equiv (φ : G₁ ≃ G₂)
    (p : Πg₁ g₂, φ (g₁ * g₂) = φ g₁ * φ g₂) : G₁ ≃g G₂ :=
  isomorphism.mk (homomorphism.mk φ p) !to_is_equiv

  @[hott] def isomorphism_of_eq {G₁ G₂ : Group} (φ : G₁ = G₂) : G₁ ≃g G₂ :=
  isomorphism_of_equiv (equiv_of_eq (ap Group.carrier φ))
    begin intros, induction φ, reflexivity end

  @[hott] def to_ginv (φ : G₁ ≃g G₂) : G₂ →g G₁ :=
  homomorphism.mk φ⁻¹
    abstract begin
    intros g₁ g₂, apply eq_of_fn_eq_fn' φ,
    rewrite [respect_mul φ, +right_inv φ]
    end end

  variable (G)
  @[hott] def isomorphism.refl [refl] : G ≃g G :=
  isomorphism.mk 1 !is_equiv_id
  variable {G}

  @[hott] def isomorphism.symm [symm] (φ : G₁ ≃g G₂) : G₂ ≃g G₁ :=
  isomorphism.mk (to_ginv φ) !is_equiv_inv

  @[hott] def isomorphism.trans [trans] (φ : G₁ ≃g G₂) (ψ : G₂ ≃g G₃) : G₁ ≃g G₃ :=
  isomorphism.mk (ψ ∘g φ) !is_equiv_compose

  @[hott] def isomorphism.eq_trans [trans]
     {G₁ G₂ : Group} {G₃ : Group} (φ : G₁ = G₂) (ψ : G₂ ≃g G₃) : G₁ ≃g G₃ :=
  proof isomorphism.trans (isomorphism_of_eq φ) ψ qed

  @[hott] def isomorphism.trans_eq [trans]
    {G₁ : Group} {G₂ G₃ : Group} (φ : G₁ ≃g G₂) (ψ : G₂ = G₃) : G₁ ≃g G₃ :=
  isomorphism.trans φ (isomorphism_of_eq ψ)

  postfix `⁻¹ᵍ`:(max + 1) := isomorphism.symm
  infixl ` ⬝g `:75 := isomorphism.trans
  infixl ` ⬝gp `:75 := isomorphism.trans_eq
  infixl ` ⬝pg `:75 := isomorphism.eq_trans

  @[hott] def pmap_of_isomorphism (φ : G₁ ≃g G₂) : G₁ →* G₂ :=
  pequiv_of_isomorphism φ

  @[hott] def to_fun_isomorphism_trans {G H K : Group} (φ : G ≃g H) (ψ : H ≃g K) :
    φ ⬝g ψ ~ ψ ∘ φ :=
  by reflexivity

  @[hott] def add_homomorphism (G H : AddGroup) : Type _ := homomorphism G H
  infix ` →a `:55 := add_homomorphism

  abbreviation agroup_fun [coercion] [reducible] {G H : AddGroup} (φ : G →a H) : G → H :=
  φ

  @[hott] def add_homomorphism.struct [instance] {G H : AddGroup} (φ : G →a H) : is_add_hom φ :=
  homomorphism.addstruct φ

  @[hott] def add_homomorphism.mk {G H : AddGroup} (φ : G → H) (h : is_add_hom φ) : G →g H :=
  homomorphism.mk φ h

  @[hott] def add_homomorphism_compose [trans] [reducible] {G₁ G₂ G₃ : AddGroup}
    (ψ : G₂ →a G₃) (φ : G₁ →a G₂) : G₁ →a G₃ :=
  add_homomorphism.mk (ψ ∘ φ) (is_add_hom_compose _ _)

  @[hott] def add_homomorphism_id [refl] (G : AddGroup) : G →a G :=
  add_homomorphism.mk (@id G) (is_add_hom_id G)

  abbreviation aid := @add_homomorphism_id
  infixr ` ∘a `:75 := add_homomorphism_compose

  @[hott] def to_respect_add' {H₁ H₂ : AddGroup} (χ : H₁ →a H₂) (g h : H₁) : χ (g + h) = χ g + χ h :=
  respect_add χ g h

  @[hott] theorem to_respect_zero' {H₁ H₂ : AddGroup} (χ : H₁ →a H₂) : χ 0 = 0 :=
  respect_zero χ

  @[hott] theorem to_respect_neg' {H₁ H₂ : AddGroup} (χ : H₁ →a H₂) (g : H₁) : χ (-g) = -(χ g) :=
  respect_neg χ g

  @[hott] def homomorphism_add {G H : AddAbGroup} (φ ψ : G →a H) : G →a H :=
  add_homomorphism.mk (λg, φ g + ψ g)
    abstract begin
      intros g g', refine ap011 add !to_respect_add' !to_respect_add' ⬝ _,
      refine !add.assoc ⬝ ap (add _) (!add.assoc⁻¹ ⬝ ap (λx, x + _) !add.comm ⬝ !add.assoc) ⬝ !add.assoc⁻¹
    end end

  @[hott] def homomorphism_mul {G H : AbGroup} (φ ψ : G →g H) : G →g H :=
  homomorphism.mk (λg, φ g * ψ g) (to_respect_add (homomorphism_add φ ψ))

  @[hott] def pmap_of_homomorphism_gid (G : Group) : pmap_of_homomorphism (gid G) ~* pid G :=
  begin
    fapply phomotopy_of_homotopy, reflexivity
  end

  @[hott] def pmap_of_homomorphism_gcompose {G H K : Group} (ψ : H →g K) (φ : G →g H)
    : pmap_of_homomorphism (ψ ∘g φ) ~* pmap_of_homomorphism ψ ∘* pmap_of_homomorphism φ :=
  begin
    fapply phomotopy_of_homotopy, reflexivity
  end

  @[hott] def pmap_of_homomorphism_phomotopy {G H : Group} {φ ψ : G →g H} (H : φ ~ ψ)
    : pmap_of_homomorphism φ ~* pmap_of_homomorphism ψ :=
  begin
    fapply phomotopy_of_homotopy, exact H
  end

  @[hott] def pequiv_of_isomorphism_trans {G₁ G₂ G₃ : Group} (φ : G₁ ≃g G₂) (ψ : G₂ ≃g G₂) :
    pequiv_of_isomorphism (φ ⬝g ψ) ~* pequiv_of_isomorphism ψ ∘* pequiv_of_isomorphism φ :=
  begin
    apply phomotopy_of_homotopy, reflexivity
  end

  @[hott] def isomorphism_eq {G H : Group} {φ ψ : G ≃g H} (p : φ ~ ψ) : φ = ψ :=
  begin
    induction φ with φ φe, induction ψ with ψ ψe,
    exact apd011 isomorphism.mk (homomorphism_eq p) !is_prop.elimo
  end

  @[hott] def is_set_isomorphism [instance] (G H : Group) : is_set (G ≃g H) :=
  begin
    have H : G ≃g H ≃ Σ(f : G →g H), is_equiv f,
    begin
      fapply equiv.MK,
      { intro φ, induction φ, constructor, assumption },
      { intro v, induction v, constructor, assumption },
      { intro v, induction v, reflexivity },
      { intro φ, induction φ, reflexivity }
    end,
    apply is_trunc_equiv_closed_rev, exact H
  end

  @[hott] def trivial_homomorphism (A B : Group) : A →g B :=
  homomorphism.mk (λa, 1) (λa a', (mul_one 1)⁻¹)

  @[hott] def trivial_add_homomorphism (A B : AddGroup) : A →a B :=
  homomorphism.mk (λa, 0) (λa a', (add_zero 0)⁻¹)


  /- given an equivalence A ≃ B we can transport a group structure on A to a group structure on B -/

  section

    parameters {A B : Type _} (f : A ≃ B) [group A]

    @[hott] def group_equiv_mul (b b' : B) : B := f (f⁻¹ᶠ b * f⁻¹ᶠ b')

    @[hott] def group_equiv_one : B := f one

    @[hott] def group_equiv_inv (b : B) : B := f (f⁻¹ᶠ b)⁻¹

    local infix * := group_equiv_mul
    local postfix ^ := group_equiv_inv
    local notation 1 := group_equiv_one

    @[hott] theorem group_equiv_mul_assoc (b₁ b₂ b₃ : B) : (b₁ * b₂) * b₃ = b₁ * (b₂ * b₃) :=
    by rewrite [↑group_equiv_mul, +left_inv f, mul.assoc]

    @[hott] theorem group_equiv_one_mul (b : B) : 1 * b = b :=
    by rewrite [↑group_equiv_mul, ↑group_equiv_one, left_inv f, one_mul, right_inv f]

    @[hott] theorem group_equiv_mul_one (b : B) : b * 1 = b :=
    by rewrite [↑group_equiv_mul, ↑group_equiv_one, left_inv f, mul_one, right_inv f]

    @[hott] theorem group_equiv_mul_left_inv (b : B) : b^ * b = 1 :=
    by rewrite [↑group_equiv_mul, ↑group_equiv_one, ↑group_equiv_inv,
                +left_inv f, mul.left_inv]

    @[hott] def group_equiv_closed : group B :=
    ⦃group,
      mul          := group_equiv_mul,
      mul_assoc    := group_equiv_mul_assoc,
      one          := group_equiv_one,
      one_mul      := group_equiv_one_mul,
      mul_one      := group_equiv_mul_one,
      inv          := group_equiv_inv,
      mul_left_inv := group_equiv_mul_left_inv,
    is_set_carrier := is_trunc_equiv_closed 0 f⦄

  end

  section
    variables {A B : Type _} (f : A ≃ B) [ab_group A]
    @[hott] def group_equiv_mul_comm (b b' : B) : group_equiv_mul f b b' = group_equiv_mul f b' b :=
    by rewrite [↑group_equiv_mul, mul.comm]

    @[hott] def ab_group_equiv_closed : ab_group B :=
    ⦃ab_group, group_equiv_closed f,
      mul_comm := group_equiv_mul_comm f⦄
  end

  variable (G)

  /- the trivial group -/
  open unit
  @[hott] def group_unit : group unit :=
  group.mk _ (λx y, star) (λx y z, idp) star (unit.rec idp) (unit.rec idp) (λx, star) (λx, idp)

  @[hott] def ab_group_unit : ab_group unit :=
  ⦃ab_group, group_unit, mul_comm := λx y, idp⦄

  @[hott] def trivial_group : Group :=
  Group.mk _ group_unit

  abbreviation G0 := trivial_group

  @[hott] def AbGroup_of_Group.{u} (G : Group.{u}) (H : Π x y : G, x * y = y * x) : AbGroup.{u} :=
  begin
    induction G,
    fapply AbGroup.mk,
    assumption,
    exact ⦃ab_group, struct', mul_comm := H⦄
  end

  @[hott] def trivial_ab_group : AbGroup.{0} :=
  begin
    fapply AbGroup_of_Group trivial_group, intros x y, reflexivity
  end

  @[hott] def trivial_group_of_is_contr [H : is_contr G] : G ≃g G0 :=
  begin
    fapply isomorphism_of_equiv,
    { apply equiv_unit_of_is_contr},
    { intros, reflexivity}
  end

  @[hott] def ab_group_of_is_contr (A : Type _) [is_contr A] : ab_group A :=
  have ab_group unit, from ab_group_unit,
  ab_group_equiv_closed (equiv_unit_of_is_contr A)⁻¹ᵉ

  @[hott] def group_of_is_contr (A : Type _) [is_contr A] : group A :=
  have ab_group A, from ab_group_of_is_contr A, by apply _

  @[hott] def ab_group_lift_unit : ab_group (lift unit) :=
  ab_group_of_is_contr (lift unit)

  @[hott] def trivial_ab_group_lift : AbGroup :=
  AbGroup.mk _ ab_group_lift_unit

  @[hott] def from_trivial_ab_group (A : AbGroup) : trivial_ab_group →g A :=
  trivial_homomorphism trivial_ab_group A

  @[hott] def is_embedding_from_trivial_ab_group (A : AbGroup) :
    is_embedding (from_trivial_ab_group A) :=
  begin
    fapply is_embedding_of_is_injective,
    intros x y p,
    induction x, induction y, reflexivity
  end

  @[hott] def to_trivial_ab_group (A : AbGroup) : A →g trivial_ab_group :=
  trivial_homomorphism A trivial_ab_group

  variable {G}

  /-
    A group where the point in the pointed type corresponds with 1 in the group.
    We need this structure when we are given a pointed type, and want to say that there is a group
    structure on it which is compatible with the point. This is used in chain complexes.
  -/
  structure pgroup [class] (X : Type*) extends semigroup X, has_inv X :=
    (pt_mul : Πa, mul pt a = a)
    (mul_pt : Πa, mul a pt = a)
    (mul_left_inv_pt : Πa, mul (inv a) a = pt)

  @[hott] def group_of_pgroup [reducible] [instance] (X : Type*) [H : pgroup X]
    : group X :=
  ⦃group, H,
          one := pt,
          one_mul := pgroup.pt_mul ,
          mul_one := pgroup.mul_pt,
          mul_left_inv := pgroup.mul_left_inv_pt⦄

  @[hott] def pgroup_of_group (X : Type*) [H : group X] (p : one = pt :> X) : pgroup X :=
  begin
    cases X with X x, esimp at *, induction p,
    exact ⦃pgroup, H,
            pt_mul := one_mul,
            mul_pt := mul_one,
            mul_left_inv_pt := mul.left_inv⦄
  end

  @[hott] def Group_of_pgroup (G : Type*) [pgroup G] : Group :=
  Group.mk G _

  @[hott] def pgroup_Group [instance] (G : Group) : pgroup G :=
  ⦃ pgroup, Group.struct G,
    pt_mul := one_mul,
    mul_pt := mul_one,
    mul_left_inv_pt := mul.left_inv ⦄

  -- infinity pgroups

  structure inf_pgroup [class] (X : Type*) extends inf_semigroup X, has_inv X :=
    (pt_mul : Πa, mul pt a = a)
    (mul_pt : Πa, mul a pt = a)
    (mul_left_inv_pt : Πa, mul (inv a) a = pt)

  @[hott] def inf_group_of_inf_pgroup [reducible] [instance] (X : Type*) [H : inf_pgroup X]
    : inf_group X :=
  ⦃inf_group, H,
          one := pt,
          one_mul := inf_pgroup.pt_mul ,
          mul_one := inf_pgroup.mul_pt,
          mul_left_inv := inf_pgroup.mul_left_inv_pt⦄

  @[hott] def inf_pgroup_of_inf_group (X : Type*) [H : inf_group X] (p : one = pt :> X) : inf_pgroup X :=
  begin
    cases X with X x, esimp at *, induction p,
    exact ⦃inf_pgroup, H,
            pt_mul := one_mul,
            mul_pt := mul_one,
            mul_left_inv_pt := mul.left_inv⦄
  end

  @[hott] def inf_Group_of_inf_pgroup (G : Type*) [inf_pgroup G] : InfGroup :=
  InfGroup.mk G _

  @[hott] def inf_pgroup_InfGroup [instance] (G : InfGroup) : inf_pgroup G :=
  ⦃ inf_pgroup, InfGroup.struct G,
    pt_mul := one_mul,
    mul_pt := mul_one,
    mul_left_inv_pt := mul.left_inv ⦄

  /- equality of groups and abelian groups -/

  @[hott] def group.to_has_mul {A : Type _} (H : group A) : has_mul A := _
  @[hott] def group.to_has_inv {A : Type _} (H : group A) : has_inv A := _
  @[hott] def group.to_has_one {A : Type _} (H : group A) : has_one A := _
  local attribute group.to_has_mul group.to_has_inv [coercion]

  universe variable l
  variables {A B : Type l}
  @[hott] def group_eq {G H : group A} (same_mul' : Π(g h : A), @mul A G g h = @mul A H g h)
    : G = H :=
  begin
    have foo : Π(g : A), @inv A G g = (@inv A G g * g) * @inv A H g,
      from λg, !mul_inv_cancel_right⁻¹,
    cases G with Gs Gm Gh1 G1 Gh2 Gh3 Gi Gh4,
    cases H with Hs Hm Hh1 H1 Hh2 Hh3 Hi Hh4,
    have same_mul : Gm = Hm, from eq_of_homotopy2 same_mul',
    cases same_mul,
    have same_one : G1 = H1, from calc
      G1 = Hm G1 H1 : Hh3
     ... = H1 : Gh2,
    have same_inv : Gi = Hi, from eq_of_homotopy (take g, calc
      Gi g = Hm (Hm (Gi g) g) (Hi g) : foo
       ... = Hm G1 (Hi g) : by rewrite Gh4
       ... = Hi g : Gh2),
    cases same_one, cases same_inv,
    have ps  : Gs  = Hs,  from !is_prop.elim,
    have ph1 : Gh1 = Hh1, from !is_prop.elim,
    have ph2 : Gh2 = Hh2, from !is_prop.elim,
    have ph3 : Gh3 = Hh3, from !is_prop.elim,
    have ph4 : Gh4 = Hh4, from !is_prop.elim,
    cases ps, cases ph1, cases ph2, cases ph3, cases ph4, reflexivity
  end

  @[hott] def group_pathover {G : group A} {H : group B} {p : A = B}
    (resp_mul : Π(g h : A), cast p (g * h) = cast p g * cast p h) : G =[p] H :=
  begin
    induction p,
    apply pathover_idp_of_eq, exact group_eq (resp_mul)
  end

  @[hott] def Group_eq_of_eq {G H : Group} (p : Group.carrier G = Group.carrier H)
    (resp_mul : Π(g h : G), cast p (g * h) = cast p g * cast p h) : G = H :=
  begin
    cases G with Gc G, cases H with Hc H,
    apply (apd011 Group.mk p),
    exact group_pathover resp_mul
  end

  @[hott] def Group_eq {G H : Group} (f : Group.carrier G ≃ Group.carrier H)
    (resp_mul : Π(g h : G), f (g * h) = f g * f h) : G = H :=
  Group_eq_of_eq (ua f) (λg h, !cast_ua ⬝ resp_mul g h ⬝ ap011 mul !cast_ua⁻¹ !cast_ua⁻¹)

  @[hott] def eq_of_isomorphism {G₁ G₂ : Group} (φ : G₁ ≃g G₂) : G₁ = G₂ :=
  Group_eq (equiv_of_isomorphism φ) (respect_mul φ)

  @[hott] def ab_group.to_has_mul {A : Type _} (H : ab_group A) : has_mul A := _
  local attribute ab_group.to_has_mul [coercion]

  @[hott] def ab_group_eq {A : Type _} {G H : ab_group A}
    (same_mul : Π(g h : A), @mul A G g h = @mul A H g h)
    : G = H :=
  begin
    have g_eq : @ab_group.to_group A G = @ab_group.to_group A H, from group_eq same_mul,
    cases G with Gs Gm Gh1 G1 Gh2 Gh3 Gi Gh4 Gh5,
    cases H with Hs Hm Hh1 H1 Hh2 Hh3 Hi Hh4 Hh5,
    have pm : Gm = Hm, from ap (@mul _ ∘ group.to_has_mul) g_eq,
    have pi : Gi = Hi, from ap (@inv _ ∘ group.to_has_inv) g_eq,
    have p1 : G1 = H1, from ap (@one _ ∘ group.to_has_one) g_eq,
    induction pm, induction pi, induction p1,
    have ps  : Gs  = Hs,  from !is_prop.elim,
    have ph1 : Gh1 = Hh1, from !is_prop.elim,
    have ph2 : Gh2 = Hh2, from !is_prop.elim,
    have ph3 : Gh3 = Hh3, from !is_prop.elim,
    have ph4 : Gh4 = Hh4, from !is_prop.elim,
    have ph5 : Gh5 = Hh5, from !is_prop.elim,
    induction ps, induction ph1, induction ph2, induction ph3, induction ph4, induction ph5,
    reflexivity
  end

  @[hott] def ab_group_pathover {A B : Type _} {G : ab_group A} {H : ab_group B} {p : A = B}
    (resp_mul : Π(g h : A), cast p (g * h) = cast p g * cast p h) : G =[p] H :=
  begin
    induction p,
    apply pathover_idp_of_eq, exact ab_group_eq (resp_mul)
  end

  @[hott] def AbGroup_eq_of_isomorphism {G₁ G₂ : AbGroup} (φ : G₁ ≃g G₂) : G₁ = G₂ :=
  begin
    induction G₁, induction G₂,
    apply apd011 AbGroup.mk (ua (equiv_of_isomorphism φ)),
    apply ab_group_pathover,
    intros g h, exact !cast_ua ⬝ respect_mul φ g h ⬝ ap011 mul !cast_ua⁻¹ !cast_ua⁻¹
  end

  @[hott] def trivial_group_of_is_contr' (G : Group) [H : is_contr G] : G = G0 :=
  eq_of_isomorphism (trivial_group_of_is_contr G)


end group
