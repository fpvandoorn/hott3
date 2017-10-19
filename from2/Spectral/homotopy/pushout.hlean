
import ..algebra.exactness homotopy.cofiber homotopy.wedge

open eq function is_trunc sigma prod lift is_equiv equiv pointed sum unit bool cofiber

namespace pushout

  section
    variables {TL BL TR : Type*} {f : TL →* BL} {g : TL →* TR}
              {TL' BL' TR' : Type*} {f' : TL' →* BL'} {g' : TL' →* TR'}
              (tl : TL ≃ TL') (bl : BL ≃* BL') (tr : TR ≃ TR')
              (fh : bl ∘ f ~ f' ∘ tl) (gh : tr ∘ g ~ g' ∘ tl)

    @[hott] def ppushout_functor (tl : TL → TL') (bl : BL →* BL') (tr : TR → TR')
      (fh : bl ∘ f ~ f' ∘ tl) (gh : tr ∘ g ~ g' ∘ tl) : ppushout f g →* ppushout f' g' :=
    begin
      fconstructor,
      { exact pushout.functor tl bl tr fh gh },
      { exact ap inl (respect_pt bl) },
    end

    @[hott] def ppushout_pequiv (tl : TL ≃ TL') (bl : BL ≃* BL') (tr : TR ≃ TR')
      (fh : bl ∘ f ~ f' ∘ tl) (gh : tr ∘ g ~ g' ∘ tl) : ppushout f g ≃* ppushout f' g' :=
    pequiv_of_equiv (pushout.equiv _ _ _ _ tl bl tr fh gh) (ap inl (respect_pt bl))

  end

  /-
    WIP: proving that satisfying the universal property of the pushout is equivalent to
    being equivalent to the pushout
  -/

  universe variables u₁ u₂ u₃ u₄
  variables {A : Type u₁} {B : Type u₂} {C : Type u₃} {D D' : Type u₄}
            {f : A → B} {g : A → C} {h : B → D} {k : C → D} (p : h ∘ f ~ k ∘ g)
            {h' : B → D'} {k' : C → D'} (p' : h' ∘ f ~ k' ∘ g)
            -- (f : A → B) (g : A → C) (h : B → D) (k : C → D)

  include p
  @[hott] def is_pushout : Type _ :=
  Π⦃X : Type max u₁ u₂ u₃ u₄⦄ (h' : B → X) (k' : C → X) (p' : h' ∘ f ~ k' ∘ g),
    is_contr (Σ(l : D → X) (v : l ∘ h ~ h' × l ∘ k ~ k'),
                 Πa, square (prod.pr1 v (f a)) (prod.pr2 v (g a)) (ap l (p a)) (p' a))

  @[hott] def cocone [reducible] (X : Type _) : Type _ :=
  Σ(v : (B → X) × (C → X)), prod.pr1 v ∘ f ~ prod.pr2 v ∘ g

  @[hott] def cocone_of_map (X : Type _) (l : D → X) : cocone p X :=
  ⟨(l ∘ h, l ∘ k), λa, ap l (p a)⟩

  -- @[hott] def cocone_of_map (X : Type _) (l : D → X) : Σ(h' : B → X) (k' : C → X),
  --   h' ∘ f ~ k' ∘ g :=
  -- ⟨l ∘ h, l ∘ k, λa, ap l (p a)⟩

  omit p

  @[hott] def is_pushout2 [reducible] : Type _ :=
  Π(X : Type max u₁ u₂ u₃ u₄), is_equiv (cocone_of_map p X)

  section
  open sigma.ops
  protected @[hott] def inv_left (H : is_pushout2 p) {X : Type _} (v : cocone p X) :
    (cocone_of_map p X)⁻¹ᶠ v ∘ h ~ prod.pr1 v.1 :=
  ap10 (ap prod.pr1 (right_inv (cocone_of_map p X) v)..1)

  protected @[hott] def inv_right (H : is_pushout2 p) {X : Type _} (v : cocone p X) :
    (cocone_of_map p X)⁻¹ᶠ v ∘ k ~ prod.pr2 v.1 :=
  ap10 (ap prod.pr2 (right_inv (cocone_of_map p X) v)..1)
  end

  section
    local attribute is_pushout [reducible]
    @[hott] def is_prop_is_pushout : is_prop (is_pushout p) :=
    _

    local attribute is_pushout2 [reducible]
    @[hott] def is_prop_is_pushout2 : is_prop (is_pushout2 p) :=
    _
  end

  @[hott] def ap_eq_apd10_ap {A B : Type _} {C : B → Type _} (f : A → Πb, C b) {a a' : A} (p : a = a') (b : B)
    : ap (λa, f a b) p = apd10 (ap f p) b :=
  by induction p; reflexivity

  variables (f g)
  @[hott] def is_pushout2_pushout : @is_pushout2 _ _ _ _ f g inl inr glue :=
  λX, to_is_equiv (pushout_arrow_equiv f g X ⬝e assoc_equiv_prod _)

  @[hott] def is_equiv_of_is_pushout2_simple {A B C D : Type u₁}
            {f : A → B} {g : A → C} {h : B → D} {k : C → D} (p : h ∘ f ~ k ∘ g)
            {h' : B → D'} {k' : C → D'} (p' : h' ∘ f ~ k' ∘ g)
 (H : is_pushout2 p) : D ≃ pushout f g :=
  begin
    fapply equiv.MK,
    { exact (cocone_of_map p _)⁻¹ᶠ ⟨(inl, inr), glue⟩ },
    { exact pushout.elim h k p },
    { intro x, exact sorry

},
    { apply ap10,
      apply eq_of_fn_eq_fn (equiv.mk _ (H D)),
      fapply sigma_eq,
      { esimp, fapply prod_eq,
          apply eq_of_homotopy, intro b,
          exact ap (pushout.elim h k p) (pushout.inv_left p H ⟨(inl, inr), glue⟩ b),
          apply eq_of_homotopy, intro c,
          exact ap (pushout.elim h k p) (pushout.inv_right p H ⟨(inl, inr), glue⟩ c) },
      { apply pi.pi_pathover_constant, intro a,
        apply eq_pathover,
        refine !ap_eq_apd10_ap ⬝ph _ ⬝hp !ap_eq_apd10_ap⁻¹,
        refine ap (λx, apd10 x _) (ap_compose (λx, x ∘ f) pr1 _ ⬝ ap02 _ !prod_eq_pr1) ⬝ph _
               ⬝hp ap (λx, apd10 x _) (ap_compose (λx, x ∘ g) pr2 _ ⬝ ap02 _ !prod_eq_pr2)⁻¹,
        refine apd10 !apd10_ap_precompose_dependent a ⬝ph _ ⬝hp apd10 !apd10_ap_precompose_dependent⁻¹ a,
        refine apd10 !apd10_eq_of_homotopy (f a) ⬝ph _ ⬝hp apd10 !apd10_eq_of_homotopy⁻¹ (g a),
        refine ap_compose (pushout.elim h k p) _ _ ⬝pv _,
        refine aps (pushout.elim h k p) _ ⬝vp (!elim_glue ⬝ !ap_id⁻¹),
        esimp,   exact sorry
        },
      }
  end


--   @[hott] def is_equiv_of_is_pushout2 (H : is_pushout2 p) : D ≃ pushout f g :=
--   begin
--     fapply equiv.MK,
--     { exact down.{_ u₄} ∘ (cocone_of_map p _)⁻¹ᶠ ⟨(up ∘ inl, up ∘ inr), λa, ap up (glue a)⟩ },
--     { exact pushout.elim h k p },
--     { intro x, exact sorry

-- },
--     { intro d, apply eq_of_fn_eq_fn (equiv_lift D), esimp, revert d,
--       apply ap10,
--       apply eq_of_fn_eq_fn (equiv.mk _ (H (lift.{_ (max u₁ u₂ u₃)} D))),
--       fapply sigma_eq,
--       { esimp, fapply prod_eq,
--           apply eq_of_homotopy, intro b, apply ap up, esimp,
--         exact ap (pushout.elim h k p ∘ down.{_ u₄})
--                    (pushout.inv_left p H ⟨(up ∘ inl, up ∘ inr), λa, ap up (glue a)⟩ b),

--         exact sorry },
--       { exact sorry },

--       -- note q := @eq_of_is_contr _ H''
--       --   ⟨up ∘ pushout.elim h k p ∘ down ∘ (center' H').1,
--       --    (λb, ap (up ∘ pushout.elim h k p ∘ down) (prod.pr1 (center' H').2 b),
--       --     λc, ap (up ∘ pushout.elim h k p ∘ down) (prod.pr2 (center' H').2 c))⟩
--       --   ⟨up, (λx, idp, λx, idp)⟩,
--       -- exact ap down (ap10 q..1 d)
--       }
--   end

  /- composing pushouts -/

  @[hott] def pushout_vcompose_to {A B C D : Type _} {f : A → B} {g : A → C} {h : B → D}
    (x : pushout h (@inl _ _ _ f g)) : pushout (h ∘ f) g :=
  begin
    induction x with d y b,
    { exact inl d },
    { induction y with b c a,
      { exact inl (h b) },
      { exact inr c },
      { exact glue a }},
    { reflexivity }
  end

  @[hott] def pushout_vcompose_from {A B C D : Type _} {f : A → B} {g : A → C} {h : B → D}
    (x : pushout (h ∘ f) g) : pushout h (@inl _ _ _ f g) :=
  begin
    induction x with d c a,
    { exact inl d },
    { exact inr (inr c) },
    { exact glue (f a) ⬝ ap inr (glue a) }
  end

  @[hott] def pushout_vcompose {A B C D : Type _} (f : A → B) (g : A → C) (h : B → D) :
    pushout h (@inl _ _ _ f g) ≃ pushout (h ∘ f) g :=
  begin
    fapply equiv.MK,
    { exact pushout_vcompose_to },
    { exact pushout_vcompose_from },
    { intro x, induction x with d c a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose pushout_vcompose_to _ _ ⬝ ap02 _ !elim_glue ⬝ _,
        refine !ap_con ⬝ !elim_glue ◾ !ap_compose'⁻¹ ⬝ !idp_con ⬝ _, esimp, apply elim_glue }},
    { intro x, induction x with d y b,
      { reflexivity },
      { induction y with b c a,
        { exact glue b },
        { reflexivity },
        { apply eq_pathover, refine ap_compose pushout_vcompose_from _ _ ⬝ph _,
          esimp, refine ap02 _ !elim_glue ⬝ !elim_glue ⬝ph _, apply square_of_eq, reflexivity }},
      { apply eq_pathover_id_right, esimp,
        refine ap_compose pushout_vcompose_from _ _ ⬝ ap02 _ !elim_glue ⬝ph _, apply square_of_eq,
        reflexivity }}
  end

  @[hott] def pushout_hcompose {A B C D : Type _} (f : A → B) (g : A → C) (h : C → D) :
    pushout (@inr _ _ _ f g) h ≃ pushout f (h ∘ g) :=
  calc
    pushout (@inr _ _ _ f g) h ≃ pushout h (@inr _ _ _ f g) : pushout.symm
      ... ≃ pushout h (@inl _ _ _ g f) :
              pushout.equiv _ _ _ _ erfl erfl (pushout.symm f g) (λa, idp) (λa, idp)
      ... ≃ pushout (h ∘ g) f : pushout_vcompose
      ... ≃ pushout f (h ∘ g) : pushout.symm


  @[hott] def pushout_vcompose_equiv {A B C D E : Type _} (f : A → B) {g : A → C} {h : B → D}
    {hf : A → D} {k : B → E} (e : E ≃ pushout f g) (p : k ~ e⁻¹ᵉ ∘ inl) (q : h ∘ f ~ hf) :
    pushout h k ≃ pushout hf g :=
  begin
    refine _ ⬝e pushout_vcompose f g h ⬝e _,
    { fapply pushout.equiv,
        reflexivity,
        reflexivity,
        exact e,
        reflexivity,
        exact homotopy_of_homotopy_inv_post e _ _ p },
    { fapply pushout.equiv,
        reflexivity,
        reflexivity,
        reflexivity,
        exact q,
        reflexivity },
  end

  @[hott] def pushout_hcompose_equiv {A B C D E : Type _} {f : A → B} (g : A → C) {h : C → E}
    {hg : A → E} {k : C → D} (e : D ≃ pushout f g) (p : k ~ e⁻¹ᵉ ∘ inr) (q : h ∘ g ~ hg) :
    pushout k h ≃ pushout f hg :=
  calc
    pushout k h ≃ pushout h k : pushout.symm
      ... ≃ pushout hg f : by exact pushout_vcompose_equiv _ (e ⬝e pushout.symm f g) p q
      ... ≃ pushout f hg : pushout.symm

  @[hott] def pushout_of_equiv_left_to {A B C : Type _} {f : A ≃ B} {g : A → C}
    (x : pushout f g) : C :=
  begin
    induction x with b c a,
    { exact g (f⁻¹ b) },
    { exact c },
    { exact ap g (left_inv f a) }
  end

  @[hott] def pushout_of_equiv_left {A B C : Type _} (f : A ≃ B) (g : A → C) :
    pushout f g ≃ C :=
  begin
    fapply equiv.MK,
    { exact pushout_of_equiv_left_to },
    { exact inr },
    { intro c, reflexivity },
    { intro x, induction x with b c a,
      { exact (glue (f⁻¹ b))⁻¹ ⬝ ap inl (right_inv f b) },
      { reflexivity },
      { apply eq_pathover_id_right, refine ap_compose inr _ _ ⬝ ap02 _ !elim_glue ⬝ph _,
        apply move_top_of_left, apply move_left_of_bot,
        refine ap02 _ (adj f _) ⬝ !ap_compose⁻¹ ⬝pv _ ⬝vp !ap_compose,
        apply natural_square_tr }}
  end

  @[hott] def pushout_of_equiv_right {A B C : Type _} (f : A → B) (g : A ≃ C) :
    pushout f g ≃ B :=
  calc
    pushout f g ≃ pushout g f : pushout.symm f g
            ... ≃ B           : pushout_of_equiv_left g f

  -- todo: define pushout.equiv (renamed to pushout_equiv_pushout) using this
  variables {A₁ B₁ C₁ A₂ B₂ C₂ A₃ B₃ C₃ : Type _} {f₁ : A₁ → B₁} {g₁ : A₁ → C₁}
    {f₂ : A₂ → B₂} {g₂ : A₂ → C₂} {f₃ : A₃ → B₃} {g₃ : A₃ → C₃}
    {h₂ : A₂ → A₃} {h₁ : A₁ → A₂}
    {i₂ : B₂ → B₃} {i₁ : B₁ → B₂}
    {j₂ : C₂ → C₃} {j₁ : C₁ → C₂}
    (p₂ : i₂ ∘ f₂ ~ f₃ ∘ h₂) (q₂ : j₂ ∘ g₂ ~ g₃ ∘ h₂)
    (p₁ : i₁ ∘ f₁ ~ f₂ ∘ h₁) (q₁ : j₁ ∘ g₁ ~ g₂ ∘ h₁)

  @[hott] def pushout_functor_compose :
    pushout.functor (h₂ ∘ h₁) (i₂ ∘ i₁) (j₂ ∘ j₁) (p₁ ⬝htyv p₂) (q₁ ⬝htyv q₂) ~
    pushout.functor h₂ i₂ j₂ p₂ q₂ ∘ pushout.functor h₁ i₁ j₁ p₁ q₁ :=
  begin
    intro x, induction x with b c a,
    { reflexivity },
    { reflexivity },
    { apply eq_pathover, apply hdeg_square, esimp,
      refine !elim_glue ⬝ whisker_right _ (!ap_con ⬝ !ap_compose'⁻¹ ◾ idp) ◾
        (ap02 _ !con_inv ⬝ !ap_con ⬝ whisker_left _ (ap02 _ !ap_inv⁻¹ ⬝ !ap_compose'⁻¹)) ⬝ _ ⬝
        (ap_compose (pushout.functor h₂ i₂ j₂ p₂ q₂) _ _ ⬝ ap02 _ !elim_glue)⁻¹,
      refine _ ⬝ (!ap_con ⬝ (!ap_con ⬝ !ap_compose'⁻¹ ◾ !elim_glue) ◾ !ap_compose'⁻¹)⁻¹ᵖ,
      refine !con.assoc⁻¹ ⬝ whisker_right _ _,
      exact whisker_right _ !con.assoc ⬝ !con.assoc }
  end

  variables {p₁ q₁}
  @[hott] def pushout_functor_homotopy_constant {p₁' : i₁ ∘ f₁ ~ f₂ ∘ h₁} {q₁' : j₁ ∘ g₁ ~ g₂ ∘ h₁}
    (p : p₁ ~ p₁') (q : q₁ ~ q₁') :
    pushout.functor h₁ i₁ j₁ p₁ q₁ ~ pushout.functor h₁ i₁ j₁ p₁' q₁' :=
  begin
    induction p, induction q, reflexivity
  end

  @[hott] def pushout_functor_homotopy {h₁ h₂ : A₁ → A₂} {i₁ i₂ : B₁ → B₂} {j₁ j₂ : C₁ → C₂}
    {p₁ : i₁ ∘ f₁ ~ f₂ ∘ h₁} {q₁ : j₁ ∘ g₁ ~ g₂ ∘ h₁}
    {p₂ : i₂ ∘ f₁ ~ f₂ ∘ h₂} {q₂ : j₂ ∘ g₁ ~ g₂ ∘ h₂}
    (r : h₁ ~ h₂) (s : i₁ ~ i₂) (t : j₁ ~ j₂)
    (u : r ⬝htyh p₁ ~ p₂ ⬝htyh s) (v : r ⬝htyh q₁ ~ q₂ ⬝htyh t) :
    pushout.functor h₁ i₁ j₁ p₁ q₁ ~ pushout.functor h₂ i₂ j₂ p₂ q₂ :=
  begin
    induction r, induction s, induction t, apply pushout_functor_homotopy_constant,
    { exact (rfl_hhconcat p₁)⁻¹ʰᵗʸ ⬝hty u ⬝hty hhconcat_rfl p₂ },
    exact (rfl_hhconcat q₁)⁻¹ʰᵗʸ ⬝hty v ⬝hty hhconcat_rfl q₂
  end

  /- pushout where one map is constant is a cofiber -/

  @[hott] def pushout_const_equiv_to {A B C : Type _} {f : A → B} {c₀ : C}
    (x : pushout f (const A c₀)) : cofiber (sum_functor f (const unit c₀)) :=
  begin
    induction x with b c a,
    { exact !cod (sum.inl b) },
    { exact !cod (sum.inr c) },
    { exact glue (sum.inl a) ⬝ (glue (sum.inr ⋆))⁻¹ }
  end

  @[hott] def pushout_const_equiv_from {A B C : Type _} {f : A → B} {c₀ : C}
    (x : cofiber (sum_functor f (const unit c₀))) : pushout f (const A c₀) :=
  begin
    induction x with v v,
    { induction v with b c, exact inl b, exact inr c },
    { exact inr c₀ },
    { induction v with a u, exact glue a, reflexivity }
  end

  @[hott] def pushout_const_equiv {A B C : Type _} (f : A → B) (c₀ : C) :
    pushout f (const A c₀) ≃ cofiber (sum_functor f (const unit c₀)) :=
  begin
    fapply equiv.MK,
    { exact pushout_const_equiv_to },
    { exact pushout_const_equiv_from },
    { intro x, induction x with v v,
      { induction v with b c, reflexivity, reflexivity },
      { exact glue (sum.inr ⋆) },
      { apply eq_pathover_id_right,
        refine ap_compose pushout_const_equiv_to _ _ ⬝ ap02 _ !elim_glue ⬝ph _,
        induction v with a u,
        { refine !elim_glue ⬝ph _, apply whisker_bl, exact hrfl },
        { induction u, exact square_of_eq idp }}},
    { intro x, induction x with c b a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose pushout_const_equiv_from _ _ ⬝ ap02 _ !elim_glue ⬝ _,
        refine !ap_con ⬝ !elim_glue ◾ (!ap_inv ⬝ !elim_glue⁻²) }}
  end

  /- wedge is the cofiber of the map 2 -> A + B -/

  -- move to sum
  @[hott] def sum_of_bool (A B : Type*) (b : bool) : A + B :=
  by induction b; exact sum.inl pt; exact sum.inr pt

  @[hott] def psum_of_pbool (A B : Type*) : pbool →* (A +* B) :=
  pmap.mk (sum_of_bool A B) idp

  -- move to wedge
  @[hott] def wedge_equiv_pushout_sum (A B : Type*) :
    wedge A B ≃ cofiber (sum_of_bool A B) :=
  begin
    refine pushout_const_equiv _ _ ⬝e _,
    fapply pushout.equiv,
      exact bool_equiv_unit_sum_unit⁻¹ᵉ,
      reflexivity,
      reflexivity,
      intro x, induction x: reflexivity,
      intro x, induction x with u u: induction u; reflexivity
  end

  section
  open prod.ops
  /- products preserve pushouts -/

  @[hott] def pushout_prod_equiv_to {A B C D : Type _} {f : A → B} {g : A → C}
    (xd : pushout f g × D) : pushout (prod_functor f (@id D)) (prod_functor g id) :=
  begin
    induction xd with x d, induction x with b c a,
    { exact inl (b, d) },
    { exact inr (c, d) },
    { exact glue (a, d) }
  end

  @[hott] def pushout_prod_equiv_from {A B C D : Type _} {f : A → B} {g : A → C}
    (x : pushout (prod_functor f (@id D)) (prod_functor g id)) : pushout f g × D :=
  begin
    induction x with bd cd ad,
    { exact (inl bd.1, bd.2) },
    { exact (inr cd.1, cd.2) },
    { exact prod_eq (glue ad.1) idp }
  end

  @[hott] def pushout_prod_equiv {A B C D : Type _} (f : A → B) (g : A → C) :
    pushout f g × D ≃ pushout (prod_functor f (@id D)) (prod_functor g id) :=
  begin
    fapply equiv.MK,
    { exact pushout_prod_equiv_to },
    { exact pushout_prod_equiv_from },
    { intro x, induction x with bd cd ad,
      { induction bd, reflexivity },
      { induction cd, reflexivity },
      { induction ad with a d, apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose pushout_prod_equiv_to _ _ ⬝ ap02 _ !elim_glue ⬝ _, esimp,
        exact !ap_prod_elim ⬝ !idp_con ⬝ !elim_glue }},
    { intro xd, induction xd with x d, induction x with b c a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        refine ap_compose (pushout_prod_equiv_from ∘ pushout_prod_equiv_to) _ _ ⬝ _,
        refine ap02 _ !ap_prod_mk_left ⬝ !ap_compose ⬝ _,
        refine ap02 _ (!ap_prod_elim ⬝ !idp_con ⬝ !elim_glue) ⬝ _,
        refine !elim_glue ⬝ !ap_prod_mk_left⁻¹ }}
  end
  end

  /- interaction of pushout and sums -/

  @[hott] def pushout_to_sum {A B C : Type _} {f : A → B} {g : A → C} (D : Type _) (c₀ : C)
    (x : pushout f g) : pushout (sum_functor f (@id D)) (sum.rec g (λd, c₀)) :=
  begin
    induction x with b c a,
    { exact inl (sum.inl b) },
    { exact inr c },
    { exact glue (sum.inl a) }
  end

  @[hott] def pushout_from_sum {A B C : Type _} {f : A → B} {g : A → C} (D : Type _) (c₀ : C)
    (x : pushout (sum_functor f (@id D)) (sum.rec g (λd, c₀))) : pushout f g :=
  begin
    induction x with x c x,
    { induction x with b d, exact inl b, exact inr c₀ },
    { exact inr c },
    { induction x with a d, exact glue a, reflexivity }
  end

  /- The pushout of B <-- A --> C is the same as the pushout of B + D <-- A + D --> C -/
  @[hott] def pushout_sum_cancel_equiv {A B C : Type _} (f : A → B) (g : A → C)
    (D : Type _) (c₀ : C) : pushout f g ≃ pushout (sum_functor f (@id D)) (sum.rec g (λd, c₀)) :=
  begin
    fapply equiv.MK,
    { exact pushout_to_sum D c₀ },
    { exact pushout_from_sum D c₀ },
    { intro x, induction x with x c x,
      { induction x with b d, reflexivity, esimp, exact (glue (sum.inr d))⁻¹ },
      { reflexivity },
      { apply eq_pathover_id_right,
        refine ap_compose (pushout_to_sum D c₀) _ _ ⬝ ap02 _ !elim_glue ⬝ph _,
        induction x with a d: esimp,
        { exact hdeg_square !elim_glue },
        { exact square_of_eq !con.left_inv }}},
    { intro x, induction x with b c a,
      { reflexivity },
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose (pushout_from_sum D c₀) _ _ ⬝ ap02 _ !elim_glue ⬝ !elim_glue }}
  end

end pushout

namespace pushout

variables {A A' B B' C C' : Type _} {f : A → B} {g : A → C} {f' : A' → B'} {g' : A' → C'}
@[hott] def sum_pushout_of_pushout_sum
  (x : pushout (sum_functor f f') (sum_functor g g')) : pushout f g ⊎ pushout f' g' :=
begin
  induction x with b c a,
  { exact sum_functor inl inl b },
  { exact sum_functor inr inr c },
  { induction a with a a', exact ap sum.inl (glue a), exact ap sum.inr (glue a') }
end

@[hott] def pushout_sum_of_sum_pushout
  (x : pushout f g ⊎ pushout f' g') : pushout (sum_functor f f') (sum_functor g g') :=
begin
  induction x with x x,
  { exact pushout.functor sum.inl sum.inl sum.inl homotopy.rfl homotopy.rfl x },
  { exact pushout.functor sum.inr sum.inr sum.inr homotopy.rfl homotopy.rfl x }
end

variables (f g f' g')
/-
  do we want to define this in terms of sigma_pushout? One possible disadvantage is that the
  computation on glue is less convenient
-/
@[hott] def pushout_sum_equiv_sum_pushout :
  pushout (sum_functor f f') (sum_functor g g') ≃ pushout f g ⊎ pushout f' g' :=
equiv.MK sum_pushout_of_pushout_sum pushout_sum_of_sum_pushout
  abstract begin
    intro x, induction x with x x,
    { induction x,
      { reflexivity },
      { reflexivity },
      apply eq_pathover, apply hdeg_square, esimp,
      exact ap_compose sum_pushout_of_pushout_sum _ _ ⬝
        ap02 _ (!elim_glue ⬝ !con_idp ⬝ !idp_con) ⬝ !elim_glue },
    { induction x,
      { reflexivity },
      { reflexivity },
      apply eq_pathover, apply hdeg_square, esimp,
      exact ap_compose sum_pushout_of_pushout_sum _ _ ⬝
        ap02 _ (!elim_glue ⬝ !con_idp ⬝ !idp_con) ⬝ !elim_glue },
  end end
  abstract begin
    intro x, induction x with b c a,
    { induction b: reflexivity },
    { induction c: reflexivity },
    { apply eq_pathover_id_right,
      refine ap_compose pushout_sum_of_sum_pushout _ _ ⬝ ap02 _ !elim_glue ⬝ph _,
      induction a with a a':
        (apply hdeg_square; refine !ap_compose'⁻¹ ⬝ !elim_glue ⬝ !con_idp ⬝ !idp_con) }
  end end

variables {f g f' g'}
variables {D E F D' E' F' : Type _} {h : D → E} {i : D → F} {h' : D' → E'} {i' : D' → F'}
  {j : A → D} {k : B → E} {l : C → F} {j' : A' → D'} {k' : B' → E'} {l' : C' → F'}
  {j₂ : A' → D} {k₂ : B' → E} {l₂ : C' → F}
  (s : hsquare f h j k) (t : hsquare g i j l)
  (s' : hsquare f' h' j' k') (t' : hsquare g' i' j' l')
  (s₂ : hsquare f' h j₂ k₂) (t₂ : hsquare g' i j₂ l₂)

@[hott] def sum_rec_pushout_sum_equiv_sum_pushout :
  sum.rec (pushout.functor j k l s t) (pushout.functor j₂ k₂ l₂ s₂ t₂) ∘
  pushout_sum_equiv_sum_pushout f g f' g' ~
  pushout.functor (sum.rec j j₂) (sum.rec k k₂) (sum.rec l l₂)
                  (sum_rec_hsquare s s₂) (sum_rec_hsquare t t₂) :=
begin
  intro x, induction x with b c a,
  { induction b with b b': reflexivity },
  { induction c with c c': reflexivity },
  { exact abstract begin apply eq_pathover,
    refine !ap_compose ⬝ ap02 _ !elim_glue ⬝ph _,
    induction a with a a': exact hdeg_square (!ap_compose'⁻¹ ⬝ !elim_glue ⬝ !elim_glue⁻¹)
    end end }
end

@[hott] def pushout_sum_equiv_sum_pushout_natural :
  hsquare
    (pushout.functor (j +→ j') (k +→ k') (l +→ l')
                     (sum_functor_hsquare s s') (sum_functor_hsquare t t'))
    (pushout.functor j k l s t +→ pushout.functor j' k' l' s' t')
    (pushout_sum_equiv_sum_pushout f g f' g')
    (pushout_sum_equiv_sum_pushout h i h' i') :=
begin
  intro x, induction x with b c a,
  { induction b with b b': reflexivity },
  { induction c with c c': reflexivity },
  { exact abstract begin apply eq_pathover,
    refine !ap_compose ⬝ ap02 _ !elim_glue ⬝ph _ ⬝hp (!ap_compose ⬝ ap02 _ !elim_glue)⁻¹,
    refine !ap_con ⬝ (!ap_con ⬝ !ap_compose'⁻¹ ◾ !elim_glue) ◾ (!ap_compose'⁻¹ ⬝ !ap_inv) ⬝ph _,
    induction a with a a',
    { apply hdeg_square, refine !ap_compose'⁻¹ ◾ idp ◾ !ap_compose'⁻¹⁻² ⬝ _ ⬝ !ap_compose',
      refine _ ⬝ (ap_compose sum.inl _ _ ⬝ ap02 _ !elim_glue)⁻¹,
      exact (ap_compose sum.inl _ _ ◾ idp ⬝ !ap_con⁻¹) ◾ (!ap_inv⁻¹ ⬝ ap_compose sum.inl _ _) ⬝
        !ap_con⁻¹ },
    { apply hdeg_square, refine !ap_compose'⁻¹ ◾ idp ◾ !ap_compose'⁻¹⁻² ⬝ _ ⬝ !ap_compose',
      refine _ ⬝ (ap_compose sum.inr _ _ ⬝ ap02 _ !elim_glue)⁻¹,
      exact (ap_compose sum.inr _ _ ◾ idp ⬝ !ap_con⁻¹) ◾ (!ap_inv⁻¹ ⬝ ap_compose sum.inr _ _) ⬝
        !ap_con⁻¹ } end end }
end

end pushout

namespace pushout
open sigma sigma.ops
variables {X : Type _} {A B C : X → Type _} {f : Πx, A x → B x} {g : Πx, A x → C x}
@[hott] def sigma_pushout_of_pushout_sigma
  (x : pushout (total f) (total g)) : Σx, pushout (f x) (g x) :=
begin
  induction x with b c a,
  { exact total (λx, inl) b },
  { exact total (λx, inr) c },
  { exact sigma_eq_right (glue a.2) }
end

@[hott] def pushout_sigma_of_sigma_pushout
  (x : Σx, pushout (f x) (g x)) : pushout (total f) (total g) :=
pushout.functor (dpair x.1) (dpair x.1) (dpair x.1) homotopy.rfl homotopy.rfl x.2

variables (f g)
@[hott] def pushout_sigma_equiv_sigma_pushout :
  pushout (total f) (total g) ≃ Σx, pushout (f x) (g x) :=
equiv.MK sigma_pushout_of_pushout_sigma pushout_sigma_of_sigma_pushout
  abstract begin
    intro x, induction x with x y, induction y with b c a,
    { reflexivity },
    { reflexivity },
    { apply eq_pathover, apply hdeg_square, esimp,
      exact ap_compose sigma_pushout_of_pushout_sigma _ _ ⬝
        ap02 _ (!elim_glue ⬝ !con_idp ⬝ !idp_con) ⬝ !elim_glue }
  end end
  abstract begin
    intro x, induction x with b c a,
    { induction b, reflexivity },
    { induction c, reflexivity },
    { apply eq_pathover_id_right,
      refine ap_compose pushout_sigma_of_sigma_pushout _ _ ⬝ ap02 _ !elim_glue ⬝ph _,
      induction a with a a',
        apply hdeg_square, refine !ap_compose'⁻¹ ⬝ !elim_glue ⬝ !con_idp ⬝ !idp_con }
  end end

variables {f g}
variables {X' : Type _} {A' B' C' : X' → Type _} {f' : Πx, A' x → B' x} {g' : Πx, A' x → C' x}
  {s : X → X'} {h₁ : Πx, A x → A' (s x)} {h₂ : Πx, B x → B' (s x)} {h₃ : Πx, C x → C' (s x)}
  (p : Πx, h₂ x ∘ f x ~ f' (s x) ∘ h₁ x) (q : Πx, h₃ x ∘ g x ~ g' (s x) ∘ h₁ x)


@[hott] def pushout_sigma_equiv_sigma_pushout_natural :
  hsquare
    (pushout.functor (sigma_functor s h₁) (sigma_functor s h₂) (sigma_functor s h₃)
      (λa, sigma_eq_right (p a.1 a.2)) (λa, sigma_eq_right (q a.1 a.2)))
    (sigma_functor s (λx, pushout.functor (h₁ x) (h₂ x) (h₃ x) (p x) (q x)))
    (pushout_sigma_equiv_sigma_pushout f g) (pushout_sigma_equiv_sigma_pushout f' g') :=
begin
  intro x, induction x with b c a,
  { reflexivity },
  { reflexivity },
  { exact abstract begin apply eq_pathover, apply hdeg_square,
    refine !ap_compose ⬝ ap02 _ !elim_glue ⬝ !ap_con ⬝
      (!ap_con ⬝ (!ap_compose'⁻¹ ⬝ !ap_compose'⁻¹) ◾ !elim_glue) ◾
      (!ap_compose'⁻¹ ⬝ ap02 _ !ap_inv⁻¹ ⬝ !ap_compose'⁻¹) ⬝ _,
    exact
      (ap_compose (sigma_functor s (λ x, pushout.functor (h₁ x) (h₂ x) (h₃ x) (p x) (q x))) _ _ ⬝
      ap02 _ !elim_glue ⬝ !ap_compose'⁻¹ ⬝ ap_compose (dpair _) _ _ ⬝ ap02 _ !elim_glue ⬝
      !ap_con ⬝ (!ap_con ⬝ !ap_compose'⁻¹ ◾ idp) ◾ !ap_compose'⁻¹)⁻¹ end end }
end


  /- an induction principle for the cofiber of f : A → B if A is a pushout where the second map has a section.
     The Pgluer is modified to get the right coherence
     See https://github.com/HoTT/HoTT-Agda/blob/master/theorems/homotopy/elims/CofPushoutSection.agda
  -/

  open sigma.ops
  @[hott] def cofiber_pushout_helper' {A : Type _} {B : A → Type _} {a₀₀ a₀₂ a₂₀ a₂₂ : A} {p₀₁ : a₀₀ = a₀₂}
    {p₁₀ : a₀₀ = a₂₀} {p₂₁ : a₂₀ = a₂₂} {p₁₂ : a₀₂ = a₂₂} {s : square p₀₁ p₂₁ p₁₀ p₁₂}
    {b₀₀ : B a₀₀} {b₂₀ : B a₂₀} {b₀₂ : B a₀₂} {b₂₂ b₂₂' : B a₂₂} {q₁₀ : b₀₀ =[p₁₀] b₂₀}
    {q₀₁ : b₀₀ =[p₀₁] b₀₂} {q₂₁ : b₂₀ =[p₂₁] b₂₂'} {q₁₂ : b₀₂ =[p₁₂] b₂₂} :
    Σ(r : b₂₂' = b₂₂), squareover B s q₀₁ (r ▸ q₂₁) q₁₀ q₁₂ :=
  begin
    induction s,
    induction q₀₁ using idp_rec_on,
    induction q₂₁ using idp_rec_on,
    induction q₁₀ using idp_rec_on,
    induction q₁₂ using idp_rec_on,
    exact ⟨idp, idso⟩
  end

  @[hott] def cofiber_pushout_helper {A B C D : Type _} {f : A → B} {g : A → C} {h : pushout f g → D}
    {P : cofiber h → Type _} {Pcod : Πd, P (cofiber.cod h d)} {Pbase : P (cofiber.base h)}
    (Pgluel : Π(b : B), Pcod (h (inl b)) =[cofiber.glue (inl b)] Pbase)
    (Pgluer : Π(c : C), Pcod (h (inr c)) =[cofiber.glue (inr c)] Pbase)
    (a : A) : Σ(p : Pbase = Pbase), squareover P (natural_square cofiber.glue (glue a))
      (Pgluel (f a)) (p ▸ Pgluer (g a))
      (pathover_ap P (λa, cofiber.cod h (h a)) (apd (λa, Pcod (h a)) (glue a)))
      (pathover_ap P (λa, cofiber.base h) (apd (λa, Pbase) (glue a))) :=
  !cofiber_pushout_helper'

  @[hott] def cofiber_pushout_rec {A B C D : Type _} {f : A → B} {g : A → C} {h : pushout f g → D}
    {P : cofiber h → Type _} (Pcod : Πd, P (cofiber.cod h d)) (Pbase : P (cofiber.base h))
    (Pgluel : Π(b : B), Pcod (h (inl b)) =[cofiber.glue (inl b)] Pbase)
    (Pgluer : Π(c : C), Pcod (h (inr c)) =[cofiber.glue (inr c)] Pbase)
    (r : C → A) (p : Πa, r (g a) = a)
    (x : cofiber h) : P x :=
  begin
    induction x with d x,
    { exact Pcod d },
    { exact Pbase },
    { induction x with b c a,
      { exact Pgluel b },
      { exact (cofiber_pushout_helper Pgluel Pgluer (r c)).1 ▸ Pgluer c },
      { apply pathover_pathover, rewrite [p a], exact (cofiber_pushout_helper Pgluel Pgluer a).2 }}
  end

  /- universal property of cofiber -/

  @[hott] def cofiber_exact_1 {X Y Z : Type*} (f : X →* Y) (g : pcofiber f →* Z) :
    (g ∘* pcod f) ∘* f ~* pconst X Z :=
  !passoc ⬝* pwhisker_left _ !pcod_pcompose ⬝* !pcompose_pconst

  protected @[hott] def pcofiber.elim {X Y Z : Type*} {f : X →* Y} (g : Y →* Z)
    (p : g ∘* f ~* pconst X Z) : pcofiber f →* Z :=
  begin
    fapply pmap.mk,
    { intro w, induction w with y x, exact g y, exact pt, exact p x },
    { reflexivity }
  end

  protected @[hott] def pcofiber.elim_pcod {X Y Z : Type*} {f : X →* Y} {g : Y →* Z}
    (p : g ∘* f ~* pconst X Z) : pcofiber.elim g p ∘* pcod f ~* g :=
  begin
    fapply phomotopy.mk,
    { intro y, reflexivity },
    { esimp, refine !idp_con ⬝ _,
      refine _ ⬝ (!ap_con ⬝ (!ap_compose'⁻¹ ⬝ !ap_inv) ◾ !elim_glue)⁻¹,
      apply eq_inv_con_of_con_eq, exact (to_homotopy_pt p)⁻¹ }
  end

  /-
    The maps  Z^{C_f} --> Z^Y --> Z^X  are exact at Z^Y.
    Here Y^X means pointed maps from X to Y and C_f is the cofiber of f.
    The maps are given by precomposing with (pcod f) and f.
  -/
  @[hott] def cofiber_exact {X Y Z : Type*} (f : X →* Y) :
    is_exact_t (@ppcompose_right _ _ Z (pcod f)) (ppcompose_right f) :=
  begin
    constructor,
    { intro g, apply eq_of_phomotopy, apply cofiber_exact_1 },
    { intros g p, note q := phomotopy_of_eq p,
      exact fiber.mk (pcofiber.elim g q) (eq_of_phomotopy (pcofiber.elim_pcod q)) }
  end

  /- cofiber of pcod is suspension -/

  @[hott] def pcofiber_pcod {A B : Type*} (f : A →* B) : pcofiber (pcod f) ≃* susp A :=
  begin
    fapply pequiv_of_equiv,
    { refine !pushout.symm ⬝e _,
      exact pushout_vcompose_equiv f equiv.rfl homotopy.rfl homotopy.rfl },
    reflexivity
  end

  -- @[hott] def pushout_vcompose {A B C D : Type _} (f : A → B) (g : A → C) (h : B → D) :
  --   pushout h (@inl _ _ _ f g) ≃ pushout (h ∘ f) g :=
  -- @[hott] def pushout_hcompose {A B C D : Type _} (f : A → B) (g : A → C) (h : C → D) :
  --   pushout (@inr _ _ _ f g) h ≃ pushout f (h ∘ g) :=

  -- @[hott] def pushout_vcompose_equiv {A B C D E : Type _} (f : A → B) {g : A → C} {h : B → D}
  --   {hf : A → D} {k : B → E} (e : E ≃ pushout f g) (p : k ~ e⁻¹ᵉ ∘ inl) (q : h ∘ f ~ hf) :
  --   pushout h k ≃ pushout hf g :=

end pushout

namespace pushout
  /- define the quotient using pushout -/
  section
  open quotient sigma.ops
  variables {A B : Type _} (R : A → A → Type _) {Q : B → B → Type _}
    (f : A → B) (k : Πa a' : A, R a a' → Q (f a) (f a'))

  @[hott] def pushout_quotient {A : Type _} (R : A → A → Type _) : Type _ :=
  @pushout ((Σa a', R a a') ⊎ (Σa a', R a a')) A (Σa a', R a a')
     (sum.rec pr1 (λx, x.2.1)) (sum.rec id id)

  variable {R}
  @[hott] def pushout_quotient_of_quotient (x : quotient R) : pushout_quotient R :=
  begin
    induction x with a a a' r,
    { exact inl a },
    { exact glue (sum.inl ⟨a, a', r⟩) ⬝ (glue (sum.inr ⟨a, a', r⟩))⁻¹ }
  end

  @[hott] def quotient_of_pushout_quotient (x : pushout_quotient R) : quotient R :=
  begin
    induction x with a x x,
    { exact class_of R a },
    { exact class_of R x.2.1 },
    { induction x with x x, exact eq_of_rel R x.2.2, reflexivity }
  end

  variable (R)
  @[hott] def quotient_equiv_pushout : quotient R ≃ pushout_quotient R :=
  equiv.MK pushout_quotient_of_quotient quotient_of_pushout_quotient
    abstract begin
      intro x, induction x with a x x,
      { reflexivity },
      { exact glue (sum.inr x) },
      { apply eq_pathover_id_right,
        refine ap_compose pushout_quotient_of_quotient _ _ ⬝ ap02 _ !elim_glue ⬝ph _,
        induction x with x x,
        { refine !elim_eq_of_rel ⬝ph _, induction x with a x, induction x with a' r,
          exact whisker_bl _ hrfl },
        { exact square_of_eq idp }}
    end end
    abstract begin
      intro x, induction x,
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square,
        refine ap_compose quotient_of_pushout_quotient _ _ ⬝ ap02 _ !elim_eq_of_rel ⬝ _,
        exact !ap_con ⬝ !elim_glue ◾ (!ap_inv ⬝ !elim_glue⁻²) }
    end end

  variable {R}
  @[hott] def sigma_functor2 : (Σ a a', R a a') → (Σ b b', Q b b') :=
  sigma_functor f (λa, sigma_functor f (k a))

  @[hott] def pushout_quotient_functor : pushout_quotient R → pushout_quotient Q :=
  let tf := sigma_functor2 f k in
  pushout.functor (sum_functor tf tf) f tf
    begin intro x, induction x: reflexivity end begin intro x, induction x: reflexivity end

  @[hott] def quotient_equiv_pushout_natural :
    hsquare (quotient.functor _ _ f k) (pushout_quotient_functor f k)
      (quotient_equiv_pushout R) (quotient_equiv_pushout Q) :=
  begin
    intro x, induction x with a a a' r,
    { reflexivity },
    { apply eq_pathover, apply hdeg_square,
      refine ap_compose pushout_quotient_of_quotient _ _ ⬝ _ ⬝
        (ap_compose (pushout.functor _ _ _ _ _) _ _)⁻¹,
      refine ap02 _ !elim_eq_of_rel ⬝ _ ⬝ (ap02 _ !elim_eq_of_rel)⁻¹,
      refine !elim_eq_of_rel ⬝ _,
      exact (!ap_con ⬝ (!pushout.elim_glue ⬝ !con_idp ⬝ !idp_con) ◾
             (!ap_inv ⬝ (!pushout.elim_glue ⬝ !con_idp ⬝ !idp_con)⁻²))⁻¹ }
  end


  end

end pushout
