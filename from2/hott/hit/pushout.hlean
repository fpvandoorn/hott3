/-
Copyright (c) 2015-16 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Ulrik Buchholtz, Jakob von Raumer

Declaration and properties of the pushout
-/

import .quotient types.sigma types.arrow_2

open quotient eq sum equiv is_trunc pointed

namespace pushout
section

parameters {TL BL TR : Type _} (f : TL → BL) (g : TL → TR)

  local abbreviation A := BL + TR
  inductive pushout_rel : A → A → Type _ :=
  | Rmk : Π(x : TL), pushout_rel (inl (f x)) (inr (g x))
  open pushout_rel
  local abbreviation R := pushout_rel

  @[hott] def pushout : Type _ := quotient R -- TODO: define this in root namespace

  parameters {f g}
  @[hott] def inl (x : BL) : pushout :=
  class_of R (inl x)

  @[hott] def inr (x : TR) : pushout :=
  class_of R (inr x)

  @[hott] def glue (x : TL) : inl (f x) = inr (g x) :=
  eq_of_rel pushout_rel (Rmk f g x)

  @[hott] protected def rec {P : pushout → Type _} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x))
      (y : pushout) : P y :=
  begin
    induction y,
    { cases a,
        apply Pinl,
        apply Pinr},
    { cases H, apply Pglue}
  end

  @[hott] protected def rec_on [reducible] {P : pushout → Type _} (y : pushout)
    (Pinl : Π(x : BL), P (inl x)) (Pinr : Π(x : TR), P (inr x))
    (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x)) : P y :=
  rec Pinl Pinr Pglue y

  @[hott] theorem rec_glue {P : pushout → Type _} (Pinl : Π(x : BL), P (inl x))
    (Pinr : Π(x : TR), P (inr x)) (Pglue : Π(x : TL), Pinl (f x) =[glue x] Pinr (g x))
      (x : TL) : apd (rec Pinl Pinr Pglue) (glue x) = Pglue x :=
  !rec_eq_of_rel

  @[hott] protected def elim {P : Type _} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (y : pushout) : P :=
  rec Pinl Pinr (λx, pathover_of_eq _ (Pglue x)) y

  @[hott] protected def elim_on [reducible] {P : Type _} (y : pushout) (Pinl : BL → P)
    (Pinr : TR → P) (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) : P :=
  elim Pinl Pinr Pglue y

  @[hott] theorem elim_glue {P : Type _} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) (x : TL)
    : ap (elim Pinl Pinr Pglue) (glue x) = Pglue x :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (glue x)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑pushout.elim,rec_glue],
  end

  @[hott] protected def elim_type (Pinl : BL → Type _) (Pinr : TR → Type _)
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) : pushout → Type _ :=
  quotient.elim_type (sum.rec Pinl Pinr)
    begin intros v v' r, induction r, apply Pglue end

  @[hott] protected def elim_type_on [reducible] (y : pushout) (Pinl : BL → Type _)
    (Pinr : TR → Type _) (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) : Type _ :=
  elim_type Pinl Pinr Pglue y

  @[hott] theorem elim_type_glue (Pinl : BL → Type _) (Pinr : TR → Type _)
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (x : TL)
    : transport (elim_type Pinl Pinr Pglue) (glue x) = Pglue x :=
  !elim_type_eq_of_rel_fn

  @[hott] theorem elim_type_glue_inv (Pinl : BL → Type _) (Pinr : TR → Type _)
    (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x)) (x : TL)
    : transport (elim_type Pinl Pinr Pglue) (glue x)⁻¹ = to_inv (Pglue x) :=
  !elim_type_eq_of_rel_inv

  @[hott] protected def rec_prop {P : pushout → Type _} [H : Πx, is_prop (P x)]
    (Pinl : Π(x : BL), P (inl x)) (Pinr : Π(x : TR), P (inr x)) (y : pushout) :=
  rec Pinl Pinr (λx, !is_prop.elimo) y

  @[hott] protected def elim_prop {P : Type _} [H : is_prop P] (Pinl : BL → P) (Pinr : TR → P)
    (y : pushout) : P :=
  elim Pinl Pinr (λa, !is_prop.elim) y

end
end pushout

attribute pushout.inl pushout.inr
attribute pushout.rec pushout.elim [recursor 10]
attribute pushout.elim_type
attribute pushout.rec_on pushout.elim_on
attribute pushout.elim_type_on

open sigma

namespace pushout

  variables {TL BL TR : Type _} (f : TL → BL) (g : TL → TR)

  @[hott] protected theorem elim_inl {P : Type _} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) {b b' : BL} (p : b = b')
    : ap (pushout.elim Pinl Pinr Pglue) (ap inl p) = ap Pinl p :=
  !ap_compose⁻¹

  @[hott] protected theorem elim_inr {P : Type _} (Pinl : BL → P) (Pinr : TR → P)
    (Pglue : Π(x : TL), Pinl (f x) = Pinr (g x)) {b b' : TR} (p : b = b')
    : ap (pushout.elim Pinl Pinr Pglue) (ap inr p) = ap Pinr p :=
  !ap_compose⁻¹

  /- The non-dependent universal property -/
  @[hott] def pushout_arrow_equiv (C : Type _)
    : (pushout f g → C) ≃ (Σ(i : BL → C) (j : TR → C), Πc, i (f c) = j (g c)) :=
  begin
    fapply equiv.MK,
    { intro f, exact ⟨λx, f (inl x), λx, f (inr x), λx, ap f (glue x)⟩},
    { intros v x, induction v with i w, induction w with j p, induction x,
        exact (i a), exact (j a), exact (p x)},
    { intro v, induction v with i w, induction w with j p, esimp,
      apply ap (λp, ⟨i, j, p⟩), apply eq_of_homotopy, intro x, apply elim_glue},
    { intro f, apply eq_of_homotopy, intro x, induction x: esimp,
      apply eq_pathover, apply hdeg_square, esimp, apply elim_glue},
  end

  /- glue squares -/
  @[hott] protected def glue_square {x x' : TL} (p : x = x')
    : square (glue x) (glue x') (ap inl (ap f p)) (ap inr (ap g p)) :=
  by cases p; apply vrefl

end pushout

open function sigma.ops

namespace pushout

  /- The flattening lemma -/
  section

    universe variable u
    parameters {TL BL TR : Type _} (f : TL → BL) (g : TL → TR)
               (Pinl : BL → Type u) (Pinr : TR → Type u)
               (Pglue : Π(x : TL), Pinl (f x) ≃ Pinr (g x))
    include Pglue

    local abbreviation A := BL + TR
    local abbreviation R : A → A → Type _ := pushout_rel f g
    local abbreviation P := pushout.elim_type Pinl Pinr Pglue

    local abbreviation F : sigma (Pinl ∘ f) → sigma Pinl :=
    λz, ⟨ f z.1 , z.2 ⟩

    local abbreviation G : sigma (Pinl ∘ f) → sigma Pinr :=
    λz, ⟨ g z.1 , Pglue z.1 z.2 ⟩

    @[hott] protected def flattening : sigma P ≃ pushout F G :=
    begin
      apply equiv.trans !quotient.flattening.flattening_lemma,
      fapply equiv.MK,
      { intro q, induction q with z z z' fr,
        { induction z with a p, induction a with x x,
          { exact inl ⟨x, p⟩ },
          { exact inr ⟨x, p⟩ } },
        { induction fr with a a' r p, induction r with x,
          exact glue ⟨x, p⟩ } },
      { intro q, induction q with xp xp xp,
        { exact class_of _ ⟨sum.inl xp.1, xp.2⟩ },
        { exact class_of _ ⟨sum.inr xp.1, xp.2⟩ },
        { apply eq_of_rel, constructor } },
      { intro q, induction q with xp xp xp: induction xp with x p,
        { apply ap inl, reflexivity },
        { apply ap inr, reflexivity },
        { unfold F, unfold G, apply eq_pathover,
          rewrite [ap_id,ap_compose' (quotient.elim _ _)],
          krewrite elim_glue, krewrite elim_eq_of_rel, apply hrefl } },
      { intro q, induction q with z z z' fr,
        { induction z with a p, induction a with x x,
          { reflexivity },
          { reflexivity } },
        { induction fr with a a' r p, induction r with x,
          esimp, apply eq_pathover,
          rewrite [ap_id,ap_compose' (pushout.elim _ _ _)],
          krewrite elim_eq_of_rel, krewrite elim_glue, apply hrefl } }
    end
  end

  -- Commutativity of pushouts
  section
  variables {TL BL TR : Type _} (f : TL → BL) (g : TL → TR)

  @[hott] protected def transpose : pushout f g → pushout g f :=
  begin
    intro x, induction x, apply inr a, apply inl a, apply !glue⁻¹
  end

  --TODO prove without krewrite?
  @[hott] protected def transpose_involutive (x : pushout f g) :
    pushout.transpose g f (pushout.transpose f g x) = x :=
  begin
      induction x, apply idp, apply idp,
      apply eq_pathover, refine _ ⬝hp !ap_id⁻¹,
      refine !(ap_compose (pushout.transpose _ _)) ⬝ph _, esimp[pushout.transpose],
      krewrite [elim_glue, ap_inv, elim_glue, inv_inv], apply hrfl
  end

  @[hott] protected def symm : pushout f g ≃ pushout g f :=
  begin
    fapply equiv.MK, do 2 exact !pushout.transpose,
    do 2 (intro x; apply pushout.transpose_involutive),
  end

  end

  -- Functoriality of pushouts
  section
    section lemmas
      variables {X : Type _} {x₀ x₁ x₂ x₃ : X}
                (p : x₀ = x₁) (q : x₁ = x₂) (r : x₂ = x₃)
      private @[hott] def is_equiv_functor_lemma₁
        : (r ⬝ ((p ⬝ q ⬝ r)⁻¹ ⬝ p)) = q⁻¹ :=
      by cases p; cases r; cases q; reflexivity

      private @[hott] def is_equiv_functor_lemma₂
        : (p ⬝ q ⬝ r)⁻¹ ⬝ (p ⬝ q) = r⁻¹ :=
      by cases p; cases r; cases q; reflexivity
    end lemmas

    variables {TL BL TR : Type _} {f : TL → BL} {g : TL → TR}
              {TL' BL' TR' : Type _} {f' : TL' → BL'} {g' : TL' → TR'}
              (tl : TL → TL') (bl : BL → BL') (tr : TR → TR')
              (fh : bl ∘ f ~ f' ∘ tl) (gh : tr ∘ g ~ g' ∘ tl)
    include fh gh

    @[hott] protected def functor : pushout f g → pushout f' g' :=
    begin
      intro x, induction x with a b z,
      { exact inl (bl a) },
      { exact inr (tr b) },
      { exact (ap inl (fh z)) ⬝ glue (tl z) ⬝ (ap inr (gh z)⁻¹) }
    end

    @[hott] protected def ap_functor_inl {x x' : BL} (p : x = x')
      : ap (pushout.functor tl bl tr fh gh) (ap inl p) = ap inl (ap bl p) :=
    by cases p; reflexivity

    @[hott] protected def ap_functor_inr {x x' : TR} (p : x = x')
      : ap (pushout.functor tl bl tr fh gh) (ap inr p) = ap inr (ap tr p) :=
    by cases p; reflexivity

    variables [ietl : is_equiv tl] [iebl : is_equiv bl] [ietr : is_equiv tr]
    include ietl iebl ietr

    open equiv is_equiv arrow
    @[hott] protected def is_equiv_functor [instance]
      : is_equiv (pushout.functor tl bl tr fh gh) :=
    adjointify
      (pushout.functor tl bl tr fh gh)
      (pushout.functor tl⁻¹ bl⁻¹ tr⁻¹
        (inv_commute_of_commute tl bl f f' fh)
        (inv_commute_of_commute tl tr g g' gh))
    abstract begin
      intro x', induction x' with a' b' z',
      { apply ap inl, apply right_inv },
      { apply ap inr, apply right_inv },
      { apply eq_pathover,
        rewrite [ap_id,ap_compose' (pushout.functor tl bl tr fh gh)],
        krewrite elim_glue,
        rewrite [ap_inv,ap_con,ap_inv],
        krewrite [pushout.ap_functor_inr], rewrite ap_con,
        krewrite [pushout.ap_functor_inl,elim_glue],
        apply transpose,
        apply move_top_of_right, apply move_top_of_left',
        krewrite [-(ap_inv inl),-ap_con,-(ap_inv inr),-ap_con],
        apply move_top_of_right, apply move_top_of_left',
        krewrite [-ap_con,-(ap_inv inl),-ap_con],
        rewrite ap_bot_inv_commute_of_commute,
        apply eq_hconcat (ap02 inl
          (is_equiv_functor_lemma₁
            (right_inv bl (f' z'))
            (ap f' (right_inv tl z')⁻¹)
            (fh (tl⁻¹ z'))⁻¹)),
        rewrite [ap_inv f',inv_inv],
        rewrite ap_bot_inv_commute_of_commute,
        refine hconcat_eq _ (ap02 inr
          (is_equiv_functor_lemma₁
            (right_inv tr (g' z'))
            (ap g' (right_inv tl z')⁻¹)
            (gh (tl⁻¹ z'))⁻¹))⁻¹,
        rewrite [ap_inv g',inv_inv],
        apply pushout.glue_square }
    end end
    abstract begin
      intro x, induction x with a b z,
      { apply ap inl, apply left_inv },
      { apply ap inr, apply left_inv },
      { apply eq_pathover,
        rewrite [ap_id,ap_compose'
          (pushout.functor tl⁻¹ bl⁻¹ tr⁻¹ _ _)
          (pushout.functor tl bl tr _ _)],
        krewrite elim_glue,
        rewrite [ap_inv,ap_con,ap_inv],
        krewrite [pushout.ap_functor_inr], rewrite ap_con,
        krewrite [pushout.ap_functor_inl,elim_glue],
        apply transpose,
        apply move_top_of_right, apply move_top_of_left',
        krewrite [-(ap_inv inl),-ap_con,-(ap_inv inr),-ap_con],
        apply move_top_of_right, apply move_top_of_left',
        krewrite [-ap_con,-(ap_inv inl),-ap_con],
        rewrite inv_commute_of_commute_top,
        apply eq_hconcat (ap02 inl
          (is_equiv_functor_lemma₂
            (ap bl⁻¹ (fh z))⁻¹
            (left_inv bl (f z))
            (ap f (left_inv tl z)⁻¹))),
        rewrite [ap_inv f,inv_inv],
        rewrite inv_commute_of_commute_top,
        refine hconcat_eq _ (ap02 inr
          (is_equiv_functor_lemma₂
            (ap tr⁻¹ (gh z))⁻¹
            (left_inv tr (g z))
            (ap g (left_inv tl z)⁻¹)))⁻¹,
        rewrite [ap_inv g,inv_inv],
        apply pushout.glue_square }
    end end

  end

  /- version giving the equivalence -/
  section
    variables {TL BL TR : Type _} (f : TL → BL) (g : TL → TR)
              {TL' BL' TR' : Type _} (f' : TL' → BL') (g' : TL' → TR')
              (tl : TL ≃ TL') (bl : BL ≃ BL') (tr : TR ≃ TR')
              (fh : bl ∘ f ~ f' ∘ tl) (gh : tr ∘ g ~ g' ∘ tl)
    include fh gh

    @[hott] protected def equiv : pushout f g ≃ pushout f' g' :=
    equiv.mk (pushout.functor tl bl tr fh gh) _
  end

  @[hott] def pointed_pushout [instance] {TL BL TR : Type _} [HTL : pointed TL]
    [HBL : pointed BL] [HTR : pointed TR] (f : TL → BL) (g : TL → TR) : pointed (pushout f g) :=
  pointed.mk (inl (point _))
end pushout open pushout

@[hott] def ppushout {TL BL TR : Type*} (f : TL →* BL) (g : TL →* TR) : Type* :=
pointed.mk' (pushout f g)

namespace pushout
  section
  parameters {TL BL TR : Type*} (f : TL →* BL) (g : TL →* TR)

  parameters {f g}
  @[hott] def pinl : BL →* ppushout f g :=
  pmap.mk inl idp

  @[hott] def pinr : TR →* ppushout f g :=
  pmap.mk inr ((ap inr (respect_pt g))⁻¹ ⬝ !glue⁻¹ ⬝ (ap inl (respect_pt f)))

  @[hott] def pglue (x : TL) : pinl (f x) = pinr (g x) := -- TODO do we need this?
  !glue

  end

  section
  variables {TL BL TR : Type*} (f : TL →* BL) (g : TL →* TR)

  @[hott] protected def psymm : ppushout f g ≃* ppushout g f :=
  begin
    fapply pequiv_of_equiv,
    { apply pushout.symm },
    { exact ap inr (respect_pt f)⁻¹ ⬝ !glue⁻¹ ⬝ ap inl (respect_pt g) }
  end

  end
end pushout
