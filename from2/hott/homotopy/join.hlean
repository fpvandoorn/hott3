/-
Copyright (c) 2015 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Ulrik Buchholtz

Declaration of a join as a special case of a pushout
-/

import hit.pushout .sphere cubical.cube

open eq function prod equiv is_trunc bool sigma.ops pointed

@[hott] def join (A B : Type _) : Type _ := @pushout.pushout (A × B) A B pr1 pr2

namespace join
  section
  variables {A B : Type _}

  @[hott] def inl (a : A) : join A B := @pushout.inl (A × B) A B pr1 pr2 a
  @[hott] def inr (b : B) : join A B := @pushout.inr (A × B) A B pr1 pr2 b

  @[hott] def glue (a : A) (b : B) : inl a = inr b :=
  @pushout.glue (A × B) A B pr1 pr2 (a, b)

  @[hott] protected def rec {P : join A B → Type _}
    (Pinl : Π(x : A), P (inl x))
    (Pinr : Π(y : B), P (inr y))
    (Pglue : Π(x : A)(y : B), Pinl x =[glue x y] Pinr y)
    (z : join A B) : P z :=
  pushout.rec Pinl Pinr (prod.rec Pglue) z

  @[hott] protected def rec_glue {P : join A B → Type _}
    (Pinl : Π(x : A), P (inl x))
    (Pinr : Π(y : B), P (inr y))
    (Pglue : Π(x : A)(y : B), Pinl x =[glue x y] Pinr y)
    (x : A) (y : B)
    : apd (join.rec Pinl Pinr Pglue) (glue x y) = Pglue x y :=
  !quotient.rec_eq_of_rel

  @[hott] protected def elim {P : Type _} (Pinl : A → P) (Pinr : B → P)
    (Pglue : Π(x : A)(y : B), Pinl x = Pinr y) (z : join A B) : P :=
  join.rec Pinl Pinr (λx y, pathover_of_eq _ (Pglue x y)) z

  @[hott] protected def elim_glue {P : Type _} (Pinl : A → P) (Pinr : B → P)
    (Pglue : Π(x : A)(y : B), Pinl x = Pinr y) (x : A) (y : B)
    : ap (join.elim Pinl Pinr Pglue) (glue x y) = Pglue x y :=
  begin
    apply equiv.eq_of_fn_eq_fn_inv !(pathover_constant (glue x y)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑join.elim],
    apply join.rec_glue
  end

  @[hott] protected def elim_ap_inl {P : Type _} (Pinl : A → P) (Pinr : B → P)
    (Pglue : Π(x : A)(y : B), Pinl x = Pinr y) {a a' : A} (p : a = a')
    : ap (join.elim Pinl Pinr Pglue) (ap inl p) = ap Pinl p :=
  by cases p; reflexivity

  @[hott] protected def hsquare {a a' : A} {b b' : B} (p : a = a') (q : b = b') :
    square (ap inl p) (ap inr q) (glue a b) (glue a' b') :=
  by induction p; induction q; exact hrfl

  @[hott] protected def vsquare {a a' : A} {b b' : B} (p : a = a') (q : b = b') :
    square (glue a b) (glue a' b') (ap inl p) (ap inr q) :=
  by induction p; induction q; exact vrfl

end

end join open join

@[hott] def pjoin (A B : Type*) : Type* := pointed.MK (join A B) (inl pt)

attribute join.inl join.inr
attribute join.rec [recursor]
attribute join.elim [recursor 7]
attribute join.rec join.elim

notation ` ★ `:40 := pjoin

/- Diamonds in joins -/
namespace join
  variables {A B : Type _}

  @[hott] protected def diamond (a a' : A) (b b' : B) :=
  square (glue a b) (glue a' b')⁻¹ (glue a b') (glue a' b)⁻¹

  @[hott] protected def hdiamond {a a' : A} (b b' : B) (p : a = a')
    : join.diamond a a' b b' :=
  begin
    cases p, unfold join.diamond,
    assert H : (glue a b' ⬝ (glue a b')⁻¹ ⬝ (glue a b)⁻¹⁻¹) = glue a b,
    { rewrite [con.right_inv,inv_inv,idp_con] },
    exact H ▸ top_deg_square (glue a b') (glue a b')⁻¹ (glue a b)⁻¹,
  end

  @[hott] protected def vdiamond (a a' : A) {b b' : B} (q : b = b')
    : join.diamond a a' b b' :=
  begin
    cases q, unfold join.diamond,
    assert H : (glue a b ⬝ (glue a' b)⁻¹ ⬝ (glue a' b)⁻¹⁻¹) = glue a b,
    { rewrite [con.assoc,con.right_inv] },
    exact H ▸ top_deg_square (glue a b) (glue a' b)⁻¹ (glue a' b)⁻¹
  end

  @[hott] protected def symm_diamond (a : A) (b : B)
    : join.vdiamond a a idp = join.hdiamond b b idp :=
  begin
    unfold join.hdiamond, unfold join.vdiamond,
    assert H : Π{X : Type _} ⦃x y : X⦄ (p : x = y),
      eq.rec (eq.rec (refl p) (symm (con.right_inv p⁻¹)))
             (symm (con.assoc p p⁻¹ p⁻¹⁻¹)) ▸ top_deg_square p p⁻¹ p⁻¹
    = eq.rec (eq.rec (eq.rec (refl p) (symm (idp_con p))) (symm (inv_inv p)))
             (symm (con.right_inv p)) ▸ top_deg_square p p⁻¹ p⁻¹
      :> square p p⁻¹ p p⁻¹,
    { intros X x y p, cases p, reflexivity },
   apply H (glue a b)
  end

end join

namespace join

  variables {A₁ A₂ B₁ B₂ : Type _}
  @[hott] def join_functor [reducible]
    (f : A₁ → A₂) (g : B₁ → B₂) : join A₁ B₁ → join A₂ B₂ :=
  begin
    intro x, induction x with a b a b,
    { exact inl (f a) }, { exact inr (g b) }, { apply glue }
  end

  @[hott] protected def ap_diamond (f : A₁ → A₂) (g : B₁ → B₂)
    {a a' : A₁} {b b' : B₁}
    : join.diamond a a' b b' → join.diamond (f a) (f a') (g b) (g b') :=
  begin
    unfold join.diamond, intro s,
    note s' := aps (join_functor f g) s,
    do 2 rewrite eq.ap_inv at s',
    do 4 rewrite join.elim_glue at s', exact s'
  end

  @[hott] def join_equiv_join
    : A₁ ≃ A₂ → B₁ ≃ B₂ → join A₁ B₁ ≃ join A₂ B₂ :=
  begin
    intros H K,
    fapply equiv.MK,
    { intro x, induction x with a b a b,
      { exact inl (to_fun H a) }, { exact inr (to_fun K b) },
      { apply glue } },
    { intro y, induction y with a b a b,
      { exact inl (to_inv H a) }, { exact inr (to_inv K b) },
      { apply glue } },
    { intro y, induction y with a b a b,
      { apply ap inl, apply to_right_inv },
      { apply ap inr, apply to_right_inv },
      { apply eq_pathover, rewrite ap_id,
        rewrite (ap_compose' (join.elim _ _ _)),
        do 2 krewrite join.elim_glue, apply join.hsquare } },
    { intro x, induction x with a b a b,
      { apply ap inl, apply to_left_inv },
      { apply ap inr, apply to_left_inv },
      { apply eq_pathover, rewrite ap_id,
        rewrite (ap_compose' (join.elim _ _ _)),
        do 2 krewrite join.elim_glue, apply join.hsquare } }
  end

  @[hott] protected def twist_diamond {A : Type _} {a a' : A} (p : a = a')
    : pathover (λx, join.diamond a' x a x)
        (join.vdiamond a' a idp) p
        (join.hdiamond a a' idp) :=
  begin
    cases p, apply pathover_idp_of_eq, apply join.symm_diamond
  end

  @[hott] def join_empty (A : Type _) : join empty A ≃ A :=
  begin
    fapply equiv.MK,
    { intro x, induction x with z a z a,
      { induction z },
      { exact a },
      { induction z } },
    { intro a, exact inr a },
    { intro a, reflexivity },
    { intro x, induction x with z a z a,
      { induction z },
      { reflexivity },
      { induction z } }
  end

  @[hott] def join_bool (A : Type _) : join bool A ≃ susp A :=
  begin
    fapply equiv.MK,
    { intro ba, induction ba with [b, a, b, a],
      { induction b, exact susp.south, exact susp.north },
      { exact susp.north },
      { induction b, esimp,
        { apply inverse, apply susp.merid, exact a },
        { reflexivity } } },
    { intro s, induction s with a,
      { exact inl tt },
      { exact inl ff },
      { exact (glue tt a) ⬝ (glue ff a)⁻¹ } },
    { intro s, induction s with a,
      { reflexivity },
      { reflexivity },
      { esimp, apply eq_pathover, rewrite ap_id,
        rewrite (ap_compose' (join.elim _ _ _)),
        rewrite [susp.elim_merid,ap_con,ap_inv],
        krewrite [join.elim_glue,join.elim_glue],
        esimp, rewrite [inv_inv,idp_con],
        apply hdeg_square, reflexivity } },
    { intro ba, induction ba with [b, a, b, a], esimp,
      { induction b, do 2 reflexivity },
      { apply glue },
      { induction b,
        { esimp, apply eq_pathover, rewrite ap_id,
          rewrite (ap_compose' (susp.elim _ _ _)),
          krewrite join.elim_glue, rewrite ap_inv,
          krewrite susp.elim_merid,
          apply square_of_eq_top, apply inverse,
          rewrite con.assoc, apply con.left_inv },
        { esimp, apply eq_pathover, rewrite ap_id,
          rewrite (ap_compose' (susp.elim _ _ _)),
          krewrite join.elim_glue, esimp,
          apply square_of_eq_top,
          rewrite [idp_con,con.right_inv] } } }
  end

end join

namespace join
  variables (A B C : Type _)

  @[hott] def is_contr_join [HA : is_contr A] :
    is_contr (join A B) :=
  begin
    fapply is_contr.mk, exact inl (center A),
    intro x, induction x with a b a b, apply ap inl, apply center_eq,
    apply glue, apply pathover_of_tr_eq,
    apply concat, apply eq_transport_Fr, esimp, rewrite ap_id,
    generalize center_eq a, intro p, cases p, apply idp_con,
  end

  @[hott] def join_swap : join A B → join B A :=
  begin
    intro x, induction x with a b a b, exact inr a, exact inl b,
    apply !glue⁻¹
  end

  @[hott] def join_swap_involutive (x : join A B) :
    join_swap B A (join_swap A B x) = x :=
  begin
    induction x with a b a b, do 2 reflexivity,
    apply eq_pathover, rewrite ap_id,
    apply hdeg_square,
    apply concat, apply ap_compose' (join.elim _ _ _),
    krewrite [join.elim_glue, ap_inv, join.elim_glue], apply inv_inv,
  end

  @[hott] def join_symm : join A B ≃ join B A :=
  by fapply equiv.MK; do 2 apply join_swap; do 2 apply join_swap_involutive

end join

/- This proves that the join operator is associative.
   The proof is more or less ported from Evan Cavallo's agda version:
   https://github.com/HoTT/HoTT-Agda/blob/master/homotopy/JoinAssocCubical.agda -/
namespace join

section join_switch

  private @[hott] def massage_sq' {A : Type _} {a₀₀ a₂₀ a₀₂ a₂₂ : A}
    {p₁₀ : a₀₀ = a₂₀} {p₁₂ :  a₀₂ = a₂₂} {p₀₁ : a₀₀ = a₀₂} {p₂₁ : a₂₀ = a₂₂}
    (sq : square p₁₀ p₁₂ p₀₁ p₂₁) : square p₁₀⁻¹ p₀₁⁻¹ (p₂₁ ⬝ p₁₂⁻¹) idp :=
  by induction sq; exact ids

  private @[hott] def massage_sq {A : Type _} {a₀₀ a₂₀ a₀₂ : A}
    {p₁₀ : a₀₀ = a₂₀} {p₁₂ :  a₀₂ = a₂₀} {p₀₁ : a₀₀ = a₀₂}
    (sq : square p₁₀ p₁₂ p₀₁ idp) : square p₁₀⁻¹ p₀₁⁻¹ p₁₂⁻¹ idp :=
  !idp_con⁻¹ ⬝ph (massage_sq' sq)

  private @[hott] def ap_square_massage {A B : Type _} (f : A → B) {a₀₀ a₀₂ a₂₀ : A}
    {p₀₁ : a₀₀ = a₀₂} {p₁₀ : a₀₀ = a₂₀} {p₁₁ : a₂₀ = a₀₂} (sq : square p₀₁ p₁₁ p₁₀ idp) :
    cube (hdeg_square (ap_inv f p₁₁)) ids
         (aps f (massage_sq sq)) (massage_sq (aps f sq))
         (hdeg_square !ap_inv) (hdeg_square !ap_inv) :=
  by apply rec_on_r sq; apply idc

  private @[hott] def massage_cube' {A : Type _} {a₀₀₀ a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₂₀₂ a₀₂₂ a₂₂₂ : A}
    {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂} {p₁₂₀ : a₀₂₀ = a₂₂₀}
    {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₂₀₁ : a₂₀₀ = a₂₀₂} {p₁₀₂ : a₀₀₂ = a₂₀₂} {p₀₁₂ : a₀₀₂ = a₀₂₂}
    {p₀₂₁ : a₀₂₀ = a₀₂₂} {p₁₂₂ : a₀₂₂ = a₂₂₂} {p₂₁₂ : a₂₀₂ = a₂₂₂} {p₂₂₁ : a₂₂₀ = a₂₂₂}
    {s₁₁₀ : square p₀₁₀ p₂₁₀ p₁₀₀ p₁₂₀} {s₁₁₂ : square p₀₁₂ p₂₁₂ p₁₀₂ p₁₂₂}
    {s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁} {s₂₁₁ : square p₂₁₀ p₂₁₂ p₂₀₁ p₂₂₁}
    {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ p₂₀₁} {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ p₂₂₁}
    (c : cube s₀₁₁ s₂₁₁ s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
    cube (s₂₁₁ ⬝v s₁₁₂⁻¹ᵛ) vrfl (massage_sq' s₁₀₁) (massage_sq' s₁₂₁) s₁₁₀⁻¹ᵛ s₀₁₁⁻¹ᵛ :=
  by cases c; apply idc

  private @[hott] def massage_cube {A : Type _} {a₀₀₀ a₂₀₀ a₀₂₀ a₂₂₀ a₀₀₂ a₀₂₂ : A}
    {p₁₀₀ : a₀₀₀ = a₂₀₀} {p₀₁₀ : a₀₀₀ = a₀₂₀} {p₀₀₁ : a₀₀₀ = a₀₀₂} {p₁₂₀ : a₀₂₀ = a₂₂₀}
    {p₂₁₀ : a₂₀₀ = a₂₂₀} {p₁₀₂ : a₀₀₂ = a₂₀₀} {p₀₁₂ : a₀₀₂ = a₀₂₂}
    {p₀₂₁ : a₀₂₀ = a₀₂₂} {p₁₂₂ : a₀₂₂ = a₂₂₀}
    {s₁₁₀ : square p₀₁₀ _ _ _} {s₁₁₂ : square p₀₁₂ p₂₁₀ p₁₀₂ p₁₂₂}
    {s₀₁₁ : square p₀₁₀ p₀₁₂ p₀₀₁ p₀₂₁} --{s₂₁₁ : square p₂₁₀ p₂₁₀ idp idp}
    {s₁₀₁ : square p₁₀₀ p₁₀₂ p₀₀₁ idp} {s₁₂₁ : square p₁₂₀ p₁₂₂ p₀₂₁ idp}
    (c : cube s₀₁₁ vrfl s₁₀₁ s₁₂₁ s₁₁₀ s₁₁₂) :
    cube s₁₁₂⁻¹ᵛ vrfl (massage_sq s₁₀₁) (massage_sq s₁₂₁) s₁₁₀⁻¹ᵛ s₀₁₁⁻¹ᵛ :=
  begin
    cases p₁₀₀, cases p₁₀₂, cases p₁₂₂, note c' := massage_cube' c, esimp[massage_sq],
    krewrite vdeg_v_eq_ph_pv_hp at c', exact c',
  end

  private @[hott] def massage_massage {A : Type _} {a₀₀ a₀₂ a₂₀ : A}
    {p₀₁ : a₀₀ = a₀₂} {p₁₀ : a₀₀ = a₂₀} {p₁₁ : a₂₀  = a₀₂} (sq : square p₀₁ p₁₁ p₁₀ idp) :
    cube (hdeg_square !inv_inv) ids (massage_sq (massage_sq sq))
      sq (hdeg_square !inv_inv) (hdeg_square !inv_inv) :=
  by apply rec_on_r sq; apply idc

  private @[hott] def square_Flr_ap_idp_cube {A B : Type _} {b : B} {f : A → B}
    {p₁ p₂ : Π a, f a = b} (α : Π a, p₁ a = p₂ a) {a₁ a₂ : A} (q : a₁ = a₂) :
    cube hrfl hrfl (square_Flr_ap_idp p₁ q) (square_Flr_ap_idp p₂ q)
      (hdeg_square (α _)) (hdeg_square (α _)) :=
  by cases q; esimp[square_Flr_ap_idp]; apply deg3_cube; esimp

  variables {A B C : Type _}

  @[hott] def switch_left [reducible] : join A B → join (join C B) A :=
  begin
    intro x, induction x with a b a b, exact inr a, exact inl (inr b), apply !glue⁻¹,
  end

  private @[hott] def switch_coh_fill_square (a : A) (b : B) (c : C) :=
  square (glue (inl c) a)⁻¹ (ap inl (glue c b))⁻¹ (ap switch_left (glue a b)) idp

  private @[hott] def switch_coh_fill_cube (a : A) (b : B) (c : C)
    (sq : switch_coh_fill_square a b c) :=
  cube (hdeg_square !join.elim_glue) ids
       sq (massage_sq !square_Flr_ap_idp)
       hrfl hrfl

  private @[hott] def switch_coh_fill_type (a : A) (b : B) (c : C) :=
  Σ sq : switch_coh_fill_square a b c, switch_coh_fill_cube a b c sq

  private @[hott] def switch_coh_fill (a : A) (b : B) (c : C)
    : switch_coh_fill_type a b c :=
  by esimp; apply cube_fill101

  private @[hott] def switch_coh (ab : join A B) (c : C) : switch_left ab = inl (inl c) :=
  begin
    induction ab with a b a b, apply !glue⁻¹, apply (ap inl !glue)⁻¹,
    apply eq_pathover, refine _ ⬝hp !ap_constant⁻¹,
    apply !switch_coh_fill.1,
  end

  @[hott] protected def switch [reducible] : join (join A B) C → join (join C B) A :=
  begin
    intro x, induction x with ab c ab c, exact switch_left ab, exact inl (inl c),
    exact switch_coh ab c,
  end

  private @[hott] def switch_inv_left_square (a : A) (b : B) :
    square idp idp (ap (!(@join.switch C) ∘ switch_left) (glue a b)) (ap inl (glue a b)) :=
  begin
    refine hdeg_square !ap_compose ⬝h _,
    refine aps join.switch (hdeg_square !join.elim_glue) ⬝h _, esimp,
    refine hdeg_square !(ap_inv join.switch) ⬝h _,
    refine hrfl⁻¹ʰ⁻¹ᵛ ⬝h _, esimp[join.switch,switch_left,switch_coh],
    refine (hdeg_square !join.elim_glue)⁻¹ᵛ ⬝h _, esimp,
    refine hrfl⁻¹ᵛ ⬝h _, apply hdeg_square !inv_inv,
  end

  private @[hott] def switch_inv_coh_left (c : C) (a : A) :
    square idp idp (ap !(@join.switch C B) (switch_coh (inl a) c)) (glue (inl a) c) :=
  begin
    refine hrfl ⬝h _,
    refine aps join.switch hrfl ⬝h _, esimp[switch_coh],
    refine hdeg_square !ap_inv ⬝h _,
    refine hrfl⁻¹ʰ⁻¹ᵛ ⬝h _, esimp[join.switch,switch_left],
    refine (hdeg_square !join.elim_glue)⁻¹ᵛ ⬝h _,
    refine hrfl⁻¹ᵛ ⬝h _, apply hdeg_square !inv_inv,
  end

  private @[hott] def switch_inv_coh_right (c : C) (b : B) :
    square idp idp (ap !(@join.switch _ _ A) (switch_coh (inr b) c)) (glue (inr b) c) :=
  begin
    refine hrfl ⬝h _,
    refine aps join.switch hrfl ⬝h _, esimp[switch_coh],
    refine hdeg_square !ap_inv ⬝h _,
    refine (hdeg_square !ap_compose)⁻¹ʰ⁻¹ᵛ ⬝h _,
    refine hrfl⁻¹ᵛ ⬝h _, esimp[join.switch,switch_left],
    refine (hdeg_square !join.elim_glue)⁻¹ᵛ ⬝h _, apply hdeg_square !inv_inv,
  end

  private @[hott] def switch_inv_left (ab : join A B) :
    !(@join.switch C) (join.switch (inl ab)) = inl ab :=
  begin
    induction ab with a b a b, do 2 reflexivity,
    apply eq_pathover, exact !switch_inv_left_square,
  end

  section
    variables (a : A) (b : B) (c : C)

    private @[hott] def switch_inv_cube_aux1 {A B C : Type _} {b : B} {f : A → B} (h : B → C)
      (g : Π a, f a = b) {x y : A} (p : x = y) :
      cube (hdeg_square (ap_compose h f p)) ids (square_Flr_ap_idp (λ a, ap h (g a)) p)
      (aps h (square_Flr_ap_idp _ _)) hrfl hrfl :=
    by cases p; esimp[square_Flr_ap_idp]; apply deg2_cube; cases (g x); esimp

    private @[hott] def switch_inv_cube_aux2 {A B : Type _} {b : B} {f : A → B}
      (g : Π a, f a = b) {x y : A} (p : x = y) {sq : square (g x) (g y) (ap f p) idp}
      (q : apd g p = eq_pathover (sq ⬝hp !ap_constant⁻¹)) : square_Flr_ap_idp _ _ = sq :=
    begin
      cases p, esimp at *, apply concat, apply inverse, apply vdeg_square_idp,
      apply concat, apply ap vdeg_square, exact ap eq_of_pathover_idp q,
      krewrite (is_equiv.right_inv (equiv.to_fun !pathover_idp)),
      exact is_equiv.left_inv (equiv.to_fun (vdeg_square_equiv _ _)) sq,
    end

    private @[hott] def switch_inv_cube (a : A) (b : B) (c : C) :
      cube (switch_inv_left_square a b) ids (square_Flr_ap_idp _ _)
      (square_Flr_ap_idp _ _) (switch_inv_coh_left c a) (switch_inv_coh_right c b) :=
    begin
      esimp [switch_inv_coh_left, switch_inv_coh_right, switch_inv_left_square],
      apply cube_concat2, apply switch_inv_cube_aux1,
      apply cube_concat2, apply cube_transport101, apply inverse,
        apply ap (λ x, aps join.switch x), apply switch_inv_cube_aux2, apply join.rec_glue,
        apply apc, apply (switch_coh_fill a b c).2,
      apply cube_concat2, esimp, apply ap_square_massage,
      apply cube_concat2, apply massage_cube, apply cube_inverse2, apply switch_inv_cube_aux1,
      apply cube_concat2, apply massage_cube, apply square_Flr_ap_idp_cube,
      apply cube_concat2, apply massage_cube, apply cube_transport101,
        apply inverse, apply switch_inv_cube_aux2,
        esimp[switch_coh], apply join.rec_glue, apply (switch_coh_fill c b a).2,
      apply massage_massage,
    end

  end

  private @[hott] def pathover_of_triangle_cube {A B : Type _} {b₀ b₁ : A → B}
    {b : B} {p₀₁ : Π a, b₀ a = b₁ a} {p₀ : Π a, b₀ a = b} {p₁ : Π a, b₁ a = b}
    {x y : A} {q : x = y} {sqx : square (p₀₁ x) idp (p₀ x) (p₁ x)}
    {sqy : square (p₀₁ y) idp (p₀ y) (p₁ y)}
    (c : cube (natural_square _ _) ids (square_Flr_ap_idp p₀ q) (square_Flr_ap_idp p₁ q)
       sqx sqy) :
    sqx =[q] sqy :=
  by cases q; apply pathover_of_eq_tr; apply eq_of_deg12_cube; exact c

  private @[hott] def pathover_of_ap_ap_square {A : Type _} {x y : A} {p : x = y}
    (g : B → A) (f : A → B) {u : g (f x) = x} {v : g (f y) = y}
    (sq : square (ap g (ap f p)) p u v) : u =[p] v :=
  by cases p; apply eq_pathover; apply transpose; exact sq

  private @[hott] def natural_square_beta {A B : Type _} {f₁ f₂ : A → B}
    (p : Π a, f₁ a = f₂ a) {x y : A} (q : x = y) {sq : square (p x) (p y) (ap f₁ q) (ap f₂ q)}
    (e : apd p q = eq_pathover sq) :
    natural_square p q = sq :=
  begin
    cases q, esimp at *, apply concat, apply inverse, apply vdeg_square_idp,
    apply concat, apply ap vdeg_square, apply ap eq_of_pathover_idp e,
    krewrite (is_equiv.right_inv (equiv.to_fun !pathover_idp)),
    exact is_equiv.left_inv (equiv.to_fun (vdeg_square_equiv _ _)) sq,
  end

  private @[hott] def switch_inv_coh (c : C) (k : join A B) :
    square (switch_inv_left k) idp (ap join.switch (switch_coh k c)) (glue k c) :=
  begin
    induction k with a b a b, apply switch_inv_coh_left, apply switch_inv_coh_right,
    refine pathover_of_triangle_cube _,
    esimp, apply cube_transport011,
    apply inverse, rotate 1, apply switch_inv_cube,
    apply natural_square_beta, apply join.rec_glue,
  end

  @[hott] protected def switch_involutive (x : join (join A B) C) :
    join.switch (join.switch x) = x :=
  begin
    induction x with ab c ab c, apply switch_inv_left, reflexivity,
    apply pathover_of_ap_ap_square join.switch join.switch,
    krewrite join.elim_glue, esimp,
    apply transpose, exact !switch_inv_coh,
  end

end join_switch

  @[hott] def join_switch_equiv (A B C : Type _) : join (join A B) C ≃ join (join C B) A :=
  by apply equiv.MK; do 2 apply join.switch_involutive

  @[hott] def join_assoc (A B C : Type _) : join (join A B) C ≃ join A (join B C) :=
  calc join (join A B) C ≃ join (join C B) A : join_switch_equiv
                     ... ≃ join A (join C B) : join_symm
                     ... ≃ join A (join B C) : join_equiv_join erfl (join_symm C B)

  @[hott] def ap_join_assoc_inv_glue_inl {A B : Type _} (C : Type _) (a : A) (b : B)
    : ap (to_inv (join_assoc A B C)) (glue a (inl b)) = ap inl (glue a b) :=
  begin
    unfold join_assoc, rewrite ap_compose, krewrite join.elim_glue,
    rewrite ap_compose, krewrite join.elim_glue, rewrite ap_inv, krewrite join.elim_glue,
    unfold switch_coh, unfold join_symm, unfold join_swap, esimp, rewrite inv_inv
  end

  @[hott] protected def ap_assoc_inv_glue_inr {A C : Type _} (B : Type _) (a : A) (c : C)
    : ap (to_inv (join_assoc A B C)) (glue a (inr c)) = glue (inl a) c :=
  begin
    unfold join_assoc, rewrite ap_compose, krewrite join.elim_glue,
    rewrite ap_compose, krewrite join.elim_glue, rewrite ap_inv, krewrite join.elim_glue,
    unfold switch_coh, unfold join_symm, unfold join_swap, esimp, rewrite inv_inv
  end

end join

namespace join

  open sphere sphere.ops

  @[hott] def join_susp (A B : Type _) : join (susp A) B ≃ susp (join A B) :=
  calc join (susp A) B
           ≃ join (join bool A) B
           : join_equiv_join (join_bool A)⁻¹ᵉ erfl
       ... ≃ join bool (join A B)
           : join_assoc
       ... ≃ susp (join A B)
           : join_bool (join A B)

  @[hott] def join_sphere (n m : ℕ) : join (S n) (S m) ≃ S (n+m+1) :=
  begin
    refine join_symm (S n) (S m) ⬝e _,
    induction m with m IH,
    { exact join_bool (S n) },
    { calc join (S (m+1)) (S n)
           ≃ susp (join (S m) (S n))
           : join_susp (S m) (S n)
       ... ≃ sphere (n+m+2)
           : susp.equiv IH }
  end

end join
