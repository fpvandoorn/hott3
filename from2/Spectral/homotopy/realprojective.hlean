-- Based on Buchholtz-Rijke: Real projective spaces in HoTT
-- Author: Ulrik Buchholtz

import homotopy.join

open eq nat susp pointed sigma is_equiv equiv fiber is_trunc trunc
  trunc_index is_conn bool unit join pushout

@[hott] def of_is_contr (A : Type _) : is_contr A → A := @center A

@[hott] def sigma_unit_left' (B : unit → Type _)
   : (Σx, B x) ≃ B star :=
begin
  fapply equiv.MK,
  { intro w, induction w with u b, induction u, exact b },
  { intro b, exact ⟨ star, b ⟩ },
  { intro b, reflexivity },
  { intro w, induction w with u b, induction u, reflexivity }
end

@[hott] def sigma_eq_equiv' {A : Type _} (B : A → Type _)
  (a₁ a₂ : A) (b₁ : B a₁) (b₂ : B a₂)
  : (⟨a₁, b₁⟩ = ⟨a₂, b₂⟩) ≃ (Σ(p : a₁ = a₂), p ▸ b₁ = b₂) :=
calc (⟨a₁, b₁⟩ = ⟨a₂, b₂⟩)
    ≃ Σ(p : a₁ = a₂), b₁ =[p] b₂  : sigma_eq_equiv
... ≃ Σ(p : a₁ = a₂), p ▸ b₁ = b₂
 : by apply sigma_equiv_sigma_right; intro e; apply pathover_equiv_tr_eq

@[hott] def dec_eq_is_prop [instance] (A : Type _) : is_prop (decidable_eq A) :=
begin
  apply is_prop.mk, intros h k,
  apply eq_of_homotopy, intro a,
  apply eq_of_homotopy, intro b,
  apply decidable.rec_on (h a b),
  { intro p, apply decidable.rec_on (k a b),
    { intro q, apply ap decidable.inl, apply is_set.elim },
    { intro q, exact absurd p q } },
  { intro p, apply decidable.rec_on (k a b),
    { intro q, exact absurd q p },
    { intro q, apply ap decidable.inr, apply is_prop.elim } }
end

@[hott] def dec_eq_bool : decidable_eq bool :=
begin
  intro a, induction a: intro b: induction b,
  { exact decidable.inl idp },
  { exact decidable.inr ff_ne_tt },
  { exact decidable.inr (λ p, ff_ne_tt p⁻¹) },
  { exact decidable.inl idp }
end

@[hott] def lemma_II_4 {A B : Type} (a : A) (b : B)
  (e f : A ≃ B) (p : e a = b) (q : f a = b)
  : (⟨e, p⟩ = ⟨f, q⟩) ≃ Σ (h : e ~ f), p = h a ⬝ q :=
calc (⟨e, p⟩ = ⟨f, q⟩)
    ≃ Σ (h : e = f), h ▸ p = q   : sigma_eq_equiv'
... ≃ Σ (h : e ~ f), p = h a ⬝ q :
begin
  apply sigma_equiv_sigma ((equiv_eq_char e f) ⬝e eq_equiv_homotopy),
  intro h, induction h, esimp, change (p = q) ≃ (p = idp ⬝ q),
  rewrite idp_con
end

-- the type of two-element types
structure BoolType :=
  (carrier : Type)
  (bool_eq_carrier : ∥ bool = carrier ∥)
attribute BoolType.carrier [coercion]

-- the basepoint
@[hott] def pointed_BoolType [instance] : pointed BoolType :=
pointed.mk (BoolType.mk bool (tr idp))

@[hott] def pBoolType : pType := pType.mk BoolType pt

@[hott] def BoolType.sigma_char : BoolType ≃ { X : Type | ∥ bool = X ∥ } :=
begin
  fapply equiv.MK: intro Xf: induction Xf with X f,
  { exact ⟨ X, f ⟩ }, { exact BoolType.mk X f },
  { esimp }, { esimp }
end

@[hott] def BoolType.eq_equiv_equiv (A B : BoolType)
  : (A = B) ≃ (A ≃ B) :=
calc (A = B)
    ≃ (BoolType.sigma_char A = BoolType.sigma_char B)
    : eq_equiv_fn_eq_of_equiv
... ≃ (BoolType.carrier A = BoolType.carrier B)
    : begin
        induction A with A p, induction B with B q,
        symmetry, esimp, apply equiv_subtype
      end
... ≃ (A ≃ B) : eq_equiv_equiv A B

@[hott] def lemma_II_3 {A B : BoolType} (a : A) (b : B)
  : (⟨A, a⟩ = ⟨B, b⟩) ≃ Σ (e : A ≃ B), e a = b :=
calc (⟨A, a⟩ = ⟨B, b⟩)
    ≃ Σ (e : A = B), e ▸ a = b : sigma_eq_equiv'
... ≃ Σ (e : A ≃ B), e a = b   :
    begin
      apply sigma_equiv_sigma
        (BoolType.eq_equiv_equiv A B),
      intro e, induction e, unfold BoolType.eq_equiv_equiv,
      induction A with A p, esimp
    end

@[hott] def theorem_II_2_lemma_1 (e : bool ≃ bool)
  (p : e tt = tt) : e ff = ff :=
sum.elim (dichotomy (e ff)) (λ q, q)
begin
  intro q, apply empty.elim, apply ff_ne_tt,
  apply to_inv (eq_equiv_fn_eq_of_equiv e ff tt),
  exact q ⬝ p⁻¹,
end

@[hott] def theorem_II_2_lemma_2 (e : bool ≃ bool)
  (p : e tt = ff) : e ff = tt :=
sum.elim (dichotomy (e ff))
begin
  intro q, apply empty.elim, apply ff_ne_tt,
  apply to_inv (eq_equiv_fn_eq_of_equiv e ff tt),
  exact q ⬝ p⁻¹
end
begin
  intro q, exact q
end

@[hott] def theorem_II_2 : is_contr (Σ (X : BoolType), X) :=
begin
  fapply is_contr.mk,
  { exact sigma.mk pt tt },
  { intro w, induction w with Xf x, induction Xf with X f,
    apply to_inv (lemma_II_3 tt x), apply of_is_contr,
    induction f with f, induction f, induction x,
    { apply is_contr.mk ⟨ equiv_bnot, idp ⟩,
      intro w, induction w with e p, symmetry,
      apply to_inv (lemma_II_4 tt ff e equiv_bnot p idp),
      fapply sigma.mk,
      { intro b, induction b,
        { exact theorem_II_2_lemma_2 e p },
        { exact p } },
      { reflexivity } },
    { apply is_contr.mk ⟨ erfl, idp ⟩,
      intro w, induction w with e p, symmetry,
      apply to_inv (lemma_II_4 tt tt e erfl p idp),
      fapply sigma.mk,
      { intro b, induction b,
        { exact theorem_II_2_lemma_1 e p },
        { exact p } },
      { reflexivity } } }
end

@[hott] def corollary_II_6 : Π A : BoolType, (pt = A) ≃ A :=
@total_space_method BoolType pt BoolType.carrier theorem_II_2 idp

@[hott] def is_conn_BoolType [instance] : is_conn 0 BoolType :=
begin
  apply is_contr.mk (tr pt),
  intro X, induction X with X, induction X with X p,
  induction p with p, induction p, reflexivity
end

@[hott] def bool_type_dec_eq : Π (A : BoolType), decidable_eq A :=
@is_conn.is_conn.elim -1 pBoolType is_conn_BoolType
    (λ A : BoolType, decidable_eq A) _ dec_eq_bool

@[hott] def alpha (A : BoolType) (x y : A) : bool :=
decidable.rec_on (bool_type_dec_eq A x y)
    (λ p, tt) (λ q, ff)

@[hott] def alpha_inv (a b : bool) : alpha pt a (alpha pt a b) = b :=
begin
  induction a: induction b: esimp
end

@[hott] def is_equiv_alpha [instance] : Π {A : BoolType} (a : A),
  is_equiv (alpha A a) :=
begin
  apply @is_conn.elim -1 pBoolType is_conn_BoolType
    (λ A : BoolType, Π a : A, is_equiv (alpha A a)),
  intro a,
  exact adjointify (alpha pt a) (alpha pt a) (alpha_inv a) (alpha_inv a)
end

@[hott] def alpha_equiv (A : BoolType) (a : A) : A ≃ bool :=
equiv.mk (alpha A a) (is_equiv_alpha a)

@[hott] def alpha_symm : Π (A : BoolType) (x y : A),
  alpha A x y = alpha A y x :=
begin
  apply @is_conn.elim -1 pBoolType is_conn_BoolType
    (λ A : BoolType, Π x y : A, alpha A x y = alpha A y x),
  intros x y, induction x: induction y: esimp
end

-- we define the type of types together with a line bundle
structure two_cover :=
  (carrier : Type)
  (cov : carrier → Type)
  (cov_eq : Π x : carrier, ∥ bool = cov x ∥ )
open two_cover

@[hott] def unit_two_cover : two_cover :=
two_cover.mk unit (λ u, bool) (λ u, tr idp)

open sigma.ops

@[hott] def two_cover_step (X : two_cover) : two_cover :=
begin
  fapply two_cover.mk,
  { exact pushout (@sigma.pr1 (carrier X) (cov X)) (λ x, star) },
  { fapply pushout.elim_type,
    { intro x, exact cov X x },
    { intro u, exact BoolType.carrier pt },
    { intro w, exact alpha_equiv
        (BoolType.mk (cov X w.1) (cov_eq X w.1)) w.2 } },
  { fapply pushout.rec,
    { intro x, exact cov_eq X x },
    { intro u, exact tr idp },
    { intro w, apply is_prop.elimo } }
end

@[hott] def realprojective_two_cover : ℕ → two_cover :=
nat.rec unit_two_cover (λ x, two_cover_step)

@[hott] def realprojective : ℕ → Type :=
λ n, carrier (realprojective_two_cover n)

@[hott] def realprojective_cov [reducible] (n : ℕ)
  : realprojective n → BoolType :=
λ x, BoolType.mk
  (cov (realprojective_two_cover n) x)
  (cov_eq (realprojective_two_cover n) x)

@[hott] def theorem_III_3_u [reducible] (n : ℕ)
  : (Σ (w : Σ x, realprojective_cov n x), realprojective_cov n w.1)
  ≃ (Σ x, realprojective_cov n x) × bool :=
calc  (Σ (w : Σ x, realprojective_cov n x), realprojective_cov n w.1)
    ≃ (Σ (w : Σ x, realprojective_cov n x), realprojective_cov n w.1)
  : sigma_assoc_comm_equiv
... ≃ Σ (w : Σ x, realprojective_cov n x), bool
  : @sigma_equiv_sigma_right (Σ x : realprojective n, realprojective_cov n x)
      (λ w, realprojective_cov n w.1) (λ w, bool)
      (λ w, alpha_equiv (realprojective_cov n w.1) w.2)
... ≃ (Σ x, realprojective_cov n x) × bool
  : equiv_prod

@[hott] def theorem_III_3 (n : ℕ)
  : sphere n ≃ sigma (realprojective_cov n) :=
begin
  induction n with n IH,
  { symmetry, apply sigma_unit_left },
  { apply equiv.trans (join_bool (sphere n))⁻¹ᵉ,
    apply equiv.trans (join_equiv_join erfl IH),
    symmetry, refine equiv.trans _ !join_symm,
    apply equiv.trans !pushout.flattening, esimp,
    fapply pushout.equiv,
    { unfold function.compose, exact theorem_III_3_u n},
    { reflexivity },
    { exact sigma_unit_left' (λ u, bool) },
    { unfold function.compose, esimp, intro w,
      induction w with w z, induction w with x y,
      reflexivity },
    { unfold function.compose, esimp, intro w,
      induction w with w z, induction w with x y,
      exact alpha_symm (realprojective_cov n x) y z } }
end
