import homotopy.join homotopy.smash types.nat.hott

open eq equiv trunc function bool join sphere sphere.ops prod
open pointed sigma smash is_trunc nat

namespace spherical_fibrations

  /- classifying type of spherical fibrations -/
  @[hott] def BG (n : ℕ) [is_succ n] : Type 1 :=
  Σ(X : Type), ∥ X ≃ S (pred n) ∥

  @[hott] def pointed_BG [instance] (n : ℕ) [is_succ n] : pointed (BG n) :=
  pointed.mk ⟨ S (pred n) , tr erfl ⟩

  @[hott] def pBG (n : ℕ) [is_succ n] : Type* := pointed.mk' (BG n)

  @[hott] def G (n : ℕ) [is_succ n] : Type 1 :=
  pt = pt :> BG n

  @[hott] def G_char (n : ℕ) [is_succ n] : G n ≃ (S (pred n) ≃ S (pred n)) :=
  calc
    G n ≃ Σ(p : pType.carrier (S (pred n)) = pType.carrier (S (pred n))), _ : sigma_eq_equiv
    ... ≃ (pType.carrier (S (pred n)) = pType.carrier (S (pred n))) : sigma_equiv_of_is_contr_right
    ... ≃ (S (pred n) ≃ S (pred n)) : eq_equiv_equiv

  @[hott] def mirror (n : ℕ) [is_succ n] : S (pred n) → G n :=
  begin
    intro v, apply to_inv (G_char n),
    exact sorry
  end

/-
  Can we give a fibration P : S n → Type _, P base = F n = Ω(BF n) = (S. n ≃* S. n)
  and total space sigma P ≃ G (n+1) = Ω(BG (n+1)) = (S n.+1 ≃ S .n+1)

  Yes, let eval : BG (n+1) → S n be the evaluation map
-/
  @[hott] def is_succ_1 [instance] : is_succ 1 := is_succ.mk 0

  @[hott] def S_of_BG (n : ℕ) : Ω(pBG (n+1)) → S n :=
  λ f, f..1 ▸ pt

  @[hott] def BG_succ (n : ℕ) [H : is_succ n] : BG n → BG (n+1) :=
  begin
    induction H with n,
    intro X, cases X with X p,
    refine sigma.mk (susp X) _, induction p with f, apply tr,
    exact susp.equiv f
  end

  /- classifying type of pointed spherical fibrations -/
  @[hott] def BF (n : ℕ) : Type 1 :=
  Σ(X : Type*), ∥ X ≃* S n ∥

  @[hott] def pointed_BF [instance] (n : ℕ) : pointed (BF n) :=
  pointed.mk ⟨ S n , tr pequiv.rfl ⟩

  @[hott] def pBF (n : ℕ) : Type* := pointed.mk' (BF n)

  @[hott] def BF_succ (n : ℕ) : BF n → BF (n+1) :=
  begin
    intro X, cases X with X p,
    apply sigma.mk (susp X), induction p with f, apply tr,
    apply susp.susp_pequiv f
  end

  @[hott] def BF_of_BG {n : ℕ} [H : is_succ n] : BG n → BF n :=
  begin
    induction H with n,
    intro X, cases X with X p,
    apply sigma.mk (pointed.MK (susp X) susp.north),
    induction p with f, apply tr,
    apply pequiv_of_equiv (susp.equiv f),
    reflexivity
  end

  @[hott] def BG_of_BF {n : ℕ} : BF n → BG (n + 1) :=
  begin
    intro X, cases X with X hX,
    apply sigma.mk (carrier X), induction hX with fX,
    apply tr, exact fX
  end

  @[hott] def BG_mul {n m : ℕ} [Hn : is_succ n] [Hm : is_succ m] (X : BG n) (Y : BG m) :
    BG (n + m) :=
  begin
    induction Hn with n, induction Hm with m,
    cases X with X pX, cases Y with Y pY,
    apply sigma.mk (join X Y),
    induction pX with fX, induction pY with fY,
    apply tr, rewrite [succ_add],
    exact join_equiv_join fX fY ⬝e join_sphere n m
  end

  @[hott] def BF_mul {n m : ℕ} (X : BF n) (Y : BF m) : BF (n + m) :=
  begin
    cases X with X hX, cases Y with Y hY,
    apply sigma.mk (smash X Y),
    induction hX with fX, induction hY with fY, apply tr,
    exact sorry -- needs smash.spheres : psmash (S. n) (S. m) ≃ S. (n + m)
  end

  @[hott] def BF_of_BG_mul (n m : ℕ) [is_succ n] [is_succ m] (X : BG n) (Y : BG m)
    : BF_of_BG (BG_mul X Y) = BF_mul (BF_of_BG X) (BF_of_BG Y) :=
  sorry

  -- Thom spaces
  namespace thom
    variables {X : Type _} {n : ℕ} (α : X → BF n)

    -- the canonical section of an F-object
    @[hott] protected def sec (x : X) : carrier (sigma.pr1 (α x)) :=
    Point _

    open pushout sigma

    @[hott] def thom_space : Type _ :=
    pushout (λx : X, ⟨x , thom.sec α x⟩) (const X unit.star)
  end thom

/-
  Things to do:
  - Orientability and orientations
    * Thom class u ∈ ~Hⁿ(Tξ)
    * eventually prove Thom-Isomorphism (Rudyak IV.5.7)
  - define BG∞ and BF∞ as colimits of BG n and BF n
  - Ω(BF n) = ΩⁿSⁿ₁ + ΩⁿSⁿ₋₁ (self-maps of degree ±1)
  - succ_BF n is (n - 2) connected (from Freudenthal)
  - pfiber (BG_of_BF n) ≃* S. n
  - π₁(BF n)=π₁(BG n)=ℤ/2ℤ
  - double covers BSG and BSF
  - O : BF n → BG 1 = Σ(A : Type _), ∥ A = bool ∥
  - BSG n = sigma O
  - π₁(BSG n)=π₁(BSF n)=O
  - BSO(n),
  - find BF' n : Type with BF' n ≃ BF n etc.
  - canonical bundle γₙ : ℝP(n) → ℝP∞=BO(1) → Type
     prove T(γₙ) = ℝP(n+1)
  - BG∞ = BF∞ (in fact = BGL₁(S), the group of units of the sphere spectrum)
  - clutching construction:
     any f : S n → SG(n)  gives S n.+1 → BSG(n)  (mut.mut. for O(n),SO(n),etc.)
  - all bundles on S 3 are trivial, incl. tangent bundle
  - Adams' result on vector fields on spheres:
     there are maximally ρ(n)-1 indep.sections of the tangent bundle of S (n-1)
     where ρ(n) is the n'th Radon-Hurwitz number.→
-/

-- tangent bundle on S 2:

  namespace two_sphere

    @[hott] def tau : S 2 → BG 2 :=
    begin
      intro v, induction v with x, do 2 exact pt,
      exact sorry
    end

  end two_sphere

end spherical_fibrations
