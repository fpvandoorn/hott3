/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura
-/
prelude
import init.relation init.tactic init.funext

open eq

inductive acc.{l₁ l₂} {A : Type l₁} (R : A → A → Type l₂) : A → Type max l₁ l₂ :=
intro : ∀x, (∀ y, R y x → acc R y) → acc R x

namespace acc
  variables {A : Type _} {R : A → A → Type _}

  @[hott] def acc_eq {a : A} (H₁ H₂ : acc R a) : H₁ = H₂ :=
  begin
    induction H₁ with a K₁ IH₁,
    induction H₂ with a K₂ IH₂,
    apply eq.ap (intro a),
    apply eq_of_homotopy, intro a,
    apply eq_of_homotopy, intro r,
    apply IH₁
  end

  @[hott] def inv {x y : A} (H₁ : acc R x) (H₂ : R y x) : acc R y :=
  acc.rec_on H₁ (λ x₁ ac₁ iH H₂, ac₁ y H₂) H₂

  -- dependent elimination for acc
  protected @[hott] def drec [recursor]
      {C : Π (a : A), acc R a → Type _}
      (h₁ : Π (x : A) (acx : Π (y : A), R y x → acc R y),
              (Π (y : A) (ryx : R y x), C y (acx y ryx)) → C x (acc.intro x acx))
      {a : A} (h₂ : acc R a) : C a h₂ :=
  acc.rec h₁ h₂
end acc

inductive well_founded [class] {A : Type _} (R : A → A → Type _) : Type _ :=
intro : (Π a, acc R a) → well_founded R

namespace well_founded
  @[hott] def apply [coercion] {A : Type _} {R : A → A → Type _} (wf : well_founded R) : Πa, acc R a :=
  take a, well_founded.rec_on wf (λp, p) a

  section
  parameters {A : Type _} {R : A → A → Type _}
  local infix `≺`:50    := R

  hypothesis [Hwf : well_founded R]

  @[hott] theorem recursion {C : A → Type _} (a : A) (H : Πx, (Πy, y ≺ x → C y) → C x) : C a :=
  acc.rec_on (Hwf a) (λ x₁ ac₁ iH, H x₁ iH)

  @[hott] theorem induction {C : A → Type _} (a : A) (H : Πx, (Πy, y ≺ x → C y) → C x) : C a :=
  recursion a H

  variable {C : A → Type _}
  variable F : Πx, (Πy, y ≺ x → C y) → C x

  @[hott] def fix_F (x : A) (a : acc R x) : C x :=
  acc.rec_on a (λ x₁ ac₁ iH, F x₁ iH)

  @[hott] theorem fix_F_eq (x : A) (r : acc R x) :
    fix_F F x r = F x (λ (y : A) (p : y ≺ x), fix_F F y (acc.inv r p)) :=
  begin
    induction r using acc.drec,
    reflexivity -- proof is star due to proof irrelevance
  end
  end

  variables {A : Type _} {C : A → Type _} {R : A → A → Type _}

  -- Well-founded fixpoint
  @[hott] def fix [Hwf : well_founded R] (F : Πx, (Πy, R y x → C y) → C x) (x : A) : C x :=
  fix_F F x (Hwf x)

  -- Well-founded fixpoint satisfies fixpoint equation
  @[hott] theorem fix_eq [Hwf : well_founded R] (F : Πx, (Πy, R y x → C y) → C x) (x : A) :
    fix F x = F x (λy h, fix F y) :=
  begin
    refine fix_F_eq F x (Hwf x) ⬝ _,
    apply ap (F x),
    apply eq_of_homotopy, intro a,
    apply eq_of_homotopy, intro r,
    apply ap (fix_F F a),
    apply acc.acc_eq
  end
end well_founded

open well_founded

-- Empty relation is well-founded
@[hott] def empty.wf {A : Type _} : well_founded empty_relation :=
well_founded.intro (λ (a : A),
  acc.intro a (λ (b : A) (lt : empty), empty.rec _ lt))

-- Subrelation of a well-founded relation is well-founded
namespace subrelation
section
  universe variable u
  parameters {A : Type _} {R Q : A → A → Type _}
  parameters (H₁ : subrelation Q R)
  parameters (H₂ : well_founded R)

  @[hott] def accessible {a : A} (ac : acc R a) : acc Q a :=
  using H₁,
  begin
    induction ac with x ax ih, constructor,
    exact λ (y : A) (lt : Q y x), ih y (H₁ lt)
  end

  @[hott] def wf : well_founded Q :=
  using H₂,
  well_founded.intro (λ a, accessible proof (@apply A R H₂ a) qed)
end
end subrelation

-- The inverse image of a well-founded relation is well-founded
namespace inv_image
section
  parameters {A B : Type _} {R : B → B → Type _}
  parameters (f : A → B)
  parameters (H : well_founded R)

  private @[hott] def acc_aux {b : B} (ac : acc R b) : Π x, f x = b → acc (inv_image R f) x :=
  begin
    induction ac with x acx ih,
    intros z e, constructor,
    intros y lt, subst x,
    exact ih (f y) lt y rfl
  end

  @[hott] def accessible {a : A} (ac : acc R (f a)) : acc (inv_image R f) a :=
  acc_aux ac a rfl

  @[hott] def wf : well_founded (inv_image R f) :=
  well_founded.intro (λ a, accessible (H (f a)))
end
end inv_image

-- The transitive closure of a well-founded relation is well-founded
namespace tc
section
  parameters {A : Type _} {R : A → A → Type _}
  local notation `R⁺` := tc R

  @[hott] def accessible {z} (ac: acc R z) : acc R⁺ z :=
  begin
    induction ac with x acx ih,
    constructor, intros y rel,
    induction rel with a b rab a b c rab rbc ih₁ ih₂,
      {exact ih a rab},
      {exact acc.inv (ih₂ acx ih) rab}
  end

  @[hott] def wf (H : well_founded R) : well_founded R⁺ :=
  well_founded.intro (λ a, accessible (H a))
end
end tc

namespace nat

  -- less-than is well-founded
  @[hott] def lt.wf [instance] : well_founded (lt : ℕ → ℕ → Type) :=
  begin
    constructor, intro n, induction n with n IH,
    { constructor, intros n H, exfalso, exact !not_lt_zero H},
    { constructor, intros m H,
      have aux : ∀ {n₁} (hlt : m < n₁), succ n = n₁ → acc lt m,
        begin
          intros n₁ hlt, induction hlt,
          { intro p, injection p with q, exact q ▸ IH},
          { intro p, injection p with q, exact (acc.inv (q ▸ IH) a)}
        end,
      apply aux H rfl},
  end

  @[hott] def measure {A : Type _} : (A → ℕ) → A → A → Type :=
  inv_image lt

  @[hott] def measure.wf {A : Type _} (f : A → ℕ) : well_founded (measure f) :=
  inv_image.wf f lt.wf

end nat

namespace prod

  open well_founded prod.ops

  section
  variables {A B : Type _}
  variable  (Ra  : A → A → Type _)
  variable  (Rb  : B → B → Type _)

  -- Lexicographical order based on Ra and Rb
  inductive lex : A × B → A × B → Type _ :=
  | left  : ∀{a₁ b₁} a₂ b₂, Ra a₁ a₂ → lex (a₁, b₁) (a₂, b₂)
  | right : ∀a {b₁ b₂},     Rb b₁ b₂ → lex (a, b₁)  (a, b₂)

  -- Relational product based on Ra and Rb
  inductive rprod : A × B → A × B → Type _ :=
  intro : ∀{a₁ b₁ a₂ b₂}, Ra a₁ a₂ → Rb b₁ b₂ → rprod (a₁, b₁) (a₂, b₂)
  end

  section
  parameters {A B : Type _}
  parameters {Ra  : A → A → Type _} {Rb  : B → B → Type _}
  local infix `≺`:50 := lex Ra Rb

  @[hott] def lex.accessible {a} (aca : acc Ra a) (acb : ∀b, acc Rb b): ∀b, acc (lex Ra Rb) (a, b) :=
  acc.rec_on aca
    (λxa aca (iHa : ∀y, Ra y xa → ∀b, acc (lex Ra Rb) (y, b)),
      λb, acc.rec_on (acb b)
        (λxb acb
          (iHb : ∀y, Rb y xb → acc (lex Ra Rb) (xa, y)),
          acc.intro (xa, xb) (λp (lt : p ≺ (xa, xb)),
            have aux : xa = xa → xb = xb → acc (lex Ra Rb) p, from
              @prod.lex.rec_on A B Ra Rb (λp₁ p₂ h, pr₁ p₂ = xa → pr₂ p₂ = xb → acc (lex Ra Rb) p₁)
                               p (xa, xb) lt
                (λa₁ b₁ a₂ b₂ (H : Ra a₁ a₂) (eq₂ : a₂ = xa) (eq₃ : b₂ = xb),
                  show acc (lex Ra Rb) (a₁, b₁), from
                  have Ra₁  : Ra a₁ xa, from eq.rec_on eq₂ H,
                  iHa a₁ Ra₁ b₁)
                (λa b₁ b₂ (H : Rb b₁ b₂) (eq₂ : a = xa) (eq₃ : b₂ = xb),
                  show acc (lex Ra Rb) (a, b₁), from
                  have Rb₁  : Rb b₁ xb, from eq.rec_on eq₃ H,
                  have eq₂' : xa = a, from eq.rec_on eq₂ rfl,
                  eq.rec_on eq₂' (iHb b₁ Rb₁)),
            aux rfl rfl)))

  -- The lexicographical order of well founded relations is well-founded
  @[hott] def lex.wf (Ha : well_founded Ra) (Hb : well_founded Rb) : well_founded (lex Ra Rb) :=
  well_founded.intro (λp, destruct p (λa b, lex.accessible (Ha a) (well_founded.apply Hb) b))

  -- Relational product is a subrelation of the lex
  @[hott] def rprod.sub_lex : ∀ a b, rprod Ra Rb a b → lex Ra Rb a b :=
  λa b H, prod.rprod.rec_on H (λ a₁ b₁ a₂ b₂ H₁ H₂, lex.left Rb a₂ b₂ H₁)

  -- The relational product of well founded relations is well-founded
  @[hott] def rprod.wf (Ha : well_founded Ra) (Hb : well_founded Rb) : well_founded (rprod Ra Rb) :=
  subrelation.wf (rprod.sub_lex) (lex.wf Ha Hb)

  end

end prod
