/-
Copyright (c) 2014-2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

Early library ported from Coq HoTT, but greatly extended since.
The basic definitions are in init.pointed

See also .pointed2
-/

import .nat.basic ..arity ..prop_trunc
open is_trunc eq prod sigma nat equiv option is_equiv bool unit sigma.ops sum algebra function

namespace pointed
  variables {A B : Type _}

  @[hott] def pointed_loop [instance] (a : A) : pointed (a = a) :=
  pointed.mk idp

  @[hott] def pointed_fun_closed (f : A → B) [H : pointed A] : pointed B :=
  pointed.mk (f pt)

  @[hott] def loop [reducible] (A : Type*) : Type* :=
  pointed.mk' (point A = point A)

  @[hott] def loopn [reducible] : ℕ → Type* → Type*
  | loopn  0    X := X
  | loopn (n+1) X := loop (loopn n X)

  notation `Ω` := loop
  notation `Ω[`:95 n:0 `]`:0 := loopn n

  namespace ops
    -- this is in a separate namespace because it caused type class inference to loop in some places
    @[hott] def is_trunc_pointed_MK [instance] [priority 1100] (n : ℕ₋₂) {A : Type _} (a : A)
      [H : is_trunc n A] : is_trunc n (pointed.MK A a) :=
    H
  end ops

  @[hott] def is_trunc_loop [instance] [priority 1100] (A : Type*)
    (n : ℕ₋₂) [H : is_trunc (n.+1) A] : is_trunc n (Ω A) :=
  !is_trunc_eq

  @[hott] def loopn_zero_eq (A : Type*)
    : Ω[0] A = A := rfl

  @[hott] def loopn_succ_eq (k : ℕ) (A : Type*)
    : Ω[succ k] A = Ω (Ω[k] A) := rfl

  @[hott] def rfln  [reducible] {n : ℕ} {A : Type*} : Ω[n] A := pt
  @[hott] def refln [reducible] (n : ℕ) (A : Type*) : Ω[n] A := pt
  @[hott] def refln_eq_refl (A : Type*) (n : ℕ) : rfln = rfl :> Ω[succ n] A := rfl

  @[hott] def loopn_space (A : Type _) [H : pointed A] (n : ℕ) : Type _ :=
  Ω[n] (pointed.mk' A)

  @[hott] def loop_mul {k : ℕ} {A : Type*} (mul : A → A → A) : Ω[k] A → Ω[k] A → Ω[k] A :=
  begin cases k with k, exact mul, exact concat end

  @[hott] def pType_eq {A B : Type*} (f : A ≃ B) (p : f pt = pt) : A = B :=
  begin
    cases A with A a, cases B with B b, esimp at *,
    fapply apdt011 @pType.mk,
    { apply ua f},
    { rewrite [cast_ua, p]},
  end

  @[hott] def pType_eq_elim {A B : Type*} (p : A = B :> Type*)
    : Σ(p : carrier A = carrier B :> Type _), Point A =[p] Point B :=
  by induction p; exact ⟨idp, idpo⟩

  @[hott] protected def pType.sigma_char.{u} : pType.{u} ≃ Σ(X : Type u), X :=
  begin
    fapply equiv.MK,
    { intro x, induction x with X x, exact ⟨X, x⟩},
    { intro x, induction x with X x, exact pointed.MK X x},
    { intro x, induction x with X x, reflexivity},
    { intro x, induction x with X x, reflexivity},
  end

  @[hott] def pType.eta_expand (A : Type*) : Type* :=
  pointed.MK A pt

  @[hott] def add_point (A : Type _) : Type* :=
  pointed.Mk (none : option A)
  postfix `₊`:(max+1) := add_point
  -- the inclusion A → A₊ is called "some", the extra point "pt" or "none" ("@none A")
end pointed

namespace pointed
  /- truncated pointed types -/
  @[hott] def ptrunctype_eq {n : ℕ₋₂} {A B : n-Type*}
    (p : A = B :> Type _) (q : Point A =[p] Point B) : A = B :=
  begin
    induction A with A HA a, induction B with B HB b, esimp at *,
    induction q, esimp,
    refine ap010 (ptrunctype.mk A) _ a,
    exact !is_prop.elim
  end

  @[hott] def ptrunctype_eq_of_pType_eq {n : ℕ₋₂} {A B : n-Type*} (p : A = B :> Type*)
    : A = B :=
  begin
    cases pType_eq_elim p with q r,
    exact ptrunctype_eq q r
  end

  @[hott] def is_trunc_ptrunctype [instance] {n : ℕ₋₂} (A : n-Type*) : is_trunc n A :=
  trunctype.struct A

end pointed open pointed

namespace pointed
  variables {A B C D : Type*} {f g h : A →* B} {P : A → Type _} {p₀ : P pt} {k k' l m : ppi P p₀}

  /- categorical properties of pointed maps -/

  @[hott] def pid [refl] (A : Type*) : A →* A :=
  pmap.mk id idp

  @[hott] def pcompose [trans] {A B C : Type*} (g : B →* C) (f : A →* B) : A →* C :=
  pmap.mk (λa, g (f a)) (ap g (respect_pt f) ⬝ respect_pt g)

  infixr ` ∘* `:60 := pcompose

  @[hott] def pmap_of_map {A B : Type _} (f : A → B) (a : A) :
    pointed.MK A a →* pointed.MK B (f a) :=
  pmap.mk f idp

  @[hott] def respect_pt_pcompose {A B C : Type*} (g : B →* C) (f : A →* B)
    : respect_pt (g ∘* f) = ap g (respect_pt f) ⬝ respect_pt g :=
  idp

  @[hott] def passoc (h : C →* D) (g : B →* C) (f : A →* B) : (h ∘* g) ∘* f ~* h ∘* (g ∘* f) :=
  phomotopy.mk (λa, idp)
    abstract !idp_con ⬝ whisker_right _ (!ap_con ⬝ whisker_right _ !ap_compose'⁻¹) ⬝ !con.assoc end

  @[hott] def pid_pcompose (f : A →* B) : pid B ∘* f ~* f :=
  begin
    fapply phomotopy.mk,
    { intro a, reflexivity},
    { reflexivity}
  end

  @[hott] def pcompose_pid (f : A →* B) : f ∘* pid A ~* f :=
  begin
    fapply phomotopy.mk,
    { intro a, reflexivity},
    { reflexivity}
  end

  /- equivalences and equalities -/

  @[hott] protected def ppi.sigma_char {A : Type*} (B : A → Type _) (b₀ : B pt) :
    ppi B b₀ ≃ Σ(k : Πa, B a), k pt = b₀ :=
  begin
    fapply equiv.MK: intro x,
    { constructor, exact respect_pt x },
    { induction x, constructor, assumption },
    { induction x, reflexivity },
    { induction x, reflexivity }
  end

  @[hott] def pmap.sigma_char {A B : Type*} : (A →* B) ≃ Σ(f : A → B), f pt = pt :=
  !ppi.sigma_char

  @[hott] def pmap.eta_expand {A B : Type*} (f : A →* B) : A →* B :=
  pmap.mk f (respect_pt f)

  @[hott] def pmap_equiv_right (A : Type*) (B : Type _)
    : (Σ(b : B), A →* (pointed.Mk b)) ≃ (A → B) :=
  begin
    fapply equiv.MK,
    { intros u a, exact pmap.to_fun u.2 a},
    { intro f, refine ⟨f pt, _⟩, fapply pmap.mk,
        intro a, esimp, exact f a,
        reflexivity},
    { intro f, reflexivity},
    { intro u, cases u with b f, cases f with f p, esimp at *, induction p,
      reflexivity}
  end

  /- some specific pointed maps -/

  -- The constant pointed map between any two types
  @[hott] def pconst (A B : Type*) : A →* B :=
  !ppi_const

  -- the pointed type of pointed maps -- TODO: remove
  @[hott] def ppmap (A B : Type*) : Type* :=
  @pppi A (λa, B)

  @[hott] def pcast {A B : Type*} (p : A = B) : A →* B :=
  pmap.mk (cast (ap pType.carrier p)) (by induction p; reflexivity)

  @[hott] def pinverse {X : Type*} : Ω X →* Ω X :=
  pmap.mk eq.inverse idp

  /-
    we generalize the @[hott] def of ap1 to arbitrary paths, so that we can prove properties about it
    using path induction (see for example ap1_gen_con and ap1_gen_con_natural)
  -/
  @[hott] def ap1_gen [reducible] {A B : Type _} (f : A → B) {a a' : A}
    {b b' : B} (q : f a = b) (q' : f a' = b') (p : a = a') : b = b' :=
  q⁻¹ ⬝ ap f p ⬝ q'

  @[hott] def ap1_gen_idp {A B : Type _} (f : A → B) {a : A} {b : B} (q : f a = b) :
    ap1_gen f q q idp = idp :=
  con.left_inv q

  @[hott] def ap1_gen_idp_left {A B : Type _} (f : A → B) {a a' : A} (p : a = a') :
    ap1_gen f idp idp p = ap f p :=
  proof idp_con (ap f p) qed

  @[hott] def ap1_gen_idp_left_con {A B : Type _} (f : A → B) {a : A} (p : a = a) (q : ap f p = idp) :
    ap1_gen_idp_left f p ⬝ q = proof ap (concat idp) q qed :=
  proof idp_con_idp q qed

  @[hott] def ap1 (f : A →* B) : Ω A →* Ω B :=
  pmap.mk (λp, ap1_gen f (respect_pt f) (respect_pt f) p) (ap1_gen_idp f (respect_pt f))

  @[hott] def apn (n : ℕ) (f : A →* B) : Ω[n] A →* Ω[n] B :=
  begin
  induction n with n IH,
  { exact f},
  { esimp [loopn], exact ap1 IH}
  end

  notation `Ω→`:(max+5) := ap1
  notation `Ω→[`:95 n:0 `]`:0 := apn n

  @[hott] def ptransport {A : Type _} (B : A → Type*) {a a' : A} (p : a = a')
    : B a →* B a' :=
  pmap.mk (transport B p) (apdt (λa, Point (B a)) p)

  @[hott] def pmap_of_eq_pt {A : Type _} {a a' : A} (p : a = a') :
    pointed.MK A a →* pointed.MK A a' :=
  pmap.mk id p

  @[hott] def pbool_pmap {A : Type*} (a : A) : pbool →* A :=
  pmap.mk (bool.rec pt a) idp

  /- properties of pointed maps -/

  @[hott] def apn_zero (f : A →* B) : Ω→[0] f = f := idp
  @[hott] def apn_succ (n : ℕ) (f : A →* B) : Ω→[n + 1] f = Ω→ (Ω→[n] f) := idp

  @[hott] def ap1_gen_con {A B : Type _} (f : A → B) {a₁ a₂ a₃ : A} {b₁ b₂ b₃ : B}
    (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (q₃ : f a₃ = b₃) (p₁ : a₁ = a₂) (p₂ : a₂ = a₃) :
    ap1_gen f q₁ q₃ (p₁ ⬝ p₂) = ap1_gen f q₁ q₂ p₁ ⬝ ap1_gen f q₂ q₃ p₂ :=
  begin induction p₂, induction q₃, induction q₂, reflexivity end

  @[hott] def ap1_gen_inv {A B : Type _} (f : A → B) {a₁ a₂ : A}
    {b₁ b₂ : B} (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (p₁ : a₁ = a₂) :
    ap1_gen f q₂ q₁ p₁⁻¹ = (ap1_gen f q₁ q₂ p₁)⁻¹ :=
  begin induction p₁, induction q₁, induction q₂, reflexivity end

  @[hott] def ap1_con {A B : Type*} (f : A →* B) (p q : Ω A) : ap1 f (p ⬝ q) = ap1 f p ⬝ ap1 f q :=
  ap1_gen_con f (respect_pt f) (respect_pt f) (respect_pt f) p q

  @[hott] theorem ap1_inv (f : A →* B) (p : Ω A) : ap1 f p⁻¹ = (ap1 f p)⁻¹ :=
  ap1_gen_inv f (respect_pt f) (respect_pt f) p

  -- the following two facts are used for the suspension axiom to define spectrum cohomology
  @[hott] def ap1_gen_con_natural {A B : Type _} (f : A → B) {a₁ a₂ a₃ : A} {p₁ p₁' : a₁ = a₂}
    {p₂ p₂' : a₂ = a₃}
    {b₁ b₂ b₃ : B} (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (q₃ : f a₃ = b₃)
    (r₁ : p₁ = p₁') (r₂ : p₂ = p₂') :
      square (ap1_gen_con f q₁ q₂ q₃ p₁ p₂)
             (ap1_gen_con f q₁ q₂ q₃ p₁' p₂')
             (ap (ap1_gen f q₁ q₃) (r₁ ◾ r₂))
             (ap (ap1_gen f q₁ q₂) r₁ ◾ ap (ap1_gen f q₂ q₃) r₂) :=
  begin induction r₁, induction r₂, exact vrfl end

  @[hott] def ap1_gen_con_idp {A B : Type _} (f : A → B) {a : A} {b : B} (q : f a = b) :
    ap1_gen_con f q q q idp idp ⬝ con.left_inv q ◾ con.left_inv q = con.left_inv q :=
  by induction q; reflexivity

  @[hott] def apn_con (n : ℕ) (f : A →* B) (p q : Ω[n+1] A)
    : apn (n+1) f (p ⬝ q) = apn (n+1) f p ⬝ apn (n+1) f q :=
  ap1_con (apn n f) p q

  @[hott] def apn_inv (n : ℕ)  (f : A →* B) (p : Ω[n+1] A) : apn (n+1) f p⁻¹ = (apn (n+1) f p)⁻¹ :=
  ap1_inv (apn n f) p

  @[hott] def is_equiv_ap1 (f : A →* B) [is_equiv f] : is_equiv (ap1 f) :=
  begin
    induction B with B b, induction f with f pf, esimp at *, cases pf, esimp,
    apply is_equiv.homotopy_closed (ap f),
    intro p, exact !idp_con⁻¹
  end

  @[hott] def is_equiv_apn (n : ℕ) (f : A →* B) [H : is_equiv f]
    : is_equiv (apn n f) :=
  begin
    induction n with n IH,
    { exact H},
    { exact is_equiv_ap1 (apn n f)}
  end

  @[hott] def pinverse_con {X : Type*} (p q : Ω X)
    : pinverse (p ⬝ q) = pinverse q ⬝ pinverse p :=
  !con_inv

  @[hott] def pinverse_inv {X : Type*} (p : Ω X)
    : pinverse p⁻¹ = (pinverse p)⁻¹ :=
  idp

  @[hott] def ap1_pcompose_pinverse {X Y : Type*} (f : X →* Y) :
    Ω→ f ∘* pinverse ~* pinverse ∘* Ω→ f :=
  phomotopy.mk (ap1_gen_inv f (respect_pt f) (respect_pt f))
    abstract begin
      induction Y with Y y₀, induction f with f f₀, esimp at * ⊢, induction f₀, reflexivity
    end end

  @[hott] def is_equiv_pcast [instance] {A B : Type*} (p : A = B) : is_equiv (pcast p) :=
  !is_equiv_cast

  /- categorical properties of pointed homotopies -/

  variable (k)
  @[hott] protected def phomotopy.refl : k ~* k :=
  phomotopy.mk homotopy.rfl !idp_con
  variable {k}
  @[hott] protected def phomotopy.rfl [reducible] [refl] : k ~* k :=
  phomotopy.refl k

  @[hott] protected def phomotopy.symm [symm] (p : k ~* l) : l ~* k :=
  phomotopy.mk p⁻¹ʰᵗʸ (inv_con_eq_of_eq_con (to_homotopy_pt p)⁻¹)

  @[hott] protected def phomotopy.trans [trans] (p : k ~* l) (q : l ~* m) :
    k ~* m :=
  phomotopy.mk (λa, p a ⬝ q a) (!con.assoc ⬝ whisker_left (p pt) (to_homotopy_pt q) ⬝ to_homotopy_pt p)

  infix ` ⬝* `:75 := phomotopy.trans
  postfix `⁻¹*`:(max+1) := phomotopy.symm

  /- equalities and equivalences relating pointed homotopies -/

  @[hott] def phomotopy.rec' [recursor] (B : k ~* l → Type _)
    (H : Π(h : k ~ l) (p : h pt ⬝ respect_pt l = respect_pt k), B (phomotopy.mk h p))
    (h : k ~* l) : B h :=
  begin
    induction h with h p,
    refine transport (λp, B (ppi.mk h p)) _ (H h (con_eq_of_eq_con_inv p)),
    apply to_left_inv !eq_con_inv_equiv_con_eq p
  end

  @[hott] def phomotopy.eta_expand (p : k ~* l) : k ~* l :=
  phomotopy.mk p (to_homotopy_pt p)

  @[hott] def is_trunc_ppi [instance] (n : ℕ₋₂) {A : Type*} (B : A → Type _) (b₀ : B pt) [Πa, is_trunc n (B a)] :
    is_trunc n (ppi B b₀) :=
  is_trunc_equiv_closed_rev _ !ppi.sigma_char

  @[hott] def is_trunc_pmap [instance] (n : ℕ₋₂) (A B : Type*) [is_trunc n B] :
    is_trunc n (A →* B) :=
  !is_trunc_ppi

  @[hott] def is_trunc_ppmap [instance] (n : ℕ₋₂) {A B : Type*} [is_trunc n B] :
    is_trunc n (ppmap A B) :=
  !is_trunc_pmap

  @[hott] def phomotopy_of_eq (p : k = l) : k ~* l :=
  phomotopy.mk (ap010 ppi.to_fun p) begin induction p, refine !idp_con end

  @[hott] def phomotopy_of_eq_idp (k : ppi P p₀) : phomotopy_of_eq idp = phomotopy.refl k :=
  idp

  @[hott] def pconcat_eq (p : k ~* l) (q : l = m) : k ~* m :=
  p ⬝* phomotopy_of_eq q

  @[hott] def eq_pconcat (p : k = l) (q : l ~* m) : k ~* m :=
  phomotopy_of_eq p ⬝* q

  infix ` ⬝*p `:75 := pconcat_eq
  infix ` ⬝p* `:75 := eq_pconcat

  @[hott] def pr1_phomotopy_eq {p q : k ~* l} (r : p = q) (a : A) : p a = q a :=
  ap010 to_homotopy r a

  @[hott] def pwhisker_left (h : B →* C) (p : f ~* g) : h ∘* f ~* h ∘* g :=
  phomotopy.mk (λa, ap h (p a))
    abstract !con.assoc⁻¹ ⬝ whisker_right _ (!ap_con⁻¹ ⬝ ap02 _ (to_homotopy_pt p)) end

  @[hott] def pwhisker_right (h : C →* A) (p : f ~* g) : f ∘* h ~* g ∘* h :=
  phomotopy.mk (λa, p (h a))
    abstract !con.assoc⁻¹ ⬝ whisker_right _ (!ap_con_eq_con_ap)⁻¹ ⬝ !con.assoc ⬝
             whisker_left _ (to_homotopy_pt p) end

  @[hott] def pconcat2 {A B C : Type*} {h i : B →* C} {f g : A →* B}
    (q : h ~* i) (p : f ~* g) : h ∘* f ~* i ∘* g :=
  pwhisker_left _ p ⬝* pwhisker_right _ q

  variables (k l)

  @[hott] def phomotopy.sigma_char
    : (k ~* l) ≃ Σ(p : k ~ l), p pt ⬝ respect_pt l = respect_pt k :=
  begin
    fapply equiv.MK : intros h,
    { exact ⟨h , to_homotopy_pt h⟩ },
    { cases h with h p, exact phomotopy.mk h p },
    { cases h with h p, exact ap (dpair h) (to_right_inv !eq_con_inv_equiv_con_eq p) },
    { induction h using phomotopy.rec' with h p,
      exact ap (phomotopy.mk h) (to_right_inv !eq_con_inv_equiv_con_eq p) }
  end

  @[hott] def ppi_eq_equiv_internal : (k = l) ≃ (k ~* l) :=
    calc (k = l) ≃ ppi.sigma_char P p₀ k = ppi.sigma_char P p₀ l
                   : eq_equiv_fn_eq (ppi.sigma_char P p₀) k l
            ...  ≃ Σ(p : k = l),
                     pathover (λh, h pt = p₀) (respect_pt k) p (respect_pt l)
                   : sigma_eq_equiv _ _
            ...  ≃ Σ(p : k = l),
                     respect_pt k = ap (λh, h pt) p ⬝ respect_pt l
                   : sigma_equiv_sigma_right
                       (λp, eq_pathover_equiv_Fl p (respect_pt k) (respect_pt l))
            ...  ≃ Σ(p : k = l),
                     respect_pt k = apd10 p pt ⬝ respect_pt l
                   : sigma_equiv_sigma_right
                       (λp, equiv_eq_closed_right _ (whisker_right _ (ap_eq_apd10 p _)))
            ...  ≃ Σ(p : k ~ l), respect_pt k = p pt ⬝ respect_pt l
                   : sigma_equiv_sigma_left' eq_equiv_homotopy
            ...  ≃ Σ(p : k ~ l), p pt ⬝ respect_pt l = respect_pt k
                   : sigma_equiv_sigma_right (λp, eq_equiv_eq_symm _ _)
            ...  ≃ (k ~* l) : phomotopy.sigma_char k l

  @[hott] def ppi_eq_equiv_internal_idp :
    ppi_eq_equiv_internal k k idp = phomotopy.refl k :=
  begin
    apply ap (phomotopy.mk (homotopy.refl _)), induction k with k k₀,
    esimp at * ⊢, induction k₀, reflexivity
  end

  @[hott] def ppi_eq_equiv : (k = l) ≃ (k ~* l) :=
  begin
    refine equiv_change_fun (ppi_eq_equiv_internal k l) _,
    { apply phomotopy_of_eq },
    { intro p, induction p, exact ppi_eq_equiv_internal_idp k }
  end
  variables {k l}

  @[hott] def pmap_eq_equiv (f g : A →* B) : (f = g) ≃ (f ~* g) :=
  ppi_eq_equiv f g

  @[hott] def eq_of_phomotopy (p : k ~* l) : k = l :=
  to_inv (ppi_eq_equiv k l) p

  @[hott] def eq_of_phomotopy_refl (k : ppi P p₀) : eq_of_phomotopy (phomotopy.refl k) = idpath k :=
  begin
    apply to_inv_eq_of_eq, reflexivity
  end

  @[hott] def phomotopy_of_homotopy (h : k ~ l) [Πa, is_set (P a)] : k ~* l :=
  begin
    fapply phomotopy.mk,
    { exact h },
    { apply is_set.elim }
  end

  @[hott] def ppi_eq_of_homotopy [Πa, is_set (P a)] (p : k ~ l) : k = l :=
  eq_of_phomotopy (phomotopy_of_homotopy p)

  @[hott] def pmap_eq_of_homotopy [is_set B] (p : f ~ g) : f = g :=
  ppi_eq_of_homotopy p

  @[hott] def phomotopy_of_eq_of_phomotopy (p : k ~* l) : phomotopy_of_eq (eq_of_phomotopy p) = p :=
  to_right_inv (ppi_eq_equiv k l) p

  @[hott] def phomotopy_rec_eq [recursor] {Q : (k ~* k') → Type _} (p : k ~* k')
    (H : Π(q : k = k'), Q (phomotopy_of_eq q)) : Q p :=
  phomotopy_of_eq_of_phomotopy p ▸ H (eq_of_phomotopy p)

  @[hott] def phomotopy_rec_idp [recursor] {Q : Π {k' : ppi P p₀}, (k ~* k') → Type _}
    {k' : ppi P p₀} (H : k ~* k') (q : Q (phomotopy.refl k)) : Q H :=
  begin
    induction H using phomotopy_rec_eq with t,
    induction t, exact phomotopy_of_eq_idp k ▸ q,
  end

  @[hott] def phomotopy_rec_idp' (Q : Π ⦃k' : ppi P p₀⦄, (k ~* k') → (k = k') → Type _)
    (q : Q phomotopy.rfl idp) ⦃k' : ppi P p₀⦄ (H : k ~* k') : Q H (eq_of_phomotopy H) :=
  begin
    induction H using phomotopy_rec_idp,
    exact transport (Q phomotopy.rfl) !eq_of_phomotopy_refl⁻¹ q
  end

  attribute phomotopy.rec' [recursor]

  @[hott] def phomotopy_rec_eq_phomotopy_of_eq {Q : (k ~* l) → Type _} (p : k = l)
    (H : Π(q : k = l), Q (phomotopy_of_eq q)) : phomotopy_rec_eq (phomotopy_of_eq p) H = H p :=
  begin
    unfold phomotopy_rec_eq,
    refine ap (λp, p ▸ _) !adj ⬝ _,
    refine !tr_compose⁻¹ ⬝ _,
    apply apdt
  end

  @[hott] def phomotopy_rec_idp_refl {Q : Π{l}, (k ~* l) → Type _} (H : Q (phomotopy.refl k)) :
    phomotopy_rec_idp phomotopy.rfl H = H :=
  !phomotopy_rec_eq_phomotopy_of_eq

  @[hott] def phomotopy_rec_idp'_refl (Q : Π ⦃k' : ppi P p₀⦄, (k ~* k') → (k = k') → Type _)
    (q : Q phomotopy.rfl idp) :
    phomotopy_rec_idp' Q q phomotopy.rfl = transport (Q phomotopy.rfl) !eq_of_phomotopy_refl⁻¹ q :=
  !phomotopy_rec_idp_refl

  /- maps out of or into contractible types -/
  @[hott] def phomotopy_of_is_contr_cod (k l : ppi P p₀) [Πa, is_contr (P a)] :
    k ~* l :=
  phomotopy.mk (λa, !eq_of_is_contr) !eq_of_is_contr

  @[hott] def phomotopy_of_is_contr_cod_pmap (f g : A →* B) [is_contr B] : f ~* g :=
  phomotopy_of_is_contr_cod f g

  @[hott] def phomotopy_of_is_contr_dom (k l : ppi P p₀) [is_contr A] : k ~* l :=
  begin
    fapply phomotopy.mk,
    { intro a, exact eq_of_pathover_idp (change_path !is_prop.elim
      (apd k !is_prop.elim ⬝op respect_pt k ⬝ (respect_pt l)⁻¹ ⬝o apd l !is_prop.elim)) },
    rewrite [▸*, +is_prop_elim_self, +apd_idp, cono_idpo],
    refine ap (λx, eq_of_pathover_idp (change_path x _)) !is_prop_elim_self ◾ idp ⬝ _,
    xrewrite [change_path_idp, idpo_concato_eq, inv_con_cancel_right],
  end

  /- adjunction between (-)₊ : Type _ → Type* and pType.carrier : Type* → Type _  -/
  @[hott] def pmap_equiv_left (A : Type _) (B : Type*) : A₊ →* B ≃ (A → B) :=
  begin
    fapply equiv.MK,
    { intros f a, cases f with f p, exact f (some a) },
    { intro f, fconstructor,
        intro a, cases a, exact pt, exact f a,
        reflexivity },
    { intro f, reflexivity },
    { intro f, cases f with f p, esimp, fapply eq_of_phomotopy, fapply phomotopy.mk,
      { intro a, cases a; all_goals (esimp at *), exact p⁻¹ },
      { esimp, exact !con.left_inv }},
  end

  -- pmap_pbool_pequiv is the pointed equivalence
  @[hott] def pmap_pbool_equiv (B : Type*) : (pbool →* B) ≃ B :=
  begin
    fapply equiv.MK,
    { intro f, cases f with f p, exact f tt },
    { intro b, fconstructor,
        intro u, cases u, exact pt, exact b,
        reflexivity },
    { intro b, reflexivity },
    { intro f, cases f with f p, esimp, fapply eq_of_phomotopy, fapply phomotopy.mk,
      { intro a, cases a; all_goals (esimp at *), exact p⁻¹ },
      { esimp, exact !con.left_inv }},
  end

  /-
    Pointed maps respecting pointed homotopies.
    In general we need function extensionality for pap,
    but for particular F we can do it without function extensionality.
    This might be preferred, because such pointed homotopies compute. On the other hand,
    when using function extensionality, it's easier to prove that if p is reflexivity, then the
    resulting pointed homotopy is reflexivity
  -/
  @[hott] def pap (F : (A →* B) → (C →* D)) {f g : A →* B} (p : f ~* g) : F f ~* F g :=
  begin
    induction p using phomotopy_rec_idp, reflexivity
  end

  @[hott] def pap_refl (F : (A →* B) → (C →* D)) (f : A →* B) :
    pap F (phomotopy.refl f) = phomotopy.refl (F f) :=
  !phomotopy_rec_idp_refl

  @[hott] def ap1_phomotopy {f g : A →* B} (p : f ~* g) : Ω→ f ~* Ω→ g :=
  pap Ω→ p

  @[hott] def ap1_phomotopy_refl {X Y : Type*} (f : X →* Y) :
    ap1_phomotopy (phomotopy.refl f) = phomotopy.refl (Ω→ f) :=
  !pap_refl

  --a proof not using function extensionality:
  @[hott] def ap1_phomotopy_explicit {f g : A →* B} (p : f ~* g) : Ω→ f ~* Ω→ g :=
  begin
    induction p with p q, induction f with f pf, induction g with g pg, induction B with B b,
    esimp at * ⊢, induction q, induction pg,
    fapply phomotopy.mk,
    { intro l, refine _ ⬝ !idp_con⁻¹ᵖ, refine !con.assoc ⬝ _, apply inv_con_eq_of_eq_con,
      apply ap_con_eq_con_ap},
    { induction A with A a, unfold [ap_con_eq_con_ap], generalize p a, generalize g a, intros b q,
      induction q, reflexivity}
  end

  @[hott] def apn_phomotopy {f g : A →* B} (n : ℕ) (p : f ~* g) : apn n f ~* apn n g :=
  begin
    induction n with n IH,
    { exact p},
    { exact ap1_phomotopy IH}
  end

  -- the following two definitiongs are mostly the same, maybe we should remove one
  @[hott] def ap_eq_of_phomotopy {A B : Type*} {f g : A →* B} (p : f ~* g) (a : A) :
    ap (λf : A →* B, f a) (eq_of_phomotopy p) = p a :=
  ap010 to_homotopy (phomotopy_of_eq_of_phomotopy p) a

  @[hott] def to_fun_eq_of_phomotopy {A B : Type*} {f g : A →* B} (p : f ~* g) (a : A) :
    ap010 pmap.to_fun (eq_of_phomotopy p) a = p a :=
  begin
    induction p using phomotopy_rec_idp,
    exact ap (λx, ap010 pmap.to_fun x a) !eq_of_phomotopy_refl
  end

  @[hott] def ap1_eq_of_phomotopy {A B : Type*} {f g : A →* B} (p : f ~* g) :
    ap Ω→ (eq_of_phomotopy p) = eq_of_phomotopy (ap1_phomotopy p) :=
  begin
    induction p using phomotopy_rec_idp,
    refine ap02 _ !eq_of_phomotopy_refl ⬝ !eq_of_phomotopy_refl⁻¹ ⬝ ap eq_of_phomotopy _,
    exact !ap1_phomotopy_refl⁻¹
  end

  /- pointed homotopies between the given pointed maps -/

  @[hott] def ap1_pid {A : Type*} : ap1 (pid A) ~* pid (Ω A) :=
  begin
    fapply phomotopy.mk,
    { intro p, esimp, refine !idp_con ⬝ !ap_id},
    { reflexivity}
  end

  @[hott] def ap1_pinverse {A : Type*} : ap1 (@pinverse A) ~* @pinverse (Ω A) :=
  begin
    fapply phomotopy.mk,
    { intro p, refine !idp_con ⬝ _, exact !inv_eq_inv2⁻¹ },
    { reflexivity}
  end

  @[hott] def ap1_gen_compose {A B C : Type _} (g : B → C) (f : A → B) {a₁ a₂ : A} {b₁ b₂ : B}
    {c₁ c₂ : C} (q₁ : f a₁ = b₁) (q₂ : f a₂ = b₂) (r₁ : g b₁ = c₁) (r₂ : g b₂ = c₂) (p : a₁ = a₂) :
    ap1_gen (g ∘ f) (ap g q₁ ⬝ r₁) (ap g q₂ ⬝ r₂) p = ap1_gen g r₁ r₂ (ap1_gen f q₁ q₂ p) :=
  begin induction p, induction q₁, induction q₂, induction r₁, induction r₂, reflexivity end

  @[hott] def ap1_gen_compose_idp {A B C : Type _} (g : B → C) (f : A → B) {a : A}
    {b : B} {c : C} (q : f a = b) (r : g b = c) :
    ap1_gen_compose g f q q r r idp ⬝ (ap (ap1_gen g r r) (ap1_gen_idp f q) ⬝ ap1_gen_idp g r) =
    ap1_gen_idp (g ∘ f) (ap g q ⬝ r) :=
  begin induction q, induction r, reflexivity end

  @[hott] def ap1_pcompose {A B C : Type*} (g : B →* C) (f : A →* B) :
    ap1 (g ∘* f) ~* ap1 g ∘* ap1 f :=
  phomotopy.mk (ap1_gen_compose g f (respect_pt f) (respect_pt f) (respect_pt g) (respect_pt g))
               (ap1_gen_compose_idp g f (respect_pt f) (respect_pt g))

  @[hott] def ap1_pconst (A B : Type*) : Ω→(pconst A B) ~* pconst (Ω A) (Ω B) :=
  phomotopy.mk (λp, ap1_gen_idp_left (const A pt) p ⬝ ap_constant p pt) rfl

  @[hott] def ap1_gen_con_left {A B : Type _} {a a' : A} {b₀ b₁ b₂ : B}
    {f : A → b₀ = b₁} {f' : A → b₁ = b₂} {q₀ q₁ : b₀ = b₁} {q₀' q₁' : b₁ = b₂}
    (r₀ : f a = q₀) (r₁ : f a' = q₁) (r₀' : f' a = q₀') (r₁' : f' a' = q₁') (p : a = a') :
      ap1_gen (λa, f a ⬝ f' a) (r₀ ◾ r₀') (r₁ ◾ r₁') p =
      whisker_right q₀' (ap1_gen f r₀ r₁ p) ⬝ whisker_left q₁ (ap1_gen f' r₀' r₁' p) :=
  begin induction r₀, induction r₁, induction r₀', induction r₁', induction p, reflexivity end

  @[hott] def ap1_gen_con_left_idp {A B : Type _} {a : A} {b₀ b₁ b₂ : B}
    {f : A → b₀ = b₁} {f' : A → b₁ = b₂} {q₀ : b₀ = b₁} {q₁ : b₁ = b₂}
    (r₀ : f a = q₀) (r₁ : f' a = q₁) :
      ap1_gen_con_left r₀ r₀ r₁ r₁ idp =
      !con.left_inv ⬝ (ap (whisker_right q₁) !con.left_inv ◾ ap (whisker_left _) !con.left_inv)⁻¹ :=
  begin induction r₀, induction r₁, reflexivity end

  @[hott] def ptransport_change_eq {A : Type _} (B : A → Type*) {a a' : A} {p q : a = a'}
    (r : p = q) : ptransport B p ~* ptransport B q :=
  phomotopy.mk (λb, ap (λp, transport B p b) r) begin induction r, apply idp_con end

  @[hott] def pnatural_square {A B : Type _} (X : B → Type*) {f g : A → B}
    (h : Πa, X (f a) →* X (g a)) {a a' : A} (p : a = a') :
    h a' ∘* ptransport X (ap f p) ~* ptransport X (ap g p) ∘* h a :=
  by induction p; exact !pcompose_pid ⬝* !pid_pcompose⁻¹*

  @[hott] def apn_pid {A : Type*} (n : ℕ) : apn n (pid A) ~* pid (Ω[n] A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact ap1_phomotopy IH ⬝* ap1_pid}
  end

  @[hott] def apn_pconst (A B : Type*) (n : ℕ) :
    apn n (pconst A B) ~* pconst (Ω[n] A) (Ω[n] B) :=
  begin
    induction n with n IH,
    { reflexivity },
    { exact ap1_phomotopy IH ⬝* !ap1_pconst }
  end

  @[hott] def apn_pcompose (n : ℕ) (g : B →* C) (f : A →* B) :
    apn n (g ∘* f) ~* apn n g ∘* apn n f :=
  begin
    induction n with n IH,
    { reflexivity},
    { refine ap1_phomotopy IH ⬝* _, apply ap1_pcompose}
  end

  @[hott] def pcast_idp {A : Type*} : pcast (idpath A) ~* pid A :=
  by reflexivity

  @[hott] def pinverse_pinverse (A : Type*) : pinverse ∘* pinverse ~* pid (Ω A) :=
  begin
    fapply phomotopy.mk,
    { apply inv_inv},
    { reflexivity}
  end

  @[hott] def pcast_ap_loop {A B : Type*} (p : A = B) :
    pcast (ap Ω p) ~* ap1 (pcast p) :=
  begin
    fapply phomotopy.mk,
    { intro a, induction p, esimp, exact (!idp_con ⬝ !ap_id)⁻¹},
    { induction p, reflexivity}
  end

  @[hott] def ap1_pmap_of_map {A B : Type _} (f : A → B) (a : A) :
    ap1 (pmap_of_map f a) ~* pmap_of_map (ap f) (idpath a) :=
  begin
    fapply phomotopy.mk,
    { intro a, esimp, apply idp_con},
    { reflexivity}
  end

  @[hott] def pcast_commute {A : Type _} {B C : A → Type*} (f : Πa, B a →* C a)
    {a₁ a₂ : A} (p : a₁ = a₂) : pcast (ap C p) ∘* f a₁ ~* f a₂ ∘* pcast (ap B p) :=
  phomotopy.mk
    begin induction p, reflexivity end
    begin induction p, esimp, refine !idp_con ⬝ !idp_con ⬝ !ap_id⁻¹ end

  /- pointed equivalences -/

  structure pequiv (A B : Type*) :=
  mk' :: (to_pmap : A →* B)
         (to_pinv1 : B →* A)
         (to_pinv2 : B →* A)
         (pright_inv : to_pmap ∘* to_pinv1 ~* pid B)
         (pleft_inv : to_pinv2 ∘* to_pmap ~* pid A)

  infix ` ≃* `:25 := pequiv

  @[hott] def pmap_of_pequiv [coercion] [reducible] {A B : Type*} (f : A ≃* B) :
    @ppi A (λa, B) pt :=
  pequiv.to_pmap f

  @[hott] def to_pinv (f : A ≃* B) : B →* A :=
  pequiv.to_pinv1 f

  @[hott] def pleft_inv' (f : A ≃* B) : to_pinv f ∘* f ~* pid A :=
  let g := to_pinv f in
  let h := pequiv.to_pinv2 f in
  calc g ∘* f ~* pid A ∘* (g ∘* f)    : by exact !pid_pcompose⁻¹*
          ... ~* (h ∘* f) ∘* (g ∘* f) : by exact pwhisker_right _ (pequiv.pleft_inv f)⁻¹*
          ... ~* h ∘* (f ∘* g) ∘* f   : by exact !passoc ⬝* pwhisker_left _ !passoc⁻¹*
          ... ~* h ∘* pid B ∘* f      : by exact !pwhisker_left (!pwhisker_right !pequiv.pright_inv)
          ... ~* h ∘* f               : by exact pwhisker_left _ !pid_pcompose
          ... ~* pid A                : by exact pequiv.pleft_inv f

  @[hott] def equiv_of_pequiv [coercion] (f : A ≃* B) : A ≃ B :=
  have is_equiv f, from adjointify f (to_pinv f) (pequiv.pright_inv f) (pleft_inv' f),
  equiv.mk f _

  attribute pointed._trans_of_equiv_of_pequiv pointed._trans_of_pmap_of_pequiv

  @[hott] def pequiv.to_is_equiv [instance] (f : A ≃* B) :
    is_equiv (pointed._trans_of_equiv_of_pequiv f) :=
  adjointify f (to_pinv f) (pequiv.pright_inv f) (pleft_inv' f)

  @[hott] def pequiv.to_is_equiv' [instance] (f : A ≃* B) :
    is_equiv (pointed._trans_of_pmap_of_pequiv f) :=
  pequiv.to_is_equiv f

  @[hott] protected def pequiv.MK (f : A →* B) (g : B →* A)
    (gf : g ∘* f ~* !pid) (fg : f ∘* g ~* !pid) : A ≃* B :=
  pequiv.mk' f g g fg gf

  @[hott] def pinv (f : A →* B) (H : is_equiv f) : B →* A :=
  pmap.mk f⁻¹ᶠ (ap f⁻¹ᶠ (respect_pt f)⁻¹ ⬝ (left_inv f pt))

  @[hott] def pequiv_of_pmap (f : A →* B) (H : is_equiv f) : A ≃* B :=
  pequiv.mk' f (pinv f H) (pinv f H)
  abstract begin
    fapply phomotopy.mk, exact right_inv f,
    induction f with f f₀, induction B with B b₀, esimp at *, induction f₀, esimp,
    exact adj f pt ⬝ ap02 f !idp_con⁻¹
  end end
  abstract begin
    fapply phomotopy.mk, exact left_inv f,
    induction f with f f₀, induction B with B b₀, esimp at *, induction f₀, esimp,
    exact !idp_con⁻¹ ⬝ !idp_con⁻¹
  end end

  @[hott] def pequiv.mk (f : A → B) (H : is_equiv f) (p : f pt = pt) : A ≃* B :=
  pequiv_of_pmap (pmap.mk f p) H

  @[hott] def pequiv_of_equiv (f : A ≃ B) (H : f pt = pt) : A ≃* B :=
  pequiv.mk f _ H

  @[hott] protected def pequiv.MK' (f : A →* B) (g : B → A)
    (gf : Πa, g (f a) = a) (fg : Πb, f (g b) = b) : A ≃* B :=
  pequiv.mk f (adjointify f g fg gf) (respect_pt f)

  /- reflexivity and symmetry (transitivity is below) -/

  @[hott] protected def pequiv.refl [refl] (A : Type*) : A ≃* A :=
  pequiv.mk' (pid A) (pid A) (pid A) !pid_pcompose !pcompose_pid

  @[hott] protected def pequiv.rfl : A ≃* A :=
  pequiv.refl A

  @[hott] protected def pequiv.symm [symm] (f : A ≃* B) : B ≃* A :=
  pequiv.MK (to_pinv f) f (pequiv.pright_inv f) (pleft_inv' f)

  postfix `⁻¹ᵉ*`:(max + 1) := pequiv.symm

  @[hott] def pleft_inv (f : A ≃* B) : f⁻¹ᵉ* ∘* f ~* pid A :=
  pleft_inv' f

  @[hott] def pright_inv (f : A ≃* B) : f ∘* f⁻¹ᵉ* ~* pid B :=
  pequiv.pright_inv f

  @[hott] def to_pmap_pequiv_of_pmap {A B : Type*} (f : A →* B) (H : is_equiv f)
    : pequiv.to_pmap (pequiv_of_pmap f H) = f :=
  by reflexivity

  @[hott] def to_pmap_pequiv_MK (f : A →* B) (g : B →* A)
    (gf : g ∘* f ~* !pid) (fg : f ∘* g ~* !pid) : pequiv.MK f g gf fg ~* f :=
  by reflexivity

  @[hott] def to_pinv_pequiv_MK (f : A →* B) (g : B →* A)
    (gf : g ∘* f ~* !pid) (fg : f ∘* g ~* !pid) : to_pinv (pequiv.MK f g gf fg) ~* g :=
  by reflexivity

  /- more on pointed equivalences -/

  @[hott] def pequiv_ap {A : Type _} (B : A → Type*) {a a' : A} (p : a = a')
    : B a ≃* B a' :=
  pequiv_of_pmap (ptransport B p) !is_equiv_tr

  @[hott] def pequiv_change_fun (f : A ≃* B) (f' : A →* B) (Heq : f ~ f') : A ≃* B :=
  pequiv_of_pmap f' (is_equiv.homotopy_closed f Heq)

  @[hott] def pequiv_change_inv (f : A ≃* B) (f' : B →* A) (Heq : to_pinv f ~ f')
    : A ≃* B :=
  pequiv.MK' f f' (to_left_inv (equiv_change_inv f Heq)) (to_right_inv (equiv_change_inv f Heq))

  @[hott] def pequiv_rect' (f : A ≃* B) (P : A → B → Type _)
    (g : Πb, P (f⁻¹ b) b) (a : A) : P a (f a) :=
  left_inv f a ▸ g (f a)

  @[hott] def pua {A B : Type*} (f : A ≃* B) : A = B :=
  pType_eq (equiv_of_pequiv f) !respect_pt

  @[hott] def pequiv_of_eq {A B : Type*} (p : A = B) : A ≃* B :=
  pequiv_of_pmap (pcast p) !is_equiv_tr

  @[hott] def eq_of_pequiv {A B : Type*} (p : A ≃* B) : A = B :=
  pType_eq (equiv_of_pequiv p) !respect_pt

  @[hott] def peap {A B : Type*} (F : Type* → Type*) (p : A ≃* B) : F A ≃* F B :=
  pequiv_of_pmap (pcast (ap F (eq_of_pequiv p))) begin cases eq_of_pequiv p, apply is_equiv_id end

  -- rename pequiv_of_eq_natural
  @[hott] def pequiv_of_eq_commute {A : Type _} {B C : A → Type*} (f : Πa, B a →* C a)
    {a₁ a₂ : A} (p : a₁ = a₂) : pequiv_of_eq (ap C p) ∘* f a₁ ~* f a₂ ∘* pequiv_of_eq (ap B p) :=
  pcast_commute f p

  -- @[hott] def pequiv.eta_expand {A B : Type*} (f : A ≃* B) : A ≃* B :=
  -- pequiv.mk' f (to_pinv f) (pequiv.to_pinv2 f) (pright_inv f) _

  /-
    the @[hott] theorem pequiv_eq, which gives a condition for two pointed equivalences are equal
    is in types.equiv to avoid circular imports
  -/

  /- computation rules of pointed homotopies, possibly combined with pointed equivalences -/
  @[hott] def pcancel_left (f : B ≃* C) {g h : A →* B} (p : f ∘* g ~* f ∘* h) : g ~* h :=
  begin
    refine _⁻¹* ⬝* pwhisker_left f⁻¹ᵉ* p ⬝* _:
    refine !passoc⁻¹* ⬝* _:
    refine pwhisker_right _ (pleft_inv f) ⬝* _:
    apply pid_pcompose
  end

  @[hott] def pcancel_right (f : A ≃* B) {g h : B →* C} (p : g ∘* f ~* h ∘* f) : g ~* h :=
  begin
    refine _⁻¹* ⬝* pwhisker_right f⁻¹ᵉ* p ⬝* _:
    refine !passoc ⬝* _:
    refine pwhisker_left _ (pright_inv f) ⬝* _:
    apply pcompose_pid
  end

  @[hott] def phomotopy_pinv_right_of_phomotopy {f : A ≃* B} {g : B →* C} {h : A →* C}
    (p : g ∘* f ~* h) : g ~* h ∘* f⁻¹ᵉ* :=
  begin
    refine _ ⬝* pwhisker_right _ p, symmetry,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (pright_inv f) ⬝* _,
    apply pcompose_pid
  end

  @[hott] def phomotopy_of_pinv_right_phomotopy {f : B ≃* A} {g : B →* C} {h : A →* C}
    (p : g ∘* f⁻¹ᵉ* ~* h) : g ~* h ∘* f :=
  begin
    refine _ ⬝* pwhisker_right _ p, symmetry,
    refine !passoc ⬝* _,
    refine pwhisker_left _ (pleft_inv f) ⬝* _,
    apply pcompose_pid
  end

  @[hott] def pinv_right_phomotopy_of_phomotopy {f : A ≃* B} {g : B →* C} {h : A →* C}
    (p : h ~* g ∘* f) : h ∘* f⁻¹ᵉ* ~* g :=
  (phomotopy_pinv_right_of_phomotopy p⁻¹*)⁻¹*

  @[hott] def phomotopy_of_phomotopy_pinv_right {f : B ≃* A} {g : B →* C} {h : A →* C}
    (p : h ~* g ∘* f⁻¹ᵉ*) : h ∘* f ~* g :=
  (phomotopy_of_pinv_right_phomotopy p⁻¹*)⁻¹*

  @[hott] def phomotopy_pinv_left_of_phomotopy {f : B ≃* C} {g : A →* B} {h : A →* C}
    (p : f ∘* g ~* h) : g ~* f⁻¹ᵉ* ∘* h :=
  begin
    refine _ ⬝* pwhisker_left _ p, symmetry,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ (pleft_inv f) ⬝* _,
    apply pid_pcompose
  end

  @[hott] def phomotopy_of_pinv_left_phomotopy {f : C ≃* B} {g : A →* B} {h : A →* C}
    (p : f⁻¹ᵉ* ∘* g ~* h) : g ~* f ∘* h :=
  begin
    refine _ ⬝* pwhisker_left _ p, symmetry,
    refine !passoc⁻¹* ⬝* _,
    refine pwhisker_right _ (pright_inv f) ⬝* _,
    apply pid_pcompose
  end

  @[hott] def pinv_left_phomotopy_of_phomotopy {f : B ≃* C} {g : A →* B} {h : A →* C}
    (p : h ~* f ∘* g) : f⁻¹ᵉ* ∘* h ~* g :=
  (phomotopy_pinv_left_of_phomotopy p⁻¹*)⁻¹*

  @[hott] def phomotopy_of_phomotopy_pinv_left {f : C ≃* B} {g : A →* B} {h : A →* C}
    (p : h ~* f⁻¹ᵉ* ∘* g) : f ∘* h ~* g :=
  (phomotopy_of_pinv_left_phomotopy p⁻¹*)⁻¹*

  @[hott] def pcompose2 {A B C : Type*} {g g' : B →* C} {f f' : A →* B} (q : g ~* g') (p : f ~* f') :
    g ∘* f ~* g' ∘* f' :=
  pwhisker_right f q ⬝* pwhisker_left g' p

  infixr ` ◾* `:80 := pcompose2

  @[hott] def phomotopy_pinv_of_phomotopy_pid {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : g ∘* f ~* pid A) : f ~* g⁻¹ᵉ* :=
  phomotopy_pinv_left_of_phomotopy p ⬝* !pcompose_pid

  @[hott] def phomotopy_pinv_of_phomotopy_pid' {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : f ∘* g ~* pid B) : f ~* g⁻¹ᵉ* :=
  phomotopy_pinv_right_of_phomotopy p ⬝* !pid_pcompose

  @[hott] def pinv_phomotopy_of_pid_phomotopy {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : pid A ~* g ∘* f) : g⁻¹ᵉ* ~* f :=
  (phomotopy_pinv_of_phomotopy_pid p⁻¹*)⁻¹*

  @[hott] def pinv_phomotopy_of_pid_phomotopy' {A B : Type*} {f : A →* B} {g : B ≃* A}
    (p : pid B ~* f ∘* g) : g⁻¹ᵉ* ~* f :=
  (phomotopy_pinv_of_phomotopy_pid' p⁻¹*)⁻¹*

  @[hott] def pinv_pcompose_cancel_left {A B C : Type*} (g : B ≃* C) (f : A →* B) :
    g⁻¹ᵉ* ∘* (g ∘* f) ~* f :=
  !passoc⁻¹* ⬝* pwhisker_right f !pleft_inv ⬝* !pid_pcompose

  @[hott] def pcompose_pinv_cancel_left {A B C : Type*} (g : C ≃* B) (f : A →* B) :
    g ∘* (g⁻¹ᵉ* ∘* f) ~* f :=
  !passoc⁻¹* ⬝* pwhisker_right f !pright_inv ⬝* !pid_pcompose

  @[hott] def pinv_pcompose_cancel_right {A B C : Type*} (g : B →* C) (f : B ≃* A) :
    (g ∘* f⁻¹ᵉ*) ∘* f ~* g :=
  !passoc ⬝* pwhisker_left g !pleft_inv ⬝* !pcompose_pid

  @[hott] def pcompose_pinv_cancel_right {A B C : Type*} (g : B →* C) (f : A ≃* B) :
    (g ∘* f) ∘* f⁻¹ᵉ* ~* g :=
  !passoc ⬝* pwhisker_left g !pright_inv ⬝* !pcompose_pid

  @[hott] def pinv_pinv {A B : Type*} (f : A ≃* B) : (f⁻¹ᵉ*)⁻¹ᵉ* ~* f :=
  (phomotopy_pinv_of_phomotopy_pid (pleft_inv f))⁻¹*

  @[hott] def pinv2 {A B : Type*} {f f' : A ≃* B} (p : f ~* f') : f⁻¹ᵉ* ~* f'⁻¹ᵉ* :=
  phomotopy_pinv_of_phomotopy_pid (pinv_right_phomotopy_of_phomotopy (!pid_pcompose ⬝* p)⁻¹*)

  postfix [parsing_only] `⁻²*`:(max+10) := pinv2

  @[hott] protected def pequiv.trans [trans] (f : A ≃* B) (g : B ≃* C) : A ≃* C :=
  pequiv.MK (g ∘* f) (f⁻¹ᵉ* ∘* g⁻¹ᵉ*)
    abstract !passoc ⬝* pwhisker_left _ (pinv_pcompose_cancel_left g f) ⬝* pleft_inv f end
    abstract !passoc ⬝* pwhisker_left _ (pcompose_pinv_cancel_left f g⁻¹ᵉ*) ⬝* pright_inv g end

  @[hott] def pequiv_compose {A B C : Type*} (g : B ≃* C) (f : A ≃* B) : A ≃* C :=
  pequiv.trans f g

  infix ` ⬝e* `:75 := pequiv.trans
  infixr ` ∘*ᵉ `:60 := pequiv_compose

  @[hott] def to_pmap_pequiv_trans {A B C : Type*} (f : A ≃* B) (g : B ≃* C)
    : pequiv.to_pmap (f ⬝e* g) = g ∘* f :=
  by reflexivity

  @[hott] def to_fun_pequiv_trans {X Y Z : Type*} (f : X ≃* Y) (g :Y ≃* Z) : f ⬝e* g ~ g ∘ f :=
  λx, idp

  @[hott] def peconcat_eq {A B C : Type*} (p : A ≃* B) (q : B = C) : A ≃* C :=
  p ⬝e* pequiv_of_eq q

  @[hott] def eq_peconcat {A B C : Type*} (p : A = B) (q : B ≃* C) : A ≃* C :=
  pequiv_of_eq p ⬝e* q


  infix ` ⬝e*p `:75 := peconcat_eq
  infix ` ⬝pe* `:75 := eq_peconcat


  @[hott] def trans_pinv {A B C : Type*} (f : A ≃* B) (g : B ≃* C) :
    (f ⬝e* g)⁻¹ᵉ* ~* f⁻¹ᵉ* ∘* g⁻¹ᵉ* :=
  by reflexivity

  @[hott] def pinv_trans_pinv_left {A B C : Type*} (f : B ≃* A) (g : B ≃* C) :
    (f⁻¹ᵉ* ⬝e* g)⁻¹ᵉ* ~* f ∘* g⁻¹ᵉ* :=
  by reflexivity

  @[hott] def pinv_trans_pinv_right {A B C : Type*} (f : A ≃* B) (g : C ≃* B) :
    (f ⬝e* g⁻¹ᵉ*)⁻¹ᵉ* ~* f⁻¹ᵉ* ∘* g :=
  by reflexivity

  @[hott] def pinv_trans_pinv_pinv {A B C : Type*} (f : B ≃* A) (g : C ≃* B) :
    (f⁻¹ᵉ* ⬝e* g⁻¹ᵉ*)⁻¹ᵉ* ~* f ∘* g :=
  by reflexivity

  /- pointed equivalences between particular pointed types -/

  -- TODO: remove is_equiv_apn, which is proven again here
  @[hott] def loopn_pequiv_loopn (n : ℕ) (f : A ≃* B) : Ω[n] A ≃* Ω[n] B :=
  pequiv.MK (apn n f) (apn n f⁻¹ᵉ*)
  abstract begin
    induction n with n IH,
    { apply pleft_inv},
    { replace nat.succ n with n + 1,
      rewrite [+apn_succ],
      refine !ap1_pcompose⁻¹* ⬝* _,
      refine ap1_phomotopy IH ⬝* _,
      apply ap1_pid}
  end end
  abstract begin
    induction n with n IH,
    { apply pright_inv},
    { replace nat.succ n with n + 1,
      rewrite [+apn_succ],
      refine !ap1_pcompose⁻¹* ⬝* _,
      refine ap1_phomotopy IH ⬝* _,
      apply ap1_pid}
  end end

  @[hott] def loop_pequiv_loop (f : A ≃* B) : Ω A ≃* Ω B :=
  loopn_pequiv_loopn 1 f

  @[hott] def loop_pequiv_eq_closed {A : Type _} {a a' : A} (p : a = a')
    : pointed.MK (a = a) idp ≃* pointed.MK (a' = a') idp :=
  pequiv_of_equiv (loop_equiv_eq_closed p) (con.left_inv p)

  @[hott] def to_pmap_loopn_pequiv_loopn (n : ℕ) (f : A ≃* B)
    : loopn_pequiv_loopn n f ~* apn n f :=
  by reflexivity

  @[hott] def to_pinv_loopn_pequiv_loopn (n : ℕ) (f : A ≃* B)
    : (loopn_pequiv_loopn n f)⁻¹ᵉ* ~* apn n f⁻¹ᵉ* :=
  by reflexivity

  @[hott] def loopn_pequiv_loopn_con (n : ℕ) (f : A ≃* B) (p q : Ω[n+1] A)
    : loopn_pequiv_loopn (n+1) f (p ⬝ q) =
    loopn_pequiv_loopn (n+1) f p ⬝ loopn_pequiv_loopn (n+1) f q :=
  ap1_con (loopn_pequiv_loopn n f) p q

  @[hott] def loop_pequiv_loop_con {A B : Type*} (f : A ≃* B) (p q : Ω A)
    : loop_pequiv_loop f (p ⬝ q) = loop_pequiv_loop f p ⬝ loop_pequiv_loop f q :=
  loopn_pequiv_loopn_con 0 f p q

  @[hott] def loopn_pequiv_loopn_rfl (n : ℕ) (A : Type*) :
    loopn_pequiv_loopn n (pequiv.refl A) ~* pequiv.refl (Ω[n] A) :=
  begin
    exact !to_pmap_loopn_pequiv_loopn ⬝* apn_pid n,
  end

  @[hott] def loop_pequiv_loop_rfl (A : Type*) :
    loop_pequiv_loop (pequiv.refl A) ~* pequiv.refl (Ω A) :=
  loopn_pequiv_loopn_rfl 1 A

  @[hott] def apn_pinv (n : ℕ) {A B : Type*} (f : A ≃* B) :
    Ω→[n] f⁻¹ᵉ* ~* (loopn_pequiv_loopn n f)⁻¹ᵉ* :=
  by reflexivity

  @[hott] def pmap_functor {A A' B B' : Type*} (f : A' →* A) (g : B →* B') :
    ppmap A B →* ppmap A' B' :=
  pmap.mk (λh, g ∘* h ∘* f)
    abstract begin
      fapply eq_of_phomotopy, fapply phomotopy.mk,
      { esimp, intro a, exact respect_pt g},
      { rewrite [▸*, ap_constant], exact !idp_con⁻¹ }
    end end

  @[hott] def pequiv_pinverse (A : Type*) : Ω A ≃* Ω A :=
  pequiv_of_pmap pinverse !is_equiv_eq_inverse

  @[hott] def pequiv_of_eq_pt {A : Type _} {a a' : A} (p : a = a') :
    pointed.MK A a ≃* pointed.MK A a' :=
  pequiv_of_pmap (pmap_of_eq_pt p) !is_equiv_id

  @[hott] def pointed_eta_pequiv (A : Type*) : A ≃* pointed.MK A pt :=
  pequiv.mk id !is_equiv_id idp

  /- every pointed map is homotopic to one of the form `pmap_of_map _ _`, up to some
     pointed equivalences -/
  @[hott] def phomotopy_pmap_of_map {A B : Type*} (f : A →* B) :
    (pointed_eta_pequiv B ⬝e* (pequiv_of_eq_pt (respect_pt f))⁻¹ᵉ*) ∘* f ∘*
      (pointed_eta_pequiv A)⁻¹ᵉ* ~* pmap_of_map f pt :=
  begin
    fapply phomotopy.mk,
    { reflexivity},
    { symmetry, exact (!ap_id ⬝ !idp_con) ◾ (!idp_con ⬝ !ap_id) ⬝ !con.right_inv }
  end

  /- properties of iterated loop space -/
  variable (A)
  @[hott] def loopn_succ_in (n : ℕ) : Ω[succ n] A ≃* Ω[n] (Ω A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact loop_pequiv_loop IH}
  end

  @[hott] def loopn_add (n m : ℕ) : Ω[n] (Ω[m] A) ≃* Ω[m+n] (A) :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact loop_pequiv_loop IH}
  end

  @[hott] def loopn_succ_out (n : ℕ) : Ω[succ n] A ≃* Ω(Ω[n] A)  :=
  by reflexivity

  variable {A}

  @[hott] def loopn_succ_in_con {n : ℕ} (p q : Ω[succ (succ n)] A) :
    loopn_succ_in A (succ n) (p ⬝ q) =
    loopn_succ_in A (succ n) p ⬝ loopn_succ_in A (succ n) q :=
  !loop_pequiv_loop_con

  @[hott] def loopn_loop_irrel (p : point A = point A) : Ω(pointed.Mk p) = Ω[2] A :=
  begin
    intros, fapply pType_eq,
    { esimp, transitivity _,
      apply eq_equiv_fn_eq_of_equiv (equiv_eq_closed_right _ p⁻¹),
      esimp, apply eq_equiv_eq_closed, apply con.right_inv, apply con.right_inv},
    { esimp, apply con.left_inv}
  end

  @[hott] def loopn_space_loop_irrel (n : ℕ) (p : point A = point A)
    : Ω[succ n](pointed.Mk p) = Ω[succ (succ n)] A :> pType :=
  calc
    Ω[succ n](pointed.Mk p) = Ω[n](Ω (pointed.Mk p)) : eq_of_pequiv !loopn_succ_in
      ... = Ω[n] (Ω[2] A)                            : loopn_loop_irrel
      ... = Ω[2+n] A                                 : eq_of_pequiv !loopn_add
      ... = Ω[n+2] A                                 : by rewrite [algebra.add.comm]

  @[hott] def apn_succ_phomotopy_in (n : ℕ) (f : A →* B) :
    loopn_succ_in B n ∘* Ω→[n + 1] f ~* Ω→[n] (Ω→ f) ∘* loopn_succ_in A n :=
  begin
    induction n with n IH,
    { reflexivity},
    { exact !ap1_pcompose⁻¹* ⬝* ap1_phomotopy IH ⬝* !ap1_pcompose}
  end

  @[hott] def loopn_succ_in_natural {A B : Type*} (n : ℕ) (f : A →* B) :
    loopn_succ_in B n ∘* Ω→[n+1] f ~* Ω→[n] (Ω→ f) ∘* loopn_succ_in A n :=
  !apn_succ_phomotopy_in

  @[hott] def loopn_succ_in_inv_natural {A B : Type*} (n : ℕ) (f : A →* B) :
    Ω→[n + 1] f ∘* (loopn_succ_in A n)⁻¹ᵉ* ~* (loopn_succ_in B n)⁻¹ᵉ* ∘* Ω→[n] (Ω→ f):=
  begin
    apply pinv_right_phomotopy_of_phomotopy,
    refine _ ⬝* !passoc⁻¹*,
    apply phomotopy_pinv_left_of_phomotopy,
    apply apn_succ_phomotopy_in
  end

end pointed
