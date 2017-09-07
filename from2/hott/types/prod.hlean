/-
Copyright (c) 2014 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Jakob von Raumer

Ported from Coq HoTT
Theorems about products
-/

open eq equiv is_equiv is_trunc prod prod.ops unit

variables {A A' B B' C D : Type _} {P Q : A → Type _}
          {a a' a'' : A} {b b₁ b₂ b' b'' : B} {u v w : A × B}

namespace prod

  /- Paths in a product space -/

  protected @[hott] def eta (u : A × B) : (pr₁ u, pr₂ u) = u :=
  by cases u; reflexivity

  @[hott] def pair_eq (pa : a = a') (pb : b = b') : (a, b) = (a', b') :=
  ap011 prod.mk pa pb

  @[hott] def prod_eq (H₁ : u.1 = v.1) (H₂ : u.2 = v.2) : u = v :=
  by cases u; cases v; exact pair_eq H₁ H₂

  @[hott] def eq_pr1 (p : u = v) : u.1 = v.1 :=
  ap pr1 p

  @[hott] def eq_pr2 (p : u = v) : u.2 = v.2 :=
  ap pr2 p

  namespace ops
    postfix `..1`:(max+1) := eq_pr1
    postfix `..2`:(max+1) := eq_pr2
  end ops
  open ops

  protected @[hott] def ap_pr1 (p : u = v) : ap pr1 p = p..1 := idp
  protected @[hott] def ap_pr2 (p : u = v) : ap pr2 p = p..2 := idp

  @[hott] def pair_prod_eq (p : u.1 = v.1) (q : u.2 = v.2)
    : ((prod_eq p q)..1, (prod_eq p q)..2) = (p, q) :=
  by induction u; induction v; esimp at *; induction p; induction q; reflexivity

  @[hott] def prod_eq_pr1 (p : u.1 = v.1) (q : u.2 = v.2) : (prod_eq p q)..1 = p :=
  (pair_prod_eq p q)..1

  @[hott] def prod_eq_pr2 (p : u.1 = v.1) (q : u.2 = v.2) : (prod_eq p q)..2 = q :=
  (pair_prod_eq p q)..2

  @[hott] def prod_eq_eta (p : u = v) : prod_eq (p..1) (p..2) = p :=
  by induction p; induction u; reflexivity

  -- the uncurried version of prod_eq. We will prove that this is an equivalence
  @[hott] def prod_eq_unc (H : u.1 = v.1 × u.2 = v.2) : u = v :=
  by cases H with H₁ H₂; exact prod_eq H₁ H₂

  @[hott] def pair_prod_eq_unc : Π(pq : u.1 = v.1 × u.2 = v.2),
    ((prod_eq_unc pq)..1, (prod_eq_unc pq)..2) = pq
  | pair_prod_eq_unc (pq₁, pq₂) := pair_prod_eq pq₁ pq₂

  @[hott] def prod_eq_unc_pr1 (pq : u.1 = v.1 × u.2 = v.2) : (prod_eq_unc pq)..1 = pq.1 :=
  (pair_prod_eq_unc pq)..1

  @[hott] def prod_eq_unc_pr2 (pq : u.1 = v.1 × u.2 = v.2) : (prod_eq_unc pq)..2 = pq.2 :=
  (pair_prod_eq_unc pq)..2

  @[hott] def prod_eq_unc_eta (p : u = v) : prod_eq_unc (p..1, p..2) = p :=
  prod_eq_eta p

  @[hott] def is_equiv_prod_eq [instance] (u v : A × B)
    : is_equiv (prod_eq_unc : u.1 = v.1 × u.2 = v.2 → u = v) :=
  adjointify prod_eq_unc
             (λp, (p..1, p..2))
             prod_eq_unc_eta
             pair_prod_eq_unc

  @[hott] def prod_eq_equiv (u v : A × B) : (u = v) ≃ (u.1 = v.1 × u.2 = v.2) :=
  (equiv.mk prod_eq_unc _)⁻¹ᵉ

  @[hott] def pair_eq_pair_equiv (a a' : A) (b b' : B) :
    ((a, b) = (a', b')) ≃ (a = a' × b = b') :=
  prod_eq_equiv (a, b) (a', b')

  @[hott] def ap_prod_mk_left (p : a = a') : ap (λa, prod.mk a b) p = prod_eq p idp :=
  ap_eq_ap011_left prod.mk p b

  @[hott] def ap_prod_mk_right (p : b = b') : ap (λb, prod.mk a b) p = prod_eq idp p :=
  ap_eq_ap011_right prod.mk a p

  @[hott] def pair_eq_eta {A B : Type _} {u v : A × B}
    (p : u = v) : pair_eq (p..1) (p..2) = prod.eta u ⬝ p ⬝ (prod.eta v)⁻¹ :=
  by induction p; induction u; reflexivity

  @[hott] def prod_eq_eq {A B : Type _} {u v : A × B}
    {p₁ q₁ : u.1 = v.1} {p₂ q₂ : u.2 = v.2} (α₁ : p₁ = q₁) (α₂ : p₂ = q₂)
    : prod_eq p₁ p₂ = prod_eq q₁ q₂ :=
  by cases α₁; cases α₂; reflexivity

  @[hott] def prod_eq_assemble {A B : Type _} {u v : A × B}
    {p q : u = v} (α₁ : p..1 = q..1) (α₂ : p..2 = q..2) : p = q :=
  (prod_eq_eta p)⁻¹ ⬝ prod.prod_eq_eq α₁ α₂ ⬝ prod_eq_eta q

  @[hott] def eq_pr1_concat {A B : Type _} {u v w : A × B}
    (p : u = v) (q : v = w)
    : (p ⬝ q)..1 = p..1 ⬝ q..1 :=
  by cases q; reflexivity

  @[hott] def eq_pr2_concat {A B : Type _} {u v w : A × B}
    (p : u = v) (q : v = w)
    : (p ⬝ q)..2 = p..2 ⬝ q..2 :=
  by cases q; reflexivity

  /- Groupoid structure -/
  @[hott] def prod_eq_inv (p : a = a') (q : b = b') : (prod_eq p q)⁻¹ = prod_eq p⁻¹ q⁻¹ :=
  by cases p; cases q; reflexivity

  @[hott] def prod_eq_concat (p : a = a') (p' : a' = a'') (q : b = b') (q' : b' = b'')
    : prod_eq p q ⬝ prod_eq p' q' = prod_eq (p ⬝ p') (q ⬝ q') :=
  by cases p; cases q; cases p'; cases q'; reflexivity

  @[hott] def prod_eq_concat_idp (p : a = a') (q : b = b')
    : prod_eq p idp ⬝ prod_eq idp q = prod_eq p q :=
  by cases p; cases q; reflexivity

  /- Transport -/

  @[hott] def prod_transport (p : a = a') (u : P a × Q a)
    : p ▸ u = (p ▸ u.1, p ▸ u.2) :=
  by induction p; induction u; reflexivity

  @[hott] def prod_eq_transport (p : a = a') (q : b = b') {R : A × B → Type _} (r : R (a, b))
    : (prod_eq p q) ▸ r = p ▸ q ▸ r :=
  by induction p; induction q; reflexivity

  /- Pathovers -/

  @[hott] def etao (p : a = a') (bc : P a × Q a) : bc =[p] (p ▸ bc.1, p ▸ bc.2) :=
  by induction p; induction bc; apply idpo

  @[hott] def prod_pathover (p : a = a') (u : P a × Q a) (v : P a' × Q a')
    (r : u.1 =[p] v.1) (s : u.2 =[p] v.2) : u =[p] v :=
  begin
    induction u, induction v, esimp at *, induction r,
    induction s using idp_rec_on,
    apply idpo
  end

  open prod.ops
  @[hott] def prod_pathover_equiv {A : Type _} {B C : A → Type _} {a a' : A} (p : a = a')
    (x : B a × C a) (x' : B a' × C a') : x =[p] x' ≃ x.1 =[p] x'.1 × x.2 =[p] x'.2 :=
  begin
    fapply equiv.MK,
    { intro q, induction q, constructor: constructor },
    { intro v, induction v with q r, exact prod_pathover _ _ _ q r },
    { intro v, induction v with q r, induction x with b c, induction x' with b' c',
      esimp at *, induction q, refine idp_rec_on r _, reflexivity },
    { intro q, induction q, induction x with b c, reflexivity }
  end


  /-
    TODO:
    * define the projections from the type u =[p] v
    * show that the uncurried version of prod_pathover is an equivalence
  -/

  /- Functorial action -/

  variables (f : A → A') (g : B → B')
  @[hott] def prod_functor (u : A × B) : A' × B' :=
  (f u.1, g u.2)

  @[hott] def ap_prod_functor (p : u.1 = v.1) (q : u.2 = v.2)
    : ap (prod_functor f g) (prod_eq p q) = prod_eq (ap f p) (ap g q) :=
  by induction u; induction v; esimp at *; induction p; induction q; reflexivity

  /- Helpers for functions of two arguments -/
  @[hott] def ap_diagonal {a a' : A} (p : a = a')
    : ap (λx : A, (x,x)) p = prod_eq p p :=
  by cases p; constructor

  @[hott] def ap_binary (m : A → B → C) (p : a = a') (q : b = b')
    : ap (λz : A × B, m z.1 z.2) (prod_eq p q)
    = ap (m a) q ⬝ ap (λx : A, m x b') p :=
  by cases p; cases q; constructor

  @[hott] def ap_prod_elim {A B C : Type _} {a a' : A} {b b' : B} (m : A → B → C)
    (p : a = a') (q : b = b') : ap (prod.rec m) (prod_eq p q)
    = ap (m a) q ⬝ ap (λx : A, m x b') p :=
  by cases p; cases q; constructor

  @[hott] def ap_prod_elim_idp {A B C : Type _} {a a' : A} (m : A → B → C)
    (p : a = a') (b : B) : ap (prod.rec m) (prod_eq p idp) = ap (λx : A, m x b) p :=
  ap_prod_elim m p idp ⬝ !idp_con

  /- Equivalences -/

  @[hott] def is_equiv_prod_functor [instance] [H : is_equiv f] [H : is_equiv g]
    : is_equiv (prod_functor f g) :=
  begin
    apply adjointify _ (prod_functor f⁻¹ g⁻¹),
      intro u, induction u, rewrite [▸*,right_inv f,right_inv g],
      intro u, induction u, rewrite [▸*,left_inv f,left_inv g],
  end

  @[hott] def prod_equiv_prod_of_is_equiv [H : is_equiv f] [H : is_equiv g]
    : A × B ≃ A' × B' :=
  equiv.mk (prod_functor f g) _

  @[hott] def prod_equiv_prod (f : A ≃ A') (g : B ≃ B') : A × B ≃ A' × B' :=
  equiv.mk (prod_functor f g) _

  -- rename
  @[hott] def prod_equiv_prod_left (g : B ≃ B') : A × B ≃ A × B' :=
  prod_equiv_prod equiv.rfl g

  -- rename
  @[hott] def prod_equiv_prod_right (f : A ≃ A') : A × B ≃ A' × B :=
  prod_equiv_prod f equiv.rfl

  /- Symmetry -/

  @[hott] def is_equiv_flip [instance] (A B : Type _)
    : is_equiv (flip : A × B → B × A) :=
  adjointify flip
             flip
             (λu, destruct u (λb a, idp))
             (λu, destruct u (λa b, idp))

  @[hott] def prod_comm_equiv (A B : Type _) : A × B ≃ B × A :=
  equiv.mk flip _

  /- Associativity -/

  @[hott] def prod_assoc_equiv (A B C : Type _) : A × (B × C) ≃ (A × B) × C :=
  begin
    fapply equiv.MK,
    { intro z, induction z with a z, induction z with b c, exact (a, b, c)},
    { intro z, induction z with z c, induction z with a b, exact (a, (b, c))},
    { intro z, induction z with z c, induction z with a b, reflexivity},
    { intro z, induction z with a z, induction z with b c, reflexivity},
  end

  @[hott] def prod_contr_equiv (A B : Type _) [H : is_contr B] : A × B ≃ A :=
  equiv.MK pr1
           (λx, (x, !center))
           (λx, idp)
           (λx, by cases x with a b; exact pair_eq idp !center_eq)

  @[hott] def prod_unit_equiv (A : Type _) : A × unit ≃ A :=
  !prod_contr_equiv

  @[hott] def prod_empty_equiv (A : Type _) : A × empty ≃ empty :=
  begin
    fapply equiv.MK,
    { intro x, cases x with a e, cases e },
    { intro e, cases e },
    { intro e, cases e },
    { intro x, cases x with a e, cases e }
  end

  /- Universal mapping properties -/
  @[hott] def is_equiv_prod_rec [instance] (P : A × B → Type _)
    : is_equiv (prod.rec : (Πa b, P (a, b)) → Πu, P u) :=
  adjointify _
             (λg a b, g (a, b))
             (λg, eq_of_homotopy (λu, by induction u;reflexivity))
             (λf, idp)

  @[hott] def equiv_prod_rec (P : A × B → Type _) : (Πa b, P (a, b)) ≃ (Πu, P u) :=
  equiv.mk prod.rec _

  @[hott] def imp_imp_equiv_prod_imp (A B C : Type _) : (A → B → C) ≃ (A × B → C) :=
  !equiv_prod_rec

  @[hott] def prod_corec_unc {P Q : A → Type _} (u : (Πa, P a) × (Πa, Q a)) (a : A)
    : P a × Q a :=
  (u.1 a, u.2 a)

  @[hott] def is_equiv_prod_corec (P Q : A → Type _)
    : is_equiv (prod_corec_unc : (Πa, P a) × (Πa, Q a) → Πa, P a × Q a) :=
  adjointify _
             (λg, (λa, (g a).1, λa, (g a).2))
             (by intro g; apply eq_of_homotopy; intro a; esimp; induction (g a); reflexivity)
             (by intro h; induction h with f g; reflexivity)

  @[hott] def equiv_prod_corec (P Q : A → Type _)
    : ((Πa, P a) × (Πa, Q a)) ≃ (Πa, P a × Q a) :=
  equiv.mk _ !is_equiv_prod_corec

  @[hott] def imp_prod_imp_equiv_imp_prod (A B C : Type _)
    : (A → B) × (A → C) ≃ (A → (B × C)) :=
  !equiv_prod_corec

  @[hott] theorem is_trunc_prod (A B : Type _) (n : trunc_index) [HA : is_trunc n A] [HB : is_trunc n B]
    : is_trunc n (A × B) :=
  begin
    revert A B HA HB, induction n with n IH, all_goals intros A B HA HB,
    { fapply is_contr.mk,
        exact (!center, !center),
        intro u, apply prod_eq, all_goals apply center_eq},
    { apply is_trunc_succ_intro, intros u v,
      apply is_trunc_equiv_closed_rev, apply prod_eq_equiv,
      exact IH _ _ _ _}
  end

end prod

attribute prod.is_trunc_prod [instance] [priority 1510]

namespace prod
  /- pointed products -/
  open pointed
  @[hott] def pointed_prod [instance] (A B : Type _) [H1 : pointed A] [H2 : pointed B]
      : pointed (A × B) :=
  pointed.mk (pt,pt)

  @[hott] def pprod (A B : Type*) : Type* :=
  pointed.mk' (A × B)

  infixr ` ×* `:35 := pprod

  @[hott] def ppr1 {A B : Type*} : A ×* B →* A :=
  pmap.mk pr1 idp

  @[hott] def ppr2 {A B : Type*} : A ×* B →* B :=
  pmap.mk pr2 idp

  @[hott] def tprod {n : trunc_index} (A B : n-Type _) : n-Type _ :=
  trunctype.mk (A × B) _

  infixr `×t`:30 := tprod

  @[hott] def ptprod {n : ℕ₋₂} (A B : n-Type*) : n-Type* :=
  ptrunctype.mk' n (A × B)

  @[hott] def pprod_functor {A B C D : Type*} (f : A →* C) (g : B →* D) : A ×* B →* C ×* D :=
  pmap.mk (prod_functor f g) (prod_eq (respect_pt f) (respect_pt g))


end prod
