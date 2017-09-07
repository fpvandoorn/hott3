/-
Copyright (c) 2014-15 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Partially ported from Coq HoTT
Theorems about pi-types (dependent function spaces)
-/

import types.sigma arity cubical.square

open eq equiv is_equiv funext sigma unit bool is_trunc prod function sigma.ops

namespace pi
  variables {A A' : Type _} {B : A → Type _} {B' : A' → Type _} {C : Πa, B a → Type _}
            {D : Πa b, C a b → Type _}
            {a a' a'' : A} {b b₁ b₂ : B a} {b' : B a'} {b'' : B a''} {f g : Πa, B a}

  /- Paths -/

  /-
    Paths [p : f ≈ g] in a function type [Πx:X, P x] are equivalent to functions taking values
    in path types, [H : Πx:X, f x ≈ g x], or concisely, [H : f ~ g].

    This equivalence, however, is just the combination of [apd10] and function extensionality
    [funext], and as such, [eq_of_homotopy]

    Now we show how these things compute.
  -/

  @[hott] def apd10_eq_of_homotopy (h : f ~ g) : apd10 (eq_of_homotopy h) ~ h :=
  apd10 (right_inv apd10 h)

  @[hott] def eq_of_homotopy_eta (p : f = g) : eq_of_homotopy (apd10 p) = p :=
  left_inv apd10 p

  @[hott] def eq_of_homotopy_idp (f : Πa, B a) : eq_of_homotopy (λx : A, refl (f x)) = refl f :=
  !eq_of_homotopy_eta

  /- homotopy.symm is an equivalence -/
  @[hott] def is_equiv_homotopy_symm : is_equiv (homotopy.symm : f ~ g → g ~ f) :=
  begin
    fapply adjointify homotopy.symm homotopy.symm,
    { intro p, apply eq_of_homotopy, intro a,
      unfold homotopy.symm, apply inv_inv },
    { intro p, apply eq_of_homotopy, intro a,
      unfold homotopy.symm, apply inv_inv }
  end

  /-
    The identification of the path space of a dependent function space,
    up to equivalence, is of course just funext.
  -/

  @[hott] def eq_equiv_homotopy (f g : Πx, B x) : (f = g) ≃ (f ~ g) :=
  equiv.mk apd10 _

  @[hott] def pi_eq_equiv (f g : Πx, B x) : (f = g) ≃ (f ~ g) := !eq_equiv_homotopy

  @[hott] def is_equiv_eq_of_homotopy (f g : Πx, B x)
    : is_equiv (eq_of_homotopy : f ~ g → f = g) :=
  _

  @[hott] def homotopy_equiv_eq (f g : Πx, B x) : (f ~ g) ≃ (f = g) :=
  equiv.mk eq_of_homotopy _


  /- Transport -/

  @[hott] def pi_transport (p : a = a') (f : Π(b : B a), C a b)
    : (transport (λa, Π(b : B a), C a b) p f) ~ (λb, !tr_inv_tr ▸ (p ▸D (f (p⁻¹ ▸ b)))) :=
  by induction p; reflexivity

  /- A special case of [transport_pi] where the type [B] does not depend on [A],
      and so it is just a fixed type [B]. -/
  @[hott] def pi_transport_constant {C : A → A' → Type _} (p : a = a') (f : Π(b : A'), C a b) (b : A')
    : (transport _ p f) b = p ▸ (f b) :=
  by induction p; reflexivity

  /- Pathovers -/

  @[hott] def pi_pathover {f : Πb, C a b} {g : Πb', C a' b'} {p : a = a'}
    (r : Π(b : B a) (b' : B a') (q : b =[p] b'), f b =[apd011 C p q] g b') : f =[p] g :=
  begin
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    apply eq_of_pathover_idp, apply r
  end

  @[hott] def pi_pathover_left {f : Πb, C a b} {g : Πb', C a' b'} {p : a = a'}
    (r : Π(b : B a), f b =[apd011 C p !pathover_tr] g (p ▸ b)) : f =[p] g :=
  begin
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    apply eq_of_pathover_idp, apply r
  end

  @[hott] def pi_pathover_right {f : Πb, C a b} {g : Πb', C a' b'} {p : a = a'}
    (r : Π(b' : B a'), f (p⁻¹ ▸ b') =[apd011 C p !tr_pathover] g b') : f =[p] g :=
  begin
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    apply eq_of_pathover_idp, apply r
  end

  @[hott] def pi_pathover_constant {C : A → A' → Type _} {f : Π(b : A'), C a b}
    {g : Π(b : A'), C a' b} {p : a = a'}
    (r : Π(b : A'), f b =[p] g b) : f =[p] g :=
  begin
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    exact eq_of_pathover_idp (r b),
  end

  -- a version where C is uncurried, but where the conclusion of r is still a proper pathover
  -- instead of a heterogenous equality
  @[hott] def pi_pathover' {C : (Σa, B a) → Type _} {f : Πb, C ⟨a, b⟩} {g : Πb', C ⟨a', b'⟩}
    {p : a = a'} (r : Π(b : B a) (b' : B a') (q : b =[p] b'), f b =[dpair_eq_dpair p q] g b')
    : f =[p] g :=
  begin
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    apply (@eq_of_pathover_idp _ C), exact (r b b (pathover.idpatho b)),
  end

  @[hott] def pi_pathover_left' {C : (Σa, B a) → Type _} {f : Πb, C ⟨a, b⟩} {g : Πb', C ⟨a', b'⟩}
    {p : a = a'} (r : Π(b : B a), f b =[dpair_eq_dpair p !pathover_tr] g (p ▸ b))
    : f =[p] g :=
  begin
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    apply eq_of_pathover_idp, esimp at r, exact !pathover_ap (r b)
  end

  @[hott] def pi_pathover_right' {C : (Σa, B a) → Type _} {f : Πb, C ⟨a, b⟩} {g : Πb', C ⟨a', b'⟩}
    {p : a = a'} (r : Π(b' : B a'), f (p⁻¹ ▸ b') =[dpair_eq_dpair p !tr_pathover] g b')
    : f =[p] g :=
  begin
    cases p, apply pathover_idp_of_eq,
    apply eq_of_homotopy, intro b,
    apply eq_of_pathover_idp, esimp at r, exact !pathover_ap (r b)
  end


  /- Maps on paths -/

  /- The action of maps given by lambda. -/
  @[hott] def ap_lambdaD {C : A' → Type _} (p : a = a') (f : Πa b, C b) :
    ap (λa b, f a b) p = eq_of_homotopy (λb, ap (λa, f a b) p) :=
  begin
    apply (eq.rec_on p),
    apply inverse,
    apply eq_of_homotopy_idp
  end

  /- Dependent paths -/

  /- with more implicit arguments the conclusion of the following @[hott] theorem is
     (Π(b : B a), transportD B C p b (f b) = g (transport B p b)) ≃
     (transport (λa, Π(b : B a), C a b) p f = g) -/
  @[hott] def heq_piD (p : a = a') (f : Π(b : B a), C a b)
    (g : Π(b' : B a'), C a' b') : (Π(b : B a), p ▸D (f b) = g (p ▸ b)) ≃ (p ▸ f = g) :=
  eq.rec_on p (λg, !homotopy_equiv_eq) g

  @[hott] def heq_pi {C : A → Type _} (p : a = a') (f : Π(b : B a), C a)
    (g : Π(b' : B a'), C a') : (Π(b : B a), p ▸ (f b) = g (p ▸ b)) ≃ (p ▸ f = g) :=
  eq.rec_on p (λg, !homotopy_equiv_eq) g


  section
  open sigma sigma.ops
  /- more implicit arguments:
  (Π(b : B a), transport C (sigma_eq p idp) (f b) = g (p ▸ b)) ≃
  (Π(b : B a), transportD B (λ(a : A) (b : B a), C ⟨a, b⟩) p b (f b) = g (transport B p b)) -/
  @[hott] def heq_pi_sigma {C : (Σa, B a) → Type _} (p : a = a')
    (f : Π(b : B a), C ⟨a, b⟩) (g : Π(b' : B a'), C ⟨a', b'⟩) :
    (Π(b : B a), (sigma_eq p !pathover_tr) ▸ (f b) = g (p ▸ b)) ≃
    (Π(b : B a), p ▸D (f b) = g (p ▸ b)) :=
  eq.rec_on p (λg, !equiv.rfl) g
  end

  /- Functorial action -/
  variables (f0 : A' → A) (f1 : Π(a':A'), B (f0 a') → B' a')

  /- The functoriality of [forall] is slightly subtle: it is contravariant in the domain type and covariant in the codomain, but the codomain is dependent on the domain. -/

  @[hott] def pi_functor : (Π(a:A), B a) → (Π(a':A'), B' a') :=
  λg a', f1 a' (g (f0 a'))

  @[hott] def pi_functor_left (B : A → Type _) : (Π(a:A), B a) → (Π(a':A'), B (f0 a')) :=
  pi_functor f0 (λa, id)

  @[hott] def pi_functor_right {B' : A → Type _} (f1 : Π(a:A), B a → B' a)
    : (Π(a:A), B a) → (Π(a:A), B' a) :=
  pi_functor id f1

  @[hott] def ap_pi_functor {g g' : Π(a:A), B a} (h : g ~ g')
    : ap (pi_functor f0 f1) (eq_of_homotopy h)
      = eq_of_homotopy (λa':A', (ap (f1 a') (h (f0 a')))) :=
  begin
  apply (is_equiv_rect (@apd10 A B g g')), intro p, clear h,
  cases p,
  apply concat,
    exact (ap (ap (pi_functor f0 f1)) (eq_of_homotopy_idp g)),
    apply symm, apply eq_of_homotopy_idp
  end

  /- Equivalences -/

  @[hott] def is_equiv_pi_functor [instance] [H0 : is_equiv f0]
    [H1 : Πa', is_equiv (f1 a')] : is_equiv (pi_functor f0 f1) :=
  begin
    apply (adjointify (pi_functor f0 f1) (pi_functor f0⁻¹
          (λ(a : A) (b' : B' (f0⁻¹ a)), transport B (right_inv f0 a) ((f1 (f0⁻¹ a))⁻¹ b')))),
    begin
      intro h, apply eq_of_homotopy, intro a', esimp,
      rewrite [adj f0 a',-tr_compose,fn_tr_eq_tr_fn _ f1,right_inv (f1 _)],
      apply apdt
    end,
    begin
      intro h, apply eq_of_homotopy, intro a, esimp,
      rewrite [left_inv (f1 _)],
      apply apdt
    end
  end

  @[hott] def pi_equiv_pi_of_is_equiv [H : is_equiv f0]
    [H1 : Πa', is_equiv (f1 a')] : (Πa, B a) ≃ (Πa', B' a') :=
  equiv.mk (pi_functor f0 f1) _

  @[hott] def pi_equiv_pi (f0 : A' ≃ A) (f1 : Πa', (B (to_fun f0 a') ≃ B' a'))
    : (Πa, B a) ≃ (Πa', B' a') :=
  pi_equiv_pi_of_is_equiv (to_fun f0) (λa', to_fun (f1 a'))

  @[hott] def pi_equiv_pi_right {P Q : A → Type _} (g : Πa, P a ≃ Q a)
    : (Πa, P a) ≃ (Πa, Q a) :=
  pi_equiv_pi equiv.rfl g

  /- Equivalence if one of the types is contractible -/

  @[hott] def pi_equiv_of_is_contr_left (B : A → Type _) [H : is_contr A]
    : (Πa, B a) ≃ B (center A) :=
  begin
    fapply equiv.MK,
    { intro f, exact f (center A)},
    { intros b a, exact center_eq a ▸ b},
    { intro b, rewrite [prop_eq_of_is_contr (center_eq (center A)) idp]},
    { intro f, apply eq_of_homotopy, intro a, induction (center_eq a),
      rewrite [prop_eq_of_is_contr (center_eq (center A)) idp]}
  end

  @[hott] def pi_equiv_of_is_contr_right [H : Πa, is_contr (B a)]
    : (Πa, B a) ≃ unit :=
  begin
    fapply equiv.MK,
    { intro f, exact star},
    { intros u a, exact !center},
    { intro u, induction u, reflexivity},
    { intro f, apply eq_of_homotopy, intro a, apply is_prop.elim}
  end

  /- Interaction with other type constructors -/

  -- most of these are in the file of the other type constructor

  @[hott] def pi_empty_left (B : empty → Type _) : (Πx, B x) ≃ unit :=
  begin
    fapply equiv.MK,
    { intro f, exact star},
    { intros x y, contradiction},
    { intro x, induction x, reflexivity},
    { intro f, apply eq_of_homotopy, intro y, contradiction},
  end

  @[hott] def pi_unit_left (B : unit → Type _) : (Πx, B x) ≃ B star :=
  !pi_equiv_of_is_contr_left

  @[hott] def pi_bool_left (B : bool → Type _) : (Πx, B x) ≃ B ff × B tt :=
  begin
    fapply equiv.MK,
    { intro f, exact (f ff, f tt)},
    { intros x b, induction x, induction b: assumption},
    { intro x, induction x, reflexivity},
    { intro f, apply eq_of_homotopy, intro b, induction b: reflexivity},
  end

  /- Truncatedness: any dependent product of n-types is an n-type -/

  @[hott] theorem is_trunc_pi (B : A → Type _) (n : trunc_index)
      [H : ∀a, is_trunc n (B a)] : is_trunc n (Πa, B a) :=
  begin
    revert B H,
    eapply (trunc_index.rec_on n),
      {intro B H,
        fapply is_contr.mk,
          intro a, apply center,
          intro f, apply eq_of_homotopy,
            intro x, apply (center_eq (f x))},
      {intro n IH B H,
        fapply is_trunc_succ_intro, intros f g,
          fapply is_trunc_equiv_closed,
            apply equiv.symm, apply eq_equiv_homotopy,
            apply IH,
              intro a,
              show is_trunc n (f a = g a), from
              is_trunc_eq n (f a) (g a)}
  end
  local attribute is_trunc_pi [instance]
  @[hott] theorem is_trunc_pi_eq [instance] [priority 500] (n : trunc_index) (f g : Πa, B a)
      [H : ∀a, is_trunc n (f a = g a)] : is_trunc n (f = g) :=
  begin
    apply is_trunc_equiv_closed_rev,
    apply eq_equiv_homotopy
  end

  @[hott] theorem is_trunc_not [instance] (n : trunc_index) (A : Type _) : is_trunc (n.+1) ¬A :=
  by unfold not;exact _

  @[hott] theorem is_prop_pi_eq [instance] [priority 490] (a : A) : is_prop (Π(a' : A), a = a') :=
  is_prop_of_imp_is_contr
  ( assume (f : Πa', a = a'),
    have is_contr A, from is_contr.mk a f,
    by exact _) /- force type clas resolution -/

  @[hott] theorem is_prop_neg (A : Type _) : is_prop (¬A) := _
  local attribute ne [reducible]
  @[hott] theorem is_prop_ne [instance] {A : Type _} (a b : A) : is_prop (a ≠ b) := _

  @[hott] def is_contr_pi_of_neg {A : Type _} (B : A → Type _) (H : ¬ A) : is_contr (Πa, B a) :=
  begin
    apply is_contr.mk (λa, empty.elim (H a)), intro f, apply eq_of_homotopy, intro x, contradiction
  end

  /- Symmetry of Π -/
  @[hott] def is_equiv_flip [instance] {P : A → A' → Type _}
    : is_equiv (@function.flip A A' P) :=
  begin
    fapply is_equiv.mk,
    exact (@function.flip _ _ (function.flip P)),
    repeat (intro f; apply idp)
  end

  @[hott] def pi_comm_equiv {P : A → A' → Type _} : (Πa b, P a b) ≃ (Πb a, P a b) :=
  equiv.mk (@function.flip _ _ P) _

  /- Dependent functions are equivalent to nondependent functions into the total space together
     with a homotopy -/
  @[hott] def pi_equiv_arrow_sigma_right {A : Type _} {B : A → Type _} (f : Πa, B a) :
    Σ(f : A → Σa, B a), pr1 ∘ f ~ id :=
  ⟨λa, ⟨a, f a⟩, λa, idp⟩

  @[hott] def pi_equiv_arrow_sigma_left.{u v} {A : Type u} {B : A → Type v}
    (v : Σ(f : A → Σa, B a), pr1 ∘ f ~ id) (a : A) : B a :=
  transport B (v.2 a) (v.1 a).2

  open funext
  @[hott] def pi_equiv_arrow_sigma {A : Type _} (B : A → Type _) :
    (Πa, B a) ≃ Σ(f : A → Σa, B a), pr1 ∘ f ~ id :=
  begin
    fapply equiv.MK,
    { exact pi_equiv_arrow_sigma_right},
    { exact pi_equiv_arrow_sigma_left},
    { intro v, induction v with f p, fapply sigma_eq: esimp,
      { apply eq_of_homotopy, intro a, fapply sigma_eq: esimp,
        { exact (p a)⁻¹},
        { apply inverseo, apply pathover_tr}},
      { apply pi_pathover_constant, intro a, apply eq_pathover_constant_right,
        refine ap_compose (λf, f a) _ _ ⬝ph _,
        refine ap02 _ !compose_eq_of_homotopy ⬝ph _,
        refine !ap_eq_apd10 ⬝ph _,
        refine apd10 (right_inv apd10 _) a ⬝ph _,
        esimp, refine !sigma_eq_pr1 ⬝ph _, apply square_of_eq, exact !con.left_inv⁻¹}},
    { intro a, reflexivity}
  end




end pi

attribute pi.is_trunc_pi [instance] [priority 1520]

namespace pi

  /- pointed pi types -/
  open pointed

  @[hott] def pointed_pi [instance] {A : Type _} (P : A → Type _) [H : Πx, pointed (P x)]
      : pointed (Πx, P x) :=
  pointed.mk (λx, pt)

end pi
