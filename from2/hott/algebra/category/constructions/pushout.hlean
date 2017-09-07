/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

The pushout of categories

The morphisms in the pushout of two categories is defined as a quotient on lists of composable
morphisms. For this we use the notion of paths in a graph.
-/

import ..category ..nat_trans hit.set_quotient algebra.relation ..groupoid algebra.graph
       .functor

open eq is_trunc functor trunc sum set_quotient relation iso category sigma nat nat_trans

  /- we first define the categorical structure on paths in a graph -/
namespace paths
  section
  parameters {A : Type _} {R : A → A → Type _}
    (Q : Π⦃a a' : A⦄, paths R a a' → paths R a a' → Type _)
  variables ⦃a a' a₁ a₂ a₃ a₄ : A⦄
  @[hott] def paths_trel (l l' : paths R a a') : Prop :=
  ∥paths_rel Q l l'∥

  local notation `S` := @paths_trel
  @[hott] def paths_quotient (a a' : A) : Type _ := set_quotient (@S a a')
  local notation `mor` := paths_quotient
  local attribute paths_quotient [reducible]

  @[hott] def is_reflexive_R : is_reflexive (@S a a') :=
  begin constructor, intro s, apply tr, constructor end
  local attribute is_reflexive_R [instance]

  @[hott] def paths_compose (g : mor a₂ a₃) (f : mor a₁ a₂) : mor a₁ a₃ :=
  begin
    refine quotient_binary_map _ _ g f, exact append,
    intros, refine trunc_functor2 _ r s, exact rel_respect_append
  end

  @[hott] def paths_id (a : A) : mor a a :=
  class_of nil

  local infix ` ∘∘ `:60 := paths_compose
  local notation `p1` := paths_id _

  @[hott] theorem paths_assoc (h : mor a₃ a₄) (g : mor a₂ a₃) (f : mor a₁ a₂) :
    h ∘∘ (g ∘∘ f) = (h ∘∘ g) ∘∘ f :=
  begin
    induction h using set_quotient.rec_prop with h,
    induction g using set_quotient.rec_prop with g,
    induction f using set_quotient.rec_prop with f,
    rewrite [▸*, append_assoc]
  end

  @[hott] theorem paths_id_left (f : mor a a') : p1 ∘∘ f = f :=
  begin
    induction f using set_quotient.rec_prop with f,
    reflexivity
  end

  @[hott] theorem paths_id_right (f : mor a a') : f ∘∘ p1 = f :=
  begin
    induction f using set_quotient.rec_prop with f,
    rewrite [▸*, append_nil]
  end

  @[hott] def Precategory_paths : Precategory :=
  precategory.MK A
                 mor
                 _
                 paths_compose
                 paths_id
                 paths_assoc
                 paths_id_left
                 paths_id_right

  /- given a way to reverse edges and some additional properties we can extend this to a
    groupoid structure -/
  parameters (inv : Π⦃a a' : A⦄, R a a' → R a' a)
    (rel_inv : Π⦃a a' : A⦄ {l l' : paths R a a'},
      Q l l' → paths_rel Q (reverse inv l) (reverse inv l'))
    (li : Π⦃a a' : A⦄ (r : R a a'), paths_rel Q [inv r, r] nil)
    (ri : Π⦃a a' : A⦄ (r : R a a'), paths_rel Q [r, inv r] nil)

  include rel_inv li ri
  @[hott] def paths_inv (f : mor a a') : mor a' a :=
  begin
    refine quotient_unary_map (reverse inv) _ f,
    intros, refine trunc_functor _ _ r, esimp,
    intro s, apply rel_respect_reverse inv s rel_inv
  end

  local postfix `^`:max := paths_inv

  @[hott] theorem paths_left_inv (f : mor a₁ a₂) : f^ ∘∘ f = p1 :=
  begin
    induction f using set_quotient.rec_prop with f,
    esimp, apply eq_of_rel, apply tr,
    apply rel_left_inv, apply li
  end

  @[hott] theorem paths_right_inv (f : mor a₁ a₂) : f ∘∘ f^ = p1 :=
  begin
    induction f using set_quotient.rec_prop with f,
    esimp, apply eq_of_rel, apply tr,
    apply rel_right_inv, apply ri
  end

  @[hott] def Groupoid_paths : Groupoid :=
  groupoid.MK Precategory_paths
    (λa b f, is_iso.mk (paths_inv f) (paths_left_inv f) (paths_right_inv f))

  end

end paths
open paths

namespace category

  /- We also define the pushout of two groupoids with a type of basepoints, which are surjectively
     mapped into C (although we don't need to assume that this mapping is surjective for the
     definition) -/

  section
  inductive bpushout_prehom_index {S : Type _} {C D E : Precategory} (k : S → C) (F : C ⇒ D)
    (G : C ⇒ E) : D + E → D + E → Type _ :=
  | iD : Π{d d' : D} (f : d ⟶ d'), bpushout_prehom_index k F G (inl d) (inl d')
  | iE : Π{e e' : E} (g : e ⟶ e'), bpushout_prehom_index k F G (inr e) (inr e')
  | DE : Π(s : S), bpushout_prehom_index k F G (inl (F (k s))) (inr (G (k s)))
  | ED : Π(s : S), bpushout_prehom_index k F G (inr (G (k s))) (inl (F (k s)))

  open bpushout_prehom_index

  @[hott] def bpushout_prehom {S : Type _} {C D E : Precategory} (k : S → C) (F : C ⇒ D) (G : C ⇒ E) :
    D + E → D + E → Type _ :=
  paths (bpushout_prehom_index k F G)

  inductive bpushout_hom_rel_index {S : Type _} {C D E : Precategory} (k : S → C) (F : C ⇒ D)
    (G : C ⇒ E) : Π⦃x x' : D + E⦄,
    bpushout_prehom k F G x x' → bpushout_prehom k F G x x' → Type _ :=
  | DD  : Π{d₁ d₂ d₃ : D} (g : d₂ ⟶ d₃) (f : d₁ ⟶ d₂),
      bpushout_hom_rel_index k F G [iD k F G g, iD k F G f] [iD k F G (g ∘ f)]
  | EE  : Π{e₁ e₂ e₃ : E} (g : e₂ ⟶ e₃) (f : e₁ ⟶ e₂),
      bpushout_hom_rel_index k F G [iE k F G g, iE k F G f] [iE k F G (g ∘ f)]
  | DED : Π(s : S), bpushout_hom_rel_index k F G [ED k F G s, DE k F G s] nil
  | EDE : Π(s : S), bpushout_hom_rel_index k F G [DE k F G s, ED k F G s] nil
  | idD : Π(d : D), bpushout_hom_rel_index k F G [iD k F G (ID d)] nil
  | idE : Π(e : E), bpushout_hom_rel_index k F G [iE k F G (ID e)] nil
  | cohDE : Π{s₁ s₂ : S} (h : k s₁ ⟶ k s₂),
        bpushout_hom_rel_index k F G [iE k F G (G h), DE k F G s₁] [DE k F G s₂, iD k F G (F h)]
  | cohED : Π{s₁ s₂ : S} (h : k s₁ ⟶ k s₂),
        bpushout_hom_rel_index k F G [ED k F G s₂, iE k F G (G h)] [iD k F G (F h), ED k F G s₁]

  open bpushout_hom_rel_index paths.paths_rel

  @[hott] def Precategory_bpushout {S : Type _} {C D E : Precategory}
    (k : S → C) (F : C ⇒ D) (G : C ⇒ E) : Precategory :=
  Precategory_paths (bpushout_hom_rel_index k F G)

  parameters {C D E X : Precategory} (F : C ⇒ D) (G : C ⇒ E) (H : D ⇒ X) (K : E ⇒ X)
    (η : H ∘f F ≅ K ∘f G)

  @[hott] def Cpushout : Precategory :=
  Precategory_bpushout (λc, c) F G

  @[hott] def Cpushout_inl : D ⇒ Cpushout :=
  begin
    fapply functor.mk,
    { exact inl},
    { intros d d' f, exact class_of [iD (λc, c) F G f]},
    { intro d, refine eq_of_rel (tr (paths_rel_of_Q _)), apply idD},
    { intros d₁ d₂ d₃ g f, refine (eq_of_rel (tr (paths_rel_of_Q _)))⁻¹, apply DD}
  end

  @[hott] def Cpushout_inr : E ⇒ Cpushout :=
  begin
    fapply functor.mk,
    { exact inr},
    { intros e e' f, exact class_of [iE (λc, c) F G f]},
    { intro e, refine eq_of_rel (tr (paths_rel_of_Q _)), apply idE},
    { intros e₁ e₂ e₃ g f, refine (eq_of_rel (tr (paths_rel_of_Q _)))⁻¹, apply EE}
  end

  @[hott] def Cpushout_coh : Cpushout_inl ∘f F ≅ Cpushout_inr ∘f G :=
  begin
    fapply natural_iso.MK,
    { intro c, exact class_of [DE (λ c, c) F G c]},
    { intros c c' f, refine eq_of_rel (tr (paths_rel_of_Q !cohDE))},
    { intro c, exact class_of [ED (λ c, c) F G c]},
    { intro c, refine eq_of_rel (tr (paths_rel_of_Q !DED))},
    { intro c, refine eq_of_rel (tr (paths_rel_of_Q !EDE))},
  end

--(class_of [DE (λ c, c) F G s])
  variables ⦃x x' x₁ x₂ x₃ : Cpushout⦄
  include H K
  local notation `R` := bpushout_prehom_index  (λ c, c) F G
  local notation `Q` := bpushout_hom_rel_index (λ c, c) F G

  @[hott] def Cpushout_functor_ob (x : Cpushout) : X :=
  begin
    induction x with d e,
    { exact H d},
    { exact K e}
  end

  include η
  parameters {F G H K}
  @[hott] def Cpushout_functor_reduction_rule (i : R x x') :
    Cpushout_functor_ob x ⟶ Cpushout_functor_ob x' :=
  begin
    induction i,
    { exact H f},
    { exact K g},
    { exact natural_map (to_hom η) s},
    { exact natural_map (to_inv η) s}
  end

  @[hott] def Cpushout_functor_list (l : paths R x x') :
    Cpushout_functor_ob x ⟶ Cpushout_functor_ob x' :=
  realize _
          Cpushout_functor_reduction_rule
          (λa, id)
          (λa b c g f, f ∘ g) l

  @[hott] def Cpushout_functor_list_nil (x : Cpushout) :
    Cpushout_functor_list (@nil _ _ x) = id :=
  idp

  @[hott] def Cpushout_functor_list_cons (r : R x₂ x₃) (l : paths R x₁ x₂) :
    Cpushout_functor_list (r :: l) = Cpushout_functor_reduction_rule r ∘ Cpushout_functor_list l :=
  idp

  @[hott] def Cpushout_functor_list_singleton (r : R x₁ x₂) :
    Cpushout_functor_list [r] = Cpushout_functor_reduction_rule r :=
  realize_singleton (λa b f, id_right f) r

  @[hott] def Cpushout_functor_list_pair (r₂ : R x₂ x₃) (r₁ : R x₁ x₂) :
    Cpushout_functor_list [r₂, r₁] =
      Cpushout_functor_reduction_rule r₂ ∘ Cpushout_functor_reduction_rule r₁ :=
  realize_pair (λa b f, id_right f) r₂ r₁

  @[hott] def Cpushout_functor_list_append (l₂ : paths R x₂ x₃) (l₁ : paths R x₁ x₂) :
    Cpushout_functor_list (l₂ ++ l₁) = Cpushout_functor_list l₂ ∘ Cpushout_functor_list l₁ :=
  realize_append (λa b c d h g f, assoc f g h) (λa b f, id_left f) l₂ l₁

  @[hott] theorem Cpushout_functor_list_rel {l l' : paths R x x'} (q : Q l l') :
    Cpushout_functor_list l = Cpushout_functor_list l' :=
  begin
    induction q,
    { rewrite [Cpushout_functor_list_pair, Cpushout_functor_list_singleton],
      exact (respect_comp H g f)⁻¹},
    { rewrite [Cpushout_functor_list_pair, Cpushout_functor_list_singleton],
      exact (respect_comp K g f)⁻¹},
    { rewrite [Cpushout_functor_list_pair, Cpushout_functor_list_nil],
      exact ap010 natural_map (to_left_inverse η) s},
    { rewrite [Cpushout_functor_list_pair, Cpushout_functor_list_nil],
      exact ap010 natural_map (to_right_inverse η) s},
    { rewrite [Cpushout_functor_list_singleton, Cpushout_functor_list_nil], exact respect_id H d},
    { rewrite [Cpushout_functor_list_singleton, Cpushout_functor_list_nil], exact respect_id K e},
    { rewrite [+Cpushout_functor_list_pair], exact naturality (to_hom η) h},
    { rewrite [+Cpushout_functor_list_pair], exact (naturality (to_inv η) h)⁻¹}
  end

  @[hott] def Cpushout_functor_hom (f : x ⟶ x') :
    Cpushout_functor_ob x ⟶ Cpushout_functor_ob x' :=
  begin
    induction f with l l l' q,
    { exact Cpushout_functor_list l},
    { esimp at *, induction q with q, refine realize_eq _ _ _ q,
      { intros, apply assoc},
      { intros, apply id_left},
      intros a₁ a₂ l₁ l₁ q, exact Cpushout_functor_list_rel q}
  end

  @[hott] def Cpushout_functor : Cpushout ⇒ X :=
  begin
    fapply functor.mk,
    { exact Cpushout_functor_ob},
    { exact Cpushout_functor_hom},
    { intro x, reflexivity},
    { intros x₁ x₂ x₃ g f,
      induction g using set_quotient.rec_prop with l₂,
      induction f using set_quotient.rec_prop with l₁,
      exact Cpushout_functor_list_append l₂ l₁}
  end

  @[hott] def Cpushout_functor_inl : Cpushout_functor ∘f Cpushout_inl ≅ H :=
  begin
    fapply natural_iso.mk,
    { fapply nat_trans.mk,
      { intro d, exact id},
      { intros d d' f, rewrite [▸*, Cpushout_functor_list_singleton], apply comp_id_eq_id_comp}},
    esimp, exact _
  end

  @[hott] def Cpushout_functor_inr : Cpushout_functor ∘f Cpushout_inr ≅ K :=
  begin
    fapply natural_iso.mk,
    { fapply nat_trans.mk,
      { intro d, exact id},
      { intros d d' f, rewrite [▸*, Cpushout_functor_list_singleton], apply comp_id_eq_id_comp}},
    esimp, exact _
  end

  @[hott] def Cpushout_functor_coh (c : C) : natural_map (to_hom Cpushout_functor_inr) (G c) ∘
    Cpushout_functor (natural_map (to_hom Cpushout_coh) c) ∘
    natural_map (to_inv Cpushout_functor_inl) (F c) = natural_map (to_hom η) c :=
  !id_leftright ⬝ !Cpushout_functor_list_singleton

  @[hott] def Cpushout_functor_unique_ob (L : Cpushout ⇒ X) (η₁ : L ∘f Cpushout_inl ≅ H)
    (η₂ : L ∘f Cpushout_inr ≅ K) (x : Cpushout) : L x ⟶ Cpushout_functor x :=
  begin
    induction x with d e,
    { exact natural_map (to_hom η₁) d},
    { exact natural_map (to_hom η₂) e}
  end

  @[hott] def Cpushout_functor_unique_inv_ob (L : Cpushout ⇒ X)
    (η₁ : L ∘f Cpushout_inl ≅ H) (η₂ : L ∘f Cpushout_inr ≅ K) (x : Cpushout) :
    Cpushout_functor x ⟶ L x :=
  begin
    induction x with d e,
    { exact natural_map (to_inv η₁) d},
    { exact natural_map (to_inv η₂) e}
  end

  @[hott] def Cpushout_functor_unique_nat_singleton (L : Cpushout ⇒ X) (η₁ : L ∘f Cpushout_inl ≅ H)
    (η₂ : L ∘f Cpushout_inr ≅ K)
    (p : Πs, natural_map (to_hom η₂) (to_fun_ob G s) ∘
             to_fun_hom L (natural_map (to_hom Cpushout_coh) s) ∘
             natural_map (to_inv η₁) (to_fun_ob F s) = natural_map (to_hom η) s) (r : R x x') :
    Cpushout_functor_reduction_rule r ∘ Cpushout_functor_unique_ob L η₁ η₂ x =
    Cpushout_functor_unique_ob L η₁ η₂ x' ∘ L (class_of [r]) :=
  begin
    induction r,
    { exact naturality (to_hom η₁) f},
    { exact naturality (to_hom η₂) g},
    { refine ap (λx, x ∘ _) (p s)⁻¹ ⬝ _, refine !assoc' ⬝ _, apply ap (λx, _ ∘ x),
      refine !assoc' ⬝ _ ⬝ !id_right, apply ap (λx, _ ∘ x),
      exact ap010 natural_map (to_left_inverse η₁) (F s)},
    { apply comp.cancel_left (to_hom (componentwise_iso η s)),
      refine !assoc ⬝ _ ⬝ ap (λx, x ∘ _) (p s),
      refine ap (λx, x ∘ _) (ap010 natural_map (to_right_inverse η) s) ⬝ _ ⬝ !assoc,
      refine !id_left ⬝ !id_right⁻¹ ⬝ _, apply ap (λx, _ ∘ x),
      refine _ ⬝ ap (λx, _ ∘ x) (ap (λx, x ∘ _) _⁻¹ ⬝ !assoc') ⬝ !assoc,
      rotate 2, exact ap010 natural_map (to_left_inverse η₁) (F s),
      refine _⁻¹ ⬝ ap (λx, _ ∘ x) !id_left⁻¹, refine (respect_comp L _ _)⁻¹ ⬝ _ ⬝ respect_id L _,
      apply ap (to_fun_hom L), refine eq_of_rel (tr (paths_rel_of_Q _)), apply EDE},
  end

  @[hott] def Cpushout_functor_unique (L : Cpushout ⇒ X) (η₁ : L ∘f Cpushout_inl ≅ H)
    (η₂ : L ∘f Cpushout_inr ≅ K)
    (p : Πs, natural_map (to_hom η₂) (to_fun_ob G s) ∘
             to_fun_hom L (natural_map (to_hom Cpushout_coh) s) ∘
             natural_map (to_inv η₁) (to_fun_ob F s) = natural_map (to_hom η) s) :
    L ≅ Cpushout_functor :=
  begin
    fapply natural_iso.MK,
    { exact Cpushout_functor_unique_ob L η₁ η₂},
    { intros x x' f, induction f using set_quotient.rec_prop with l,
      esimp, induction l with x x₁ x₂ x₃ r l IH,
      { refine !id_left ⬝ !id_right⁻¹ ⬝ _⁻¹, apply ap (λx, _ ∘ x), apply respect_id},
      { rewrite [Cpushout_functor_list_cons, assoc', ▸*, IH, assoc, ▸*,
                 Cpushout_functor_unique_nat_singleton L η₁ η₂ p r, ▸*, assoc', -respect_comp L]}},
    { exact Cpushout_functor_unique_inv_ob L η₁ η₂},
    { intro x, induction x with d e,
      { exact ap010 natural_map (to_left_inverse η₁) d},
      { exact ap010 natural_map (to_left_inverse η₂) e}},
    { intro x, induction x with d e,
      { exact ap010 natural_map (to_right_inverse η₁) d},
      { exact ap010 natural_map (to_right_inverse η₂) e}},
  end

  end

  open bpushout_prehom_index prod prod.ops is_equiv equiv
  @[hott] def Cpushout_universal {C D E : Precategory} {X : Category} (F : C ⇒ D) (G : C ⇒ E)
    (H : D ⇒ X) (K : E ⇒ X) (η : H ∘f F ≅ K ∘f G) :
    is_contr (Σ(L : Cpushout F G ⇒ X) (θ : L ∘f Cpushout_inl F G ≅ H × L ∘f Cpushout_inr F G ≅ K),
      Πs, natural_map (to_hom θ.2) (to_fun_ob G s) ∘ to_fun_hom L (class_of [DE (λ c, c) F G s]) ∘
          natural_map (to_inv θ.1) (to_fun_ob F s) = natural_map (to_hom η) s) :=
  begin
    fapply is_contr.mk,
    { exact ⟨Cpushout_functor η, (Cpushout_functor_inl η, Cpushout_functor_inr η),
             Cpushout_functor_coh η⟩},
    intro v₁, induction v₁ with L v₂, induction v₂ with θ p, induction θ with θ₁ θ₂,
    fapply sigma_eq,
    { esimp, apply eq_of_iso, symmetry, exact Cpushout_functor_unique η L θ₁ θ₂ p},
    fapply sigma_pathover,
    { apply prod_pathover: esimp,
      { apply iso_pathover,
        apply hom_pathover_functor_left_constant_right (precomposition_functor _ _),
        apply nat_trans_eq, intro d,
        xrewrite [↑[hom_of_eq], to_right_inv !eq_equiv_iso, ▸*],
        exact (ap010 natural_map (to_right_inverse θ₁) d)⁻¹},
      { apply iso_pathover,
        apply hom_pathover_functor_left_constant_right (precomposition_functor _ _),
        apply nat_trans_eq, intro e,
        xrewrite [↑[hom_of_eq], to_right_inv !eq_equiv_iso, ▸*],
        exact (ap010 natural_map (to_right_inverse θ₂) e)⁻¹}},
    apply is_prop.elimo
  end

  local attribute prod.eq_pr1 prod.eq_pr2 [reducible]
  @[hott] def Cpushout_equiv {C D E : Precategory} {X : Category} (F : C ⇒ D) (G : C ⇒ E) :
    (Cpushout F G ⇒ X) ≃ Σ(H : (D ⇒ X) × (E ⇒ X)), H.1 ∘f F ≅ H.2 ∘f G :=
  begin
    fapply equiv.MK,
    { intro K, refine ⟨(K ∘f Cpushout_inl F G, K ∘f Cpushout_inr F G), _⟩,
      exact !assoc_iso⁻¹ⁱ ⬝i (K ∘fi Cpushout_coh F G) ⬝i !assoc_iso},
    { intro v, cases v with w η, cases w with K L, exact Cpushout_functor η},
    { exact abstract begin intro v, cases v with w η, cases w with K L, esimp at *,
      fapply sigma_eq,
      { fapply prod_eq: esimp; apply eq_of_iso,
        { exact Cpushout_functor_inl η},
        { exact Cpushout_functor_inr η}},
        esimp, apply iso_pathover, apply hom_pathover,
        rewrite [ap_compose' _ pr₁, ap_compose' _ pr₂, prod_eq_pr1, prod_eq_pr2],
        rewrite [-+respect_hom_of_eq (precomposition_functor _ _), +hom_of_eq_eq_of_iso],
        apply nat_trans_eq, intro c, esimp [category.to_precategory],
        rewrite [+id_left, +id_right, Cpushout_functor_list_singleton] end end},
    { exact abstract begin intro K, esimp,
      refine eq_base_of_is_prop_sigma _ !is_trunc_succ _ _, rotate 1,
      { refine Cpushout_universal F G (K ∘f Cpushout_inl F G) (K ∘f Cpushout_inr F G) _,
        exact !assoc_iso⁻¹ⁱ ⬝i (K ∘fi Cpushout_coh F G) ⬝i !assoc_iso},
      { esimp, fconstructor, esimp, split,
        { fapply natural_iso.mk',
          { intro c, reflexivity},
          { intros c c' f, rewrite [▸*, id_right, Cpushout_functor_list_singleton, id_left]}},
        { fapply natural_iso.mk',
          { intro c, reflexivity},
          { intros c c' f, rewrite [▸*, id_right, Cpushout_functor_list_singleton, id_left]}},
        intro c, rewrite [▸*, id_left, id_right, Cpushout_functor_list_singleton]},
      { esimp, fconstructor,
        { split: reflexivity},
        intro c, reflexivity} end end}
  end

  /- Pushout of groupoids with a type of basepoints -/
  section
  variables {S : Type _} {C D E : Groupoid} (k : S → C) (F : C ⇒ D) (G : C ⇒ E)
  variables ⦃x x' x₁ x₂ x₃ x₄ : Precategory_bpushout k F G⦄
  open bpushout_prehom_index paths.paths_rel bpushout_hom_rel_index
  @[hott] def bpushout_index_inv (i : bpushout_prehom_index k F G x x') :
    bpushout_prehom_index k F G x' x :=
  begin
    induction i,
    { exact iD k F G f⁻¹},
    { exact iE k F G g⁻¹},
    { exact ED k F G s},
    { exact DE k F G s},
  end

  @[hott] theorem bpushout_index_reverse {l l' : bpushout_prehom k F G x x'}
    (q : bpushout_hom_rel_index k F G l l') : paths_rel (bpushout_hom_rel_index k F G)
      (reverse (bpushout_index_inv k F G) l) (reverse (bpushout_index_inv k F G) l') :=
  begin
    induction q: apply paths_rel_of_Q;
    try rewrite reverse_singleton; rewrite *reverse_pair; try rewrite reverse_nil; esimp;
    try rewrite [comp_inverse]; try rewrite [id_inverse]; rewrite [-*respect_inv]; constructor
  end

  @[hott] theorem bpushout_index_li (i : bpushout_prehom_index k F G x x') :
    paths_rel (bpushout_hom_rel_index k F G) [bpushout_index_inv k F G i, i] nil :=
  begin
    induction i: esimp,
    { refine rtrans (paths_rel_of_Q !DD) _,
      rewrite [comp.left_inverse], exact paths_rel_of_Q !idD},
    { refine rtrans (paths_rel_of_Q !EE) _,
      rewrite [comp.left_inverse], exact paths_rel_of_Q !idE},
    { exact paths_rel_of_Q !DED},
    { exact paths_rel_of_Q !EDE}
  end

  @[hott] theorem bpushout_index_ri (i : bpushout_prehom_index k F G x x') :
    paths_rel (bpushout_hom_rel_index k F G) [i, bpushout_index_inv k F G i] nil :=
  begin
    induction i: esimp,
    { refine rtrans (paths_rel_of_Q !DD) _,
      rewrite [comp.right_inverse], exact paths_rel_of_Q !idD},
    { refine rtrans (paths_rel_of_Q !EE) _,
      rewrite [comp.right_inverse], exact paths_rel_of_Q !idE},
    { exact paths_rel_of_Q !EDE},
    { exact paths_rel_of_Q !DED}
  end

  @[hott] def Groupoid_bpushout : Groupoid :=
  Groupoid_paths (bpushout_hom_rel_index k F G) (bpushout_index_inv k F G)
    (bpushout_index_reverse k F G) (bpushout_index_li k F G) (bpushout_index_ri k F G)

  @[hott] def Gpushout : Groupoid :=
  Groupoid_bpushout (λc, c) F G

  end

end category
