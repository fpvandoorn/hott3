/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Favonia

The Wedge Sum of a family of Pointed Types
-/
import homotopy.wedge ..move_to_lib ..choice ..pointed_pi

open eq is_equiv pushout pointed unit trunc_index sigma bool equiv choice unit is_trunc sigma.ops lift function pi prod

@[hott] def fwedge' {I : Type _} (F : I → Type*) : Type _ := pushout (λi, ⟨i, Point (F i)⟩) (λi, ⋆)
@[hott] def pt' {I : Type _} {F : I → Type*} : fwedge' F := inr ⋆
@[hott] def fwedge {I : Type _} (F : I → Type*) : Type* := pointed.MK (fwedge' F) pt'

notation `⋁` := fwedge

namespace fwedge
  variables {I : Type _} {F : I → Type*}

  @[hott] def il {i : I} (x : F i) : ⋁F := inl ⟨i, x⟩
  @[hott] def inl (i : I) (x : F i) : ⋁F := il x
  @[hott] def pinl (i : I) : F i →* ⋁F := pmap.mk (inl i) (glue i)
  @[hott] def glue (i : I) : inl i pt = pt :> ⋁ F := glue i

  @[hott] protected def rec {P : ⋁F → Type _} (Pinl : Π(i : I) (x : F i), P (il x))
    (Pinr : P pt) (Pglue : Πi, pathover P (Pinl i pt) (glue i) (Pinr)) (y : fwedge' F) : P y :=
  begin induction y, induction x, apply Pinl, induction x, apply Pinr, apply Pglue end

  @[hott] protected def elim {P : Type _} (Pinl : Π(i : I) (x : F i), P)
    (Pinr : P) (Pglue : Πi, Pinl i pt = Pinr) (y : fwedge' F) : P :=
  begin induction y with x u, induction x with i x, exact Pinl i x, induction u, apply Pinr, apply Pglue end

  @[hott] protected def elim_glue {P : Type _} {Pinl : Π(i : I) (x : F i), P}
    {Pinr : P} (Pglue : Πi, Pinl i pt = Pinr) (i : I)
    : ap (fwedge.elim Pinl Pinr Pglue) (fwedge.glue i) = Pglue i :=
  !pushout.elim_glue

  @[hott] protected def rec_glue {P : ⋁F → Type _} {Pinl : Π(i : I) (x : F i), P (il x)}
    {Pinr : P pt} (Pglue : Πi, pathover P (Pinl i pt) (glue i) (Pinr)) (i : I)
    : apd (fwedge.rec Pinl Pinr Pglue) (fwedge.glue i) = Pglue i :=
  !pushout.rec_glue

end fwedge

attribute fwedge.rec fwedge.elim [recursor 7]
attribute fwedge.il fwedge.inl

namespace fwedge

  @[hott] def fwedge_of_wedge {A B : Type*} (x : A ∨ B) : ⋁(bool.rec A B) :=
  begin
    induction x with a b,
    { exact inl ff a },
    { exact inl tt b },
    { exact glue ff ⬝ (glue tt)⁻¹ }
  end

  @[hott] def wedge_of_fwedge {A B : Type*} (x : ⋁(bool.rec A B)) : A ∨ B :=
  begin
    induction x with b x b,
    { induction b, exact pushout.inl x, exact pushout.inr x },
    { exact pushout.inr pt },
    { induction b, exact pushout.glue ⋆, reflexivity }
  end

  @[hott] def wedge_pequiv_fwedge (A B : Type*) : A ∨ B ≃* ⋁(bool.rec A B) :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact fwedge_of_wedge },
      { exact wedge_of_fwedge },
      { exact abstract begin intro x, induction x with b x b,
        { induction b: reflexivity },
        { exact glue tt },
        { apply eq_pathover_id_right,
          refine ap_compose fwedge_of_wedge _ _ ⬝ ap02 _ !elim_glue ⬝ph _,
          induction b, exact !elim_glue ⬝ph whisker_bl _ hrfl, apply square_of_eq idp }
        end end },
      { exact abstract begin intro x, induction x with a b,
        { reflexivity },
        { reflexivity },
        { apply eq_pathover_id_right,
          refine ap_compose wedge_of_fwedge _ _ ⬝ ap02 _ !elim_glue ⬝ !ap_con ⬝
                 !elim_glue ◾ (!ap_inv ⬝ !elim_glue⁻²) ⬝ph _, exact hrfl } end end}},
    { exact glue ff }
  end

  @[hott] def is_contr_fwedge_of_neg {I : Type _} (P : I → Type*) (H : ¬ I) : is_contr (⋁P) :=
  begin
    apply is_contr.mk pt, intro x, induction x, contradiction, reflexivity, contradiction
  end

  @[hott] def is_contr_fwedge_empty [instance] : is_contr (⋁empty.elim) :=
  is_contr_fwedge_of_neg _ id

  @[hott] def fwedge_pmap {I : Type _} {F : I → Type*} {X : Type*} (f : Πi, F i →* X) : ⋁F →* X :=
  begin
    fapply pmap.mk,
    { intro x, induction x,
        exact f i x,
        exact pt,
        exact respect_pt (f i) },
    { reflexivity }
  end

 @[hott] def wedge_pmap {A B : Type*} {X : Type*} (f : A →* X) (g : B →* X) : (A ∨ B) →* X :=
  begin
    fapply pmap.mk,
    { intro x, induction x, exact (f a), exact (g a), exact (respect_pt (f) ⬝ (respect_pt g)⁻¹) },
    { exact respect_pt f }
  end

  @[hott] def fwedge_pmap_beta {I : Type _} {F : I → Type*} {X : Type*} (f : Πi, F i →* X) (i : I) :
    fwedge_pmap f ∘* pinl i ~* f i :=
  begin
    fapply phomotopy.mk,
    { reflexivity },
    { exact !idp_con ⬝ !fwedge.elim_glue⁻¹ }
  end

  @[hott] def fwedge_pmap_eta {I : Type _} {F : I → Type*} {X : Type*} (g : ⋁F →* X) :
    fwedge_pmap (λi, g ∘* pinl i) ~* g :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x,
        reflexivity,
        exact (respect_pt g)⁻¹,
        apply eq_pathover, refine !elim_glue ⬝ph _, apply whisker_lb, exact hrfl },
    { exact con.left_inv (respect_pt g) }
  end

  @[hott] def fwedge_pmap_pinl {I : Type _} {F : I → Type*} : fwedge_pmap (λi, pinl i) ~* pid (⋁ F) :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x,
        reflexivity, reflexivity,
        apply eq_pathover, apply hdeg_square, refine !elim_glue ⬝ !ap_id⁻¹ },
    { reflexivity }
  end

  @[hott] def fwedge_pmap_equiv {I : Type _} (F : I → Type*) (X : Type*) :
    ⋁F →* X ≃ Πi, F i →* X :=
  begin
    fapply equiv.MK,
    { intros g i, exact g ∘* pinl i },
    { exact fwedge_pmap },
    { intro f, apply eq_of_homotopy, intro i, apply eq_of_phomotopy, apply fwedge_pmap_beta f i },
    { intro g, apply eq_of_phomotopy, exact fwedge_pmap_eta g }
  end

  @[hott] def wedge_pmap_equiv  (A B X : Type*) :
    ((A ∨ B) →* X) ≃ ((A →* X) × (B →* X)) :=
    calc (A ∨ B) →* X ≃ ⋁(bool.rec A B) →* X : by exact pequiv_ppcompose_right (wedge_pequiv_fwedge A B)⁻¹ᵉ*
            ...       ≃ Πi, (bool.rec A B) i →* X : by exact fwedge_pmap_equiv (bool.rec A B) X
            ...       ≃  (A →* X) × (B →* X) : by exact pi_bool_left (λ i, bool.rec A B i →* X)


  @[hott] def fwedge_pmap_nat₂ {I : Type _}(F : I → Type*){X Y : Type*}
                              (f : X →* Y) (h : Πi, F i →* X) (w : fwedge F) :
             (f ∘* (fwedge_pmap h)) w = fwedge_pmap (λi, f ∘* (h i)) w :=
  begin
      induction w, reflexivity,
      refine !respect_pt,
      apply eq_pathover,
      refine ap_compose f (fwedge_pmap h) _ ⬝ph _,
      refine ap (ap f) !elim_glue ⬝ph _,
      refine _ ⬝hp !elim_glue⁻¹, esimp,
      apply whisker_br,
      apply !hrefl
  end

-- making the maps in hsquare 1:

  -- top and bottom:
  @[hott] def prod_pi_bool_comp_funct {A B : Type*}(X : Type*) : (A →* X) × (B →* X) → Π u, (bool.rec A B u →* X) :=
   begin
     refine equiv.symm _,
     fapply pi_bool_left
   end

  -- left:
  @[hott] def prod_funct_comp {A B X Y : Type*} (f : X →* Y) : (A →* X) × (B →* X) → (A →* Y) × (B →* Y) :=
   prod_functor (pcompose f) (pcompose f)

  -- right:
  @[hott] def left_comp_pi_bool_funct {A B X Y : Type*} (f : X →* Y) : (Π u, (bool.rec A B u →* X)) →  (Π u, (bool.rec A B u →* Y)) :=
  begin
    intro, intro, exact f ∘* (a u)
  end

  @[hott] def left_comp_pi_bool {A B X Y : Type*} (f : X →* Y) : Π u, ((bool.rec A B u →* X) →  (bool.rec A B u →* Y)) :=
  begin
    intro, intro, exact f∘* a
  end

-- hsquare 1:
 @[hott] def prod_to_pi_bool_nat_square {A B X Y : Type*} (f : X →* Y) :
   hsquare (prod_pi_bool_comp_funct X) (prod_pi_bool_comp_funct Y) (prod_funct_comp f) (@left_comp_pi_bool_funct A B X Y f) :=
  begin
   intro x, fapply eq_of_homotopy, intro u, induction u, esimp, esimp
  end

-- hsquare 2:
  @[hott] def fwedge_pmap_nat_square {A B X Y : Type*} (f : X →* Y) :
       hsquare (fwedge_pmap_equiv (bool.rec A B) X)⁻¹ᵉ (fwedge_pmap_equiv (bool.rec A B) Y)⁻¹ᵉ (left_comp_pi_bool_funct f) (pcompose f) :=
  begin
   intro h, esimp, fapply eq_of_phomotopy, fapply phomotopy.mk,
   exact fwedge_pmap_nat₂ (λ u, bool.rec A B u) f h,
   reflexivity
  end

-- hsquare 3:
  @[hott] def fwedge_to_wedge_nat_square {A B X Y : Type*} (f : X →* Y) :
        hsquare (pequiv_ppcompose_right (wedge_pequiv_fwedge A B)) (pequiv_ppcompose_right (wedge_pequiv_fwedge A B)) (pcompose f) (pcompose f) :=
  begin
    exact sorry
  end

 @[hott] def wedge_pmap_nat₂ (A B X Y : Type*) (f : X →* Y) (h : A →* X) (k : B →* X) : Π (w : A ∨ B),
    (f ∘* (wedge_pmap h k)) w = wedge_pmap (f ∘* h )(f ∘* k) w  :=
have H : _, from
    (@prod_to_pi_bool_nat_square A B X Y f) ⬝htyh (fwedge_pmap_nat_square f) ⬝htyh (fwedge_to_wedge_nat_square f),
sorry

-- SA to here 7/5

  @[hott] def fwedge_pmap_phomotopy {I : Type _} {F : I → Type*} {X : Type*} {f g : Π i, F i →* X}
    (h : Π i, f i ~* g i) : fwedge_pmap f ~* fwedge_pmap g :=
  begin
    fconstructor,
    { fapply fwedge.rec,
      { exact h },
      { reflexivity },
      { intro i, apply eq_pathover,
        refine _ ⬝ph _ ⬝hp _,
        { exact (respect_pt (g i)) },
        { exact (respect_pt (f i)) },
        { exact !elim_glue },
        { apply square_of_eq,
          exact ((phomotopy.sigma_char (f i) (g i)) (h i)).2
        },
        { refine !elim_glue⁻¹ }
      }
    },
    { reflexivity }
  end




  open trunc
  @[hott] def trunc_fwedge_pmap_equiv.{u} {n : ℕ₋₂} {I : Type u} (H : has_choice n I)
    (F : I → pType.{u}) (X : pType.{u}) : trunc n (⋁F →* X) ≃ Πi, trunc n (F i →* X) :=
  trunc_equiv_trunc n (fwedge_pmap_equiv F X) ⬝e choice_equiv (λi, F i →* X)


  @[hott] def fwedge_functor {I : Type _} {F F' : I → Type*} (f : Π i, F i →* F' i)
    : ⋁ F →* ⋁ F' := fwedge_pmap (λ i, pinl i ∘* f i)

  @[hott] def fwedge_functor_pid {I : Type _} {F : I → Type*}
    : @fwedge_functor I F F (λ i, !pid) ~* !pid :=
  calc fwedge_pmap (λ i, pinl i ∘* !pid) ~* fwedge_pmap pinl : by exact fwedge_pmap_phomotopy (λ i, pcompose_pid (pinl i))
                                     ... ~* fwedge_pmap (λ i, !pid ∘* pinl i) : by exact fwedge_pmap_phomotopy (λ i, phomotopy.symm (pid_pcompose (pinl i)))
                                     ... ~* !pid : by exact fwedge_pmap_eta !pid

  @[hott] def fwedge_functor_pcompose {I : Type _} {F F' F'' : I → Type*} (g : Π i, F' i →* F'' i)
    (f : Π i, F i →* F' i) : fwedge_functor (λ i, g i ∘* f i) ~* fwedge_functor g ∘* fwedge_functor f :=
  calc        fwedge_functor (λ i, g i ∘* f i)
           ~* fwedge_pmap (λ i, (pinl i ∘* g i) ∘* f i)
              : by exact fwedge_pmap_phomotopy (λ i, phomotopy.symm (passoc (pinl i) (g i) (f i)))
       ... ~* fwedge_pmap (λ i, (fwedge_functor g ∘* pinl i) ∘* f i)
              : by exact fwedge_pmap_phomotopy (λ i, pwhisker_right (f i) (phomotopy.symm (fwedge_pmap_beta (λ i, pinl i ∘* g i) i)))
       ... ~* fwedge_pmap (λ i, fwedge_functor g ∘* (pinl i ∘* f i))
              : by exact fwedge_pmap_phomotopy (λ i, passoc (fwedge_functor g) (pinl i) (f i))
       ... ~* fwedge_pmap (λ i, fwedge_functor g ∘* (fwedge_functor f ∘* pinl i))
              : by exact fwedge_pmap_phomotopy (λ i, pwhisker_left (fwedge_functor g) (phomotopy.symm (fwedge_pmap_beta (λ i, pinl i ∘* f i) i)))
       ... ~* fwedge_pmap (λ i, (fwedge_functor g ∘* fwedge_functor f) ∘* pinl i)
              : by exact fwedge_pmap_phomotopy (λ i, (phomotopy.symm (passoc (fwedge_functor g) (fwedge_functor f) (pinl i))))
       ... ~* fwedge_functor g ∘* fwedge_functor f
              : by exact fwedge_pmap_eta (fwedge_functor g ∘* fwedge_functor f)

  @[hott] def fwedge_functor_phomotopy {I : Type _} {F F' : I → Type*} {f g : Π i, F i →* F' i}
    (h : Π i, f i ~* g i) : fwedge_functor f ~* fwedge_functor g :=
    fwedge_pmap_phomotopy (λ i, pwhisker_left (pinl i) (h i))

  @[hott] def fwedge_pequiv {I : Type _} {F F' : I → Type*} (f : Π i, F i ≃* F' i) : ⋁ F ≃* ⋁ F' :=
  let pto := fwedge_functor (λ i, f i) in
  let pfrom := fwedge_functor (λ i, (f i)⁻¹ᵉ*) in
  begin
    fapply pequiv_of_pmap, exact pto,
    fapply adjointify, exact pfrom,
    { intro y, refine (fwedge_functor_pcompose (λ i, f i) (λ i, (f i)⁻¹ᵉ*) y)⁻¹ ⬝ _,
      refine fwedge_functor_phomotopy (λ i, pright_inv (f i)) y ⬝ _,
      exact fwedge_functor_pid y
    },
    { intro y, refine (fwedge_functor_pcompose (λ i, (f i)⁻¹ᵉ*) (λ i, f i) y)⁻¹ ⬝ _,
      refine fwedge_functor_phomotopy (λ i, pleft_inv (f i)) y ⬝ _,
      exact fwedge_functor_pid y
    }
  end

  @[hott] def plift_fwedge.{u v} {I : Type _} (F : I → pType.{u}) : plift.{u v} (⋁ F) ≃* ⋁ (plift.{u v} ∘ F) :=
  calc plift.{u v} (⋁ F) ≃* ⋁ F : by exact !pequiv_plift ⁻¹ᵉ*
                     ... ≃* ⋁ (λ i, plift.{u v} (F i)) : by exact fwedge_pequiv (λ i, !pequiv_plift)

  @[hott] def fwedge_down_left.{u v} {I : Type _} (F : I → pType) : ⋁ (F ∘ down.{u v}) ≃* ⋁ F :=
  proof
  let pto := @fwedge_pmap (lift.{u v} I) (F ∘ down) (⋁ F) (λ i, pinl (down i)) in
  let pfrom := @fwedge_pmap I F (⋁ (F ∘ down.{u v})) (λ i, pinl (up.{u v} i)) in
  begin
    fapply pequiv_of_pmap,
    { exact pto },
    fapply adjointify,
    { exact pfrom },
    { intro x, exact calc pto (pfrom x) = fwedge_pmap (λ i, (pto ∘* pfrom) ∘* pinl i) x : by exact (fwedge_pmap_eta (pto ∘* pfrom) x)⁻¹
                                    ... = fwedge_pmap (λ i, pto ∘* (pfrom ∘* pinl i)) x : by exact fwedge_pmap_phomotopy (λ i, passoc pto pfrom (pinl i)) x
                                    ... = fwedge_pmap (λ i, pto ∘* pinl (up.{u v} i)) x : by exact fwedge_pmap_phomotopy (λ i, pwhisker_left pto (fwedge_pmap_beta (λ i, pinl (up.{u v} i)) i)) x
                                    ... = fwedge_pmap pinl x : by exact fwedge_pmap_phomotopy (λ i, fwedge_pmap_beta (λ i, (pinl (down.{u v} i))) (up.{u v} i)) x
                                    ... = x : by exact fwedge_pmap_pinl x
    },
    { intro x, exact calc pfrom (pto x) = fwedge_pmap (λ i, (pfrom ∘* pto) ∘* pinl i) x : by exact (fwedge_pmap_eta (pfrom ∘* pto) x)⁻¹
                                    ... = fwedge_pmap (λ i, pfrom ∘* (pto ∘* pinl i)) x : by exact fwedge_pmap_phomotopy (λ i, passoc pfrom pto (pinl i)) x
                                    ... = fwedge_pmap (λ i, pfrom ∘* pinl (down.{u v} i)) x : by exact fwedge_pmap_phomotopy (λ i, pwhisker_left pfrom (fwedge_pmap_beta (λ i, pinl (down.{u v} i)) i)) x
                                    ... = fwedge_pmap pinl x : by exact fwedge_pmap_phomotopy (λ i,
                                            begin induction i with i,
                                              exact fwedge_pmap_beta (λ i, (pinl (up.{u v} i))) i
                                            end
                                          ) x
                                    ... = x : by exact fwedge_pmap_pinl x
    }

  end
  qed

end fwedge
