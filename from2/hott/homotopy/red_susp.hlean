/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

Declaration of the reduced suspension
red_susp X
-/

import hit.two_quotient types.pointed algebra.e_closure

open simple_two_quotient eq unit pointed e_closure susp function

namespace red_susp
section

  parameter {A : Type*}

  inductive red_susp_R : unit → unit → Type _ :=
  | Rmk : Π(a : A), red_susp_R star star
  open red_susp_R
  inductive red_susp_Q : Π⦃x : unit⦄, e_closure red_susp_R x x → Type _ :=
  | Qmk : red_susp_Q [Rmk pt]
  open red_susp_Q
  local abbreviation R := red_susp_R
  local abbreviation Q := red_susp_Q

  parameter (A)
  @[hott] def red_susp' : Type _ := simple_two_quotient R Q
  parameter {A}
  @[hott] def base' : red_susp' :=
  incl0 R Q star
  parameter (A)
  @[hott] def red_susp : Type* := pointed.MK red_susp' base'
  parameter {A}

  @[hott] def base [reducible] : red_susp :=
  base'

  @[hott] def equator (a : A) : base = base :=
  incl1 R Q (Rmk a)

  @[hott] def equator_pt : equator pt = idp :=
  incl2 R Q Qmk

  @[hott] protected def rec {P : red_susp → Type _} (Pb : P base) (Pm : Π(a : A), Pb =[equator a] Pb)
    (Pe : change_path equator_pt (Pm pt) = idpo) (x : red_susp') : P x :=
  begin
    induction x,
    { induction a, exact Pb},
    { induction s, exact Pm a},
    { induction q, esimp, exact Pe}
  end

  @[hott] protected def rec_on [reducible] {P : red_susp → Type _} (x : red_susp') (Pb : P base)
    (Pm : Π(a : A), Pb =[equator a] Pb) (Pe : change_path equator_pt (Pm pt) = idpo) : P x :=
  red_susp.rec Pb Pm Pe x

  @[hott] def rec_equator {P : red_susp → Type _} (Pb : P base) (Pm : Π(a : A), Pb =[equator a] Pb)
    (Pe : change_path equator_pt (Pm pt) = idpo) (a : A)
    : apd (rec Pb Pm Pe) (equator a) = Pm a :=
  !rec_incl1

  @[hott] protected def elim {P : Type _} (Pb : P) (Pm : Π(a : A), Pb = Pb)
    (Pe : Pm pt = idp) (x : red_susp') : P :=
  begin
    induction x,
      exact Pb,
      induction s, exact Pm a,
      induction q, exact Pe
  end

 @[hott] protected def elim_on [reducible] {P : Type _} (x : red_susp') (Pb : P)
    (Pm : Π(a : A), Pb = Pb) (Pe : Pm pt = idp) : P :=
  elim Pb Pm Pe x

  @[hott] def elim_equator {P : Type _} {Pb : P} {Pm : Π(a : A), Pb = Pb}
    (Pe : Pm pt = idp) (a : A)
    : ap (elim Pb Pm Pe) (equator a) = Pm a :=
  !elim_incl1

  @[hott] theorem elim_equator_pt {P : Type _} (Pb : P) (Pm : Π(a : A), Pb = Pb)
    (Pe : Pm pt = idp) : square (ap02 (elim Pb Pm Pe) equator_pt) Pe (elim_equator Pe pt) idp :=
  !elim_incl2

end
end red_susp

attribute red_susp.base red_susp.base'
attribute red_susp.rec red_susp.elim [recursor 6]
--attribute red_susp.elim_type
attribute red_susp.rec_on red_susp.elim_on
--attribute red_susp.elim_type_on

namespace red_susp

  @[hott] protected def pelim' {A P : Type*} (f : A →* Ω P) : red_susp' A → P :=
  red_susp.elim pt f (respect_pt f)

  @[hott] protected def pelim {A P : Type*} (f : A →* Ω P) : red_susp A →* P :=
  pmap.mk (red_susp.pelim' f) idp

  @[hott] def susp_of_red_susp {A : Type*} (x : red_susp A) : susp A :=
  begin
    induction x,
    { exact !north },
    { exact merid a ⬝ (merid pt)⁻¹ },
    { apply con.right_inv }
  end

  @[hott] def red_susp_of_susp {A : Type*} (x : susp A) : red_susp A :=
  begin
    induction x,
    { exact pt },
    { exact pt },
    { exact equator a }
  end

  @[hott] def red_susp_helper_@[hott] lemma {A : Type _} {a : A} {p₁ p₂ : a = a} (q : p₁ = p₂) (q' : p₂ = idp)
    : square (q ◾ (q ⬝ q')⁻²) idp (con.right_inv p₁) q' :=
  begin induction q, cases q', exact hrfl end

  @[hott] def red_susp_equiv_susp (A : Type*) : red_susp A ≃ susp A :=
  begin
    fapply equiv.MK,
    { exact susp_of_red_susp },
    { exact red_susp_of_susp },
    { exact abstract begin intro x, induction x,
      { reflexivity },
      { exact merid pt },
      { apply eq_pathover_id_right,
        refine ap_compose susp_of_red_susp _ _ ⬝ ap02 _ !elim_merid ⬝ !elim_equator ⬝ph _,
        apply whisker_bl, exact hrfl } end end },
    { exact abstract begin intro x, induction x,
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        refine ap_compose red_susp_of_susp _ _ ⬝ (ap02 _ !elim_equator ⬝ _) ⬝ !ap_id⁻¹,
        exact !ap_con ⬝ whisker_left _ !ap_inv ⬝ !elim_merid ◾ (!elim_merid ⬝ equator_pt)⁻² },
      { refine !change_path_eq_pathover ⬝ ap eq_pathover !eq_hconcat_eq_hdeg_square ⬝ _,
        refine @(ap (eq_pathover ∘ hdeg_square)) _ idp _, symmetry, apply eq_bot_of_square,
        refine _ ⬝h !ap02_id⁻¹ʰ, refine !ap02_compose ⬝h _,
        apply move_top_of_left', refine whisker_right _ !ap_inv⁻¹ ⬝ !ap_con⁻¹ ⬝ph _,
        refine ap02 _ (eq_bot_of_square !elim_equator_pt)⁻¹ ⬝ph _,
        refine transpose !ap_con_right_inv_sq ⬝h _, apply red_susp_helper_@[hott] lemma } end end }
  end

  /- a second proof that the reduced suspension is the suspension, by first proving
     a new induction principle for the reduced suspension -/

  @[hott] protected def susp_rec {A : Type*} {P : red_susp A → Type _} (P0 : P base)
    (P1 : Πa, P0 =[equator a] P0) (x : red_susp' A) : P x :=
  begin
    induction x,
    { exact P0 },
    { refine change_path _ (P1 a ⬝o (P1 pt)⁻¹ᵒ), exact whisker_left (equator a) equator_pt⁻² },
    { refine !change_path_con⁻¹ ⬝ _, refine ap (λx, change_path x _) _ ⬝ cono_invo_eq_idpo idp,
      exact whisker_left_inverse2 equator_pt }
  end

  @[hott] def red_susp_equiv_susp' (A : Type*) : red_susp A ≃ susp A :=
  begin
    fapply equiv.MK,
    { exact susp_of_red_susp },
    { exact red_susp_of_susp },
    { exact abstract begin intro x, induction x,
      { reflexivity },
      { exact merid pt },
      { apply eq_pathover_id_right,
        refine ap_compose susp_of_red_susp _ _ ⬝ ap02 _ !elim_merid ⬝ !elim_equator ⬝ph _,
        apply whisker_bl, exact hrfl } end end },
    { intro x, induction x using red_susp.susp_rec,
      { reflexivity },
      { apply eq_pathover, apply hdeg_square,
        refine ap_compose red_susp_of_susp _ _ ⬝ (ap02 _ !elim_equator ⬝ _) ⬝ !ap_id⁻¹,
        exact !ap_con ⬝ whisker_left _ !ap_inv ⬝ !elim_merid ◾ (!elim_merid ⬝ equator_pt)⁻² }}
  end


end red_susp
