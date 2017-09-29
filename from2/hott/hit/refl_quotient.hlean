/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Quotient of a reflexive relation
-/

import homotopy.circle cubical.squareover .two_quotient

open eq simple_two_quotient e_closure

namespace refl_quotient
section

  parameters {A : Type _} (R : A → A → Type _) (ρ : Πa, R a a)
  inductive refl_quotient_Q : Π⦃a : A⦄, e_closure R a a → Type _ :=
  | Qmk {} : Π(a : A), refl_quotient_Q [ρ a]
  open refl_quotient_Q
  local abbreviation Q := refl_quotient_Q

  @[hott] def refl_quotient : Type _ := simple_two_quotient R Q

  @[hott] def rclass_of (a : A) : refl_quotient := incl0 R Q a
  @[hott] def req_of_rel ⦃a a' : A⦄ (r : R a a') : rclass_of a = rclass_of a' :=
  incl1 R Q r

  @[hott] def pρ (a : A) : req_of_rel (ρ a) = idp :=
  incl2 R Q (Qmk a)

  @[hott] protected def rec {P : refl_quotient → Type _} (Pc : Π(a : A), P (rclass_of a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
    (Pr : Π(a : A), change_path (pρ a) (Pp (ρ a)) = idpo) (x : refl_quotient) : P x :=
  begin
    induction x,
      exact Pc a,
      exact Pp s,
      induction q, apply Pr
  end

  @[hott] protected def rec_on [reducible] {P : refl_quotient → Type _} (x : refl_quotient)
    (Pc : Π(a : A), P (rclass_of a)) (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
    (Pr : Π(a : A), change_path (pρ a) (Pp (ρ a)) = idpo) : P x :=
  rec Pc Pp Pr x

  @[hott] def rec_req_of_rel {P : Type _} {P : refl_quotient → Type _} (Pc : Π(a : A), P (rclass_of a))
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a =[req_of_rel H] Pc a')
    (Pr : Π(a : A), change_path (pρ a) (Pp (ρ a)) = idpo) ⦃a a' : A⦄ (r : R a a')
    : apd (rec Pc Pp Pr) (req_of_rel r) = Pp r :=
  !rec_incl1

  @[hott] protected def elim {P : Type _} (Pc : Π(a : A), P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (Pr : Π(a : A), Pp (ρ a) = idp)
    (x : refl_quotient) : P :=
  begin
    induction x,
      exact Pc a,
      exact Pp s,
      induction q, apply Pr
  end

  @[hott] protected def elim_on [reducible] {P : Type _} (x : refl_quotient) (Pc : Π(a : A), P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (Pr : Π(a : A), Pp (ρ a) = idp) : P :=
  elim Pc Pp Pr x

  @[hott] def elim_req_of_rel {P : Type _} {Pc : Π(a : A), P}
    {Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a'} (Pr : Π(a : A), Pp (ρ a) = idp)
    ⦃a a' : A⦄ (r : R a a') : ap (elim Pc Pp Pr) (req_of_rel r) = Pp r :=
  !elim_incl1

  @[hott] theorem elim_pρ {P : Type _} (Pc : Π(a : A), P)
    (Pp : Π⦃a a' : A⦄ (H : R a a'), Pc a = Pc a') (Pr : Π(a : A), Pp (ρ a) = idp) (a : A)
     : square (ap02 (elim Pc Pp Pr) (pρ a)) (Pr a) (elim_req_of_rel Pr (ρ a)) idp :=
  !elim_incl2

end
end refl_quotient

attribute refl_quotient.rclass_of
attribute refl_quotient.rec refl_quotient.elim [recursor 8]
--attribute refl_quotient.elim_type
attribute refl_quotient.rec_on refl_quotient.elim_on
--attribute refl_quotient.elim_type_on
