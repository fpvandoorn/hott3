/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Declaration of the torus
-/

import hit.two_quotient

open two_quotient eq bool unit equiv

namespace torus

  open e_closure relation
  @[hott] def torus_R (x y : unit) := bool
  local infix `⬝r`:75 := @e_closure.trans unit torus_R star star star
  local postfix `⁻¹ʳ`:(max+10) := @e_closure.symm unit torus_R star star
  local notation `[`:max a `]`:0 := @e_closure.of_rel unit torus_R star star a

  inductive torus_Q : Π⦃x y : unit⦄, e_closure torus_R x y → e_closure torus_R x y → Type _ :=
  | Qmk : torus_Q ([ff] ⬝r [tt]) ([tt] ⬝r [ff])

  open torus_Q

  @[hott] def torus := two_quotient torus_R torus_Q
  notation `T²` := torus
  @[hott] def base  : torus := incl0 _ _ star
  @[hott] def loop1 : base = base := incl1 _ _ ff
  @[hott] def loop2 : base = base := incl1 _ _ tt
  @[hott] def surf' : loop1 ⬝ loop2 = loop2 ⬝ loop1 :=
  incl2 _ _ Qmk
  @[hott] def surf  : square loop1 loop1 loop2 loop2 :=
  square_of_eq (incl2 _ _ Qmk)

  @[hott] protected def rec {P : torus → Type _} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Ps : squareover P surf Pl1 Pl1 Pl2 Pl2) (x : torus) : P x :=
  begin
    induction x,
    { induction a, exact Pb},
    { induction s: induction a; induction a',
      { exact Pl1},
      { exact Pl2}},
    { induction q, esimp, apply change_path_of_pathover, apply pathover_of_squareover, exact Ps},
  end

  @[hott] protected def rec_on [reducible] {P : torus → Type _} (x : torus) (Pb : P base)
    (Pl1 : Pb =[loop1] Pb) (Pl2 : Pb =[loop2] Pb) (Ps : squareover P surf Pl1 Pl1 Pl2 Pl2) : P x :=
  torus.rec Pb Pl1 Pl2 Ps x

  @[hott] theorem rec_loop1 {P : torus → Type _} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Ps : squareover P surf Pl1 Pl1 Pl2 Pl2)
    : apd (torus.rec Pb Pl1 Pl2 Ps) loop1 = Pl1 :=
  !rec_incl1

  @[hott] theorem rec_loop2 {P : torus → Type _} (Pb : P base) (Pl1 : Pb =[loop1] Pb)
    (Pl2 : Pb =[loop2] Pb) (Ps : squareover P surf Pl1 Pl1 Pl2 Pl2)
    : apd (torus.rec Pb Pl1 Pl2 Ps) loop2 = Pl2 :=
  !rec_incl1

  @[hott] protected def elim {P : Type _} (Pb : P) (Pl1 : Pb = Pb) (Pl2 : Pb = Pb)
    (Ps : square Pl1 Pl1 Pl2 Pl2) (x : torus) : P :=
  begin
    induction x,
    { exact Pb},
    { induction s,
      { exact Pl1},
      { exact Pl2}},
    { induction q, apply eq_of_square, exact Ps},
  end

  @[hott] protected def elim_on [reducible] {P : Type _} (x : torus) (Pb : P)
    (Pl1 : Pb = Pb) (Pl2 : Pb = Pb) (Ps : square Pl1 Pl1 Pl2 Pl2) : P :=
  torus.elim Pb Pl1 Pl2 Ps x

  @[hott] def elim_loop1 {P : Type _} {Pb : P} {Pl1 : Pb = Pb} {Pl2 : Pb = Pb}
    (Ps : square Pl1 Pl1 Pl2 Pl2) : ap (torus.elim Pb Pl1 Pl2 Ps) loop1 = Pl1 :=
  !elim_incl1

  @[hott] def elim_loop2 {P : Type _} {Pb : P} {Pl1 : Pb = Pb} {Pl2 : Pb = Pb}
    (Ps : square Pl1 Pl1 Pl2 Pl2) : ap (torus.elim Pb Pl1 Pl2 Ps) loop2 = Pl2 :=
  !elim_incl1

  @[hott] theorem elim_surf {P : Type _} {Pb : P} {Pl1 : Pb = Pb} {Pl2 : Pb = Pb}
    (Ps : square Pl1 Pl1 Pl2 Pl2)
    : whisker_square (elim_loop1 Ps) (elim_loop1 Ps) (elim_loop2 Ps) (elim_loop2 Ps)
                     (aps (torus.elim Pb Pl1 Pl2 Ps) surf) = Ps :=
  begin
    apply whisker_square_aps_eq,
    apply elim_incl2
  end

end torus

attribute torus.base
attribute torus.rec torus.elim [recursor 6]
--attribute torus.elim_type
attribute torus.rec_on torus.elim_on
--attribute torus.elim_type_on
