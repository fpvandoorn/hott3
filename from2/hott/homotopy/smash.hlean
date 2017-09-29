/-
Copyright (c) 2016 Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer, Floris van Doorn

The Smash Product of Types.

One @[hott] def is the cofiber of the map
    wedge A B → A × B
However, we define it (equivalently) as the pushout of the maps A + B → 2 and A + B → A × B.
-/

import homotopy.circle homotopy.join types.pointed homotopy.cofiber homotopy.wedge

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge

namespace smash

  variables {A B : Type*}

  section
  open pushout

  @[hott] def prod_of_sum (u : A + B) : A × B :=
  by induction u with a b; exact (a, pt); exact (pt, b)

  @[hott] def bool_of_sum (u : A + B) : bool :=
  by induction u; exact ff; exact tt

  @[hott] def smash' (A B : Type*) : Type _ := pushout (@prod_of_sum A B) (@bool_of_sum A B)
  @[hott] protected def mk' (a : A) (b : B) : smash' A B := inl (a, b)

  @[hott] def pointed_smash' [instance] (A B : Type*) : pointed (smash' A B) :=
  pointed.mk (smash.mk' pt pt)
  @[hott] def smash (A B : Type*) : Type* :=
  pointed.mk' (smash' A B)

  infixr ` ∧ ` := smash

  @[hott] protected def mk (a : A) (b : B) : A ∧ B := inl (a, b)
  @[hott] def auxl : smash A B := inr ff
  @[hott] def auxr : smash A B := inr tt
  @[hott] def gluel (a : A) : smash.mk a pt = auxl :> smash A B := glue (inl a)
  @[hott] def gluer (b : B) : smash.mk pt b = auxr :> smash A B := glue (inr b)

  end

  @[hott] def gluel' (a a' : A) : smash.mk a pt = smash.mk a' pt :> smash A B :=
  gluel a ⬝ (gluel a')⁻¹
  @[hott] def gluer' (b b' : B) : smash.mk pt b = smash.mk pt b' :> smash A B :=
  gluer b ⬝ (gluer b')⁻¹
  @[hott] def glue (a : A) (b : B) : smash.mk a pt = smash.mk pt b :=
  gluel' a pt ⬝ gluer' pt b

  @[hott] def glue_pt_left (b : B) : glue (Point A) b = gluer' pt b :=
  whisker_right _ !con.right_inv ⬝ !idp_con

  @[hott] def glue_pt_right (a : A) : glue a (Point B) = gluel' a pt :=
  proof whisker_left _ !con.right_inv qed

  @[hott] def ap_mk_left {a a' : A} (p : a = a') : ap (λa, smash.mk a (Point B)) p = gluel' a a' :=
  !ap_is_constant

  @[hott] def ap_mk_right {b b' : B} (p : b = b') : ap (smash.mk (Point A)) p = gluer' b b' :=
  !ap_is_constant

  @[hott] protected def rec {P : smash A B → Type _} (Pmk : Πa b, P (smash.mk a b))
    (Pl : P auxl) (Pr : P auxr) (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (x : smash' A B) : P x :=
  begin
    induction x with x b u,
    { induction x with a b, exact Pmk a b },
    { induction b, exact Pl, exact Pr },
    { induction u: esimp,
      { apply Pgl },
      { apply Pgr }}
  end

  @[hott] theorem rec_gluel {P : smash A B → Type _} {Pmk : Πa b, P (smash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (a : A) :
    apd (smash.rec Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a :=
  !pushout.rec_glue

  @[hott] theorem rec_gluer {P : smash A B → Type _} {Pmk : Πa b, P (smash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (b : B) :
    apd (smash.rec Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b :=
  !pushout.rec_glue

  @[hott] theorem rec_glue {P : smash A B → Type _} {Pmk : Πa b, P (smash.mk a b)}
    {Pl : P auxl} {Pr : P auxr} (Pgl : Πa, Pmk a pt =[gluel a] Pl)
    (Pgr : Πb, Pmk pt b =[gluer b] Pr) (a : A) (b : B) :
    apd (smash.rec Pmk Pl Pr Pgl Pgr) (glue a b) =
      (Pgl a ⬝o (Pgl pt)⁻¹ᵒ) ⬝o (Pgr pt ⬝o (Pgr b)⁻¹ᵒ) :=
  by rewrite [↑glue, ↑gluel', ↑gluer', +apd_con, +apd_inv, +rec_gluel, +rec_gluer]

  @[hott] protected def elim {P : Type _} (Pmk : Πa b, P) (Pl Pr : P)
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (x : smash' A B) : P :=
  smash.rec Pmk Pl Pr (λa, pathover_of_eq _ (Pgl a)) (λb, pathover_of_eq _ (Pgr b)) x

  -- an elim where you are forced to make (Pgl pt) and (Pgl pt) to be reflexivity
  @[hott] protected def elim' [reducible] {P : Type _} (Pmk : Πa b, P)
    (Pgl : Πa : A, Pmk a pt = Pmk pt pt) (Pgr : Πb : B, Pmk pt b = Pmk pt pt)
    (ql : Pgl pt = idp) (qr : Pgr pt = idp) (x : smash' A B) : P :=
  smash.elim Pmk (Pmk pt pt) (Pmk pt pt) Pgl Pgr x

  @[hott] theorem elim_gluel {P : Type _} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (a : A) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluel a) = Pgl a :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (@gluel A B a)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑smash.elim,rec_gluel],
  end

  @[hott] theorem elim_gluer {P : Type _} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (b : B) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (gluer b) = Pgr b :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (@gluer A B b)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑smash.elim,rec_gluer],
  end

  @[hott] theorem elim_glue {P : Type _} {Pmk : Πa b, P} {Pl Pr : P}
    (Pgl : Πa : A, Pmk a pt = Pl) (Pgr : Πb : B, Pmk pt b = Pr) (a : A) (b : B) :
    ap (smash.elim Pmk Pl Pr Pgl Pgr) (glue a b) = (Pgl a ⬝ (Pgl pt)⁻¹) ⬝ (Pgr pt ⬝ (Pgr b)⁻¹) :=
  by rewrite [↑glue, ↑gluel', ↑gluer', +ap_con, +ap_inv, +elim_gluel, +elim_gluer]

end smash
open smash
attribute smash.mk smash.mk' auxl auxr
attribute smash.elim' smash.rec smash.elim [recursor 9]

namespace smash

  variables {A B : Type*}

  @[hott] def of_smash_pbool (x : smash A pbool) : A :=
  begin
    induction x,
    { induction b, exact pt, exact a },
    { exact pt },
    { exact pt },
    { reflexivity },
    { induction b: reflexivity }
  end

  @[hott] def smash_pbool_pequiv (A : Type*) : smash A pbool ≃* A :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact of_smash_pbool },
      { intro a, exact smash.mk a tt },
      { intro a, reflexivity },
      { exact abstract begin intro x, induction x,
        { induction b, exact gluer' tt pt ⬝ gluel' pt a, reflexivity },
        { exact gluer' tt ff ⬝ gluel pt, },
        { exact gluer tt, },
        { apply eq_pathover_id_right,
          refine ap_compose (λa, smash.mk a tt) _ _ ⬝ ap02 _ !elim_gluel ⬝ph _,
          apply square_of_eq_top, refine !con.assoc⁻¹ ⬝ whisker_right _ !idp_con⁻¹ },
        { apply eq_pathover_id_right,
          refine ap_compose (λa, smash.mk a tt) _ _ ⬝ ap02 _ !elim_gluer ⬝ph _,
          induction b: esimp,
          { apply square_of_eq_top,
            refine whisker_left _ !con.right_inv ⬝ !con_idp ⬝ whisker_right _ !idp_con⁻¹ },
          { apply square_of_eq idp }} end end }},
    { reflexivity }
  end

end smash
