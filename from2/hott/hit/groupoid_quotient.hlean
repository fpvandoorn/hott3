/-
Copyright (c) 2015-16 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

The groupoid quotient. This is a 1-type which path spaces is the same as the morphisms
a given groupoid. We define it as the 1-truncation of a two quotient.
-/

import algebra.category.groupoid .two_quotient homotopy.connectedness
       algebra.group_theory

open trunc_two_quotient eq bool unit relation category e_closure iso is_trunc trunc equiv is_equiv
     group

namespace groupoid_quotient
section
  parameter (G : Groupoid)

  inductive groupoid_quotient_R : G → G → Type _ :=
  | Rmk : Π{a b : G} (f : a ⟶ b), groupoid_quotient_R a b

  open groupoid_quotient_R
  local abbreviation R := groupoid_quotient_R

  inductive groupoid_quotient_Q : Π⦃x y : G⦄,
    e_closure groupoid_quotient_R x y → e_closure groupoid_quotient_R x y → Type _ :=
  | Qconcat : Π{a b c : G} (g : b ⟶ c) (f : a ⟶ b),
                groupoid_quotient_Q [Rmk (g ∘ f)] ([Rmk f] ⬝r [Rmk g])

  open groupoid_quotient_Q
  local abbreviation Q := groupoid_quotient_Q

  @[hott] def groupoid_quotient := trunc_two_quotient 1 R Q

  local attribute groupoid_quotient [reducible]
  @[hott] def is_trunc_groupoid_quotient [instance] : is_trunc 1 groupoid_quotient := _

  parameter {G}
  variables {a b c : G}
  @[hott] def elt (a : G) : groupoid_quotient := incl0 a
  @[hott] def pth (f : a ⟶ b) : elt a = elt b := incl1 (Rmk f)
  @[hott] def resp_comp (g : b ⟶ c) (f : a ⟶ b) : pth (g ∘ f) = pth f ⬝ pth g := incl2 (Qconcat g f)
  @[hott] def resp_id (a : G) : pth (ID a) = idp :=
  begin
    apply cancel_right (pth (id)), refine _ ⬝ !idp_con⁻¹,
    refine !resp_comp⁻¹ ⬝ _,
    exact ap pth !id_id,
  end

  @[hott] def resp_inv (f : a ⟶ b) : pth (f⁻¹) = (pth f)⁻¹ :=
  begin
    apply eq_inv_of_con_eq_idp',
    refine !resp_comp⁻¹ ⬝ _,
    refine ap pth !right_inverse ⬝ _,
    apply resp_id
  end

  @[hott] protected def rec {P : groupoid_quotient → Type _} [Πx, is_trunc 1 (P x)]
    (Pe : Πg, P (elt g)) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a =[pth f] Pe b)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b),
      change_path (resp_comp g f) (Pp (g ∘ f)) = Pp f ⬝o Pp g)
    (x : groupoid_quotient) : P x :=
  begin
    induction x,
    { apply Pe},
    { induction s with a b f, apply Pp},
    { induction q with a b c g f,
      apply Pcomp}
  end

  @[hott] protected def rec_on {P : groupoid_quotient → Type _} [Πx, is_trunc 1 (P x)]
    (x : groupoid_quotient)
    (Pe : Πg, P (elt g)) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a =[pth f] Pe b)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b),
      change_path (resp_comp g f) (Pp (g ∘ f)) = Pp f ⬝o Pp g) : P x :=
  rec Pe Pp Pcomp x

  @[hott] protected def set_rec {P : groupoid_quotient → Type _} [Πx, is_set (P x)]
    (Pe : Πg, P (elt g)) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a =[pth f] Pe b)
    (x : groupoid_quotient) : P x :=
  rec Pe Pp !center x

  @[hott] protected def prop_rec {P : groupoid_quotient → Type _} [Πx, is_prop (P x)]
    (Pe : Πg, P (elt g)) (x : groupoid_quotient) : P x :=
  rec Pe !center !center x

  @[hott] def rec_pth {P : groupoid_quotient → Type _} [Πx, is_trunc 1 (P x)]
    {Pe : Πg, P (elt g)} {Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a =[pth f] Pe b}
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b),
      change_path (resp_comp g f) (Pp (g ∘ f)) = Pp f ⬝o Pp g)
    {a b : G} (f : a ⟶ b) : apd (rec Pe Pp Pcomp) (pth f) = Pp f :=
  proof !rec_incl1 qed

  @[hott] protected def elim {P : Type _} [is_trunc 1 P] (Pe : G → P)
    (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    (x : groupoid_quotient) : P :=
  begin
    induction x,
    { exact Pe a},
    { induction s with a b f, exact Pp f},
    { induction q with a b c g f,
      exact Pcomp g f}
  end

  @[hott] protected def elim_on [reducible] {P : Type _} [is_trunc 1 P] (x : groupoid_quotient)
    (Pe : G → P) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g) : P :=
  elim Pe Pp Pcomp x

  @[hott] protected def set_elim [reducible] {P : Type _} [is_set P] (Pe : G → P)
    (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b)
    (x : groupoid_quotient) : P :=
  elim Pe Pp !center x

  @[hott] protected def prop_elim [reducible] {P : Type _} [is_prop P] (Pe : G → P)
    (x : groupoid_quotient) : P :=
  elim Pe !center !center x

  @[hott] def elim_pth {P : Type _} [is_trunc 1 P] {Pe : G → P} {Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b}
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g) {a b : G} (f : a ⟶ b) :
    ap (elim Pe Pp Pcomp) (pth f) = Pp f :=
  !elim_incl1

  -- The following rule is also true because P is a 1-type, and can be proven by `!is_set.elims`
  -- The following is the canonical proofs which holds for any truncated two-quotient.
  @[hott] theorem elim_resp_comp {P : Type _} [is_trunc 1 P] {Pe : G → P}
    {Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a = Pe b}
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b), Pp (g ∘ f) = Pp f ⬝ Pp g)
    {a b c : G} (g : b ⟶ c) (f : a ⟶ b)
    : square (ap02 (elim Pe Pp Pcomp) (resp_comp g f))
             (Pcomp g f)
             (elim_pth Pcomp (g ∘ f))
             (!ap_con ⬝ (elim_pth Pcomp f ◾ elim_pth Pcomp g)) :=
  proof !elim_incl2 qed

  @[hott] protected def elim_set.{u} (Pe : G → Set.{u}) (Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a ≃ Pe b)
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b) (x : Pe a), Pp (g ∘ f) x = Pp g (Pp f x))
    (x : groupoid_quotient) : Set.{u} :=
  elim Pe (λa b f, tua (Pp f)) (λa b c g f, ap tua (equiv_eq (Pcomp g f)) ⬝ !tua_trans) x

  @[hott] theorem elim_set_pth {Pe : G → Set} {Pp : Π⦃a b⦄ (f : a ⟶ b), Pe a ≃ Pe b}
    (Pcomp : Π⦃a b c⦄ (g : b ⟶ c) (f : a ⟶ b) (x : Pe a), Pp (g ∘ f) x = Pp g (Pp f x))
    {a b : G} (f : a ⟶ b) :
    transport (elim_set Pe Pp Pcomp) (pth f) = Pp f :=
  by rewrite [tr_eq_cast_ap_fn, ↑elim_set, ▸*, ap_compose' trunctype.carrier, elim_pth];
     apply tcast_tua_fn

end
end groupoid_quotient

attribute groupoid_quotient.elt
attribute groupoid_quotient.rec groupoid_quotient.elim [recursor 7]
attribute groupoid_quotient.rec_on groupoid_quotient.elim_on
attribute groupoid_quotient.set_rec groupoid_quotient.set_elim
attribute groupoid_quotient.prop_rec groupoid_quotient.prop_elim
          groupoid_quotient.elim_set


open sigma pi is_conn function
namespace groupoid_quotient
section
  universe variables u v
  variables {G : Groupoid.{u v}} (a : G) {b c : G}

  include a

  @[hott] protected def code (x : groupoid_quotient G) : Set.{v} :=
  begin
    refine groupoid_quotient.elim_set _ _ _ x,
    { intro b, exact homset a b},
    { intros b c g, exact equiv_postcompose g},
    { intros b c d h g f, esimp at *, apply assoc'}
  end

  omit a

  local abbreviation code := @groupoid_quotient.code G a

  variable {a}
  @[hott] protected def encode (x : groupoid_quotient G) (p : elt a = x) : code a x :=
  transport (code a) p (ID a)

  @[hott] protected def decode (x : groupoid_quotient G) (z : code a x) : elt a = x :=
  begin
    induction x using groupoid_quotient.set_rec with b b c g,
    { esimp, exact pth z},
    { apply arrow_pathover_left, esimp, intro f, apply eq_pathover_constant_left_id_right,
      apply square_of_eq, refine !resp_comp⁻¹ ⬝ _ ⬝ !idp_con⁻¹, rewrite elim_set_pth}
  end

  local abbreviation encode := @groupoid_quotient.encode G a
  local abbreviation decode := @groupoid_quotient.decode G a

  @[hott] protected def decode_encode (x : groupoid_quotient G) (p : elt a = x) :
    decode x (encode x p) = p :=
  begin induction p, esimp, apply resp_id end

  @[hott] protected def encode_decode (x : groupoid_quotient G) (z : code a x) :
    encode x (decode x z) = z :=
  begin
    induction x using groupoid_quotient.prop_rec with b,
    esimp, refine ap10 !elim_set_pth.{u v v} (ID a) ⬝ _, esimp,
    apply id_right
  end

  @[hott] def decode_comp (z : code a (elt b)) (z' : code b (elt c)) :
    decode (elt c) (z' ∘ z) = decode (elt b) z ⬝ decode (elt c) z' :=
  !resp_comp

  variables (a b)
  @[hott] def elt_eq_elt_equiv : (elt a = elt b) ≃ (a ⟶ b) :=
  equiv.MK (encode (elt b)) (decode (elt b))
           (groupoid_quotient.encode_decode (elt b)) (groupoid_quotient.decode_encode (elt b))

  variables {a b}
  @[hott] def encode_con (p : elt a = elt b)
    (q : elt b = elt c) : encode (elt c) (p ⬝ q) = encode (elt c) q ∘ encode (elt b) p :=
  begin
    apply eq_of_fn_eq_fn (elt_eq_elt_equiv a c)⁻¹ᵉ,
    refine !right_inv ⬝ _ ⬝ !decode_comp⁻¹,
    apply concat2, do 2 exact (to_left_inv !elt_eq_elt_equiv _)⁻¹
  end

  variable (G)
  @[hott] def is_conn_groupoid_quotient [H : is_conn 0 G] : is_conn 0 (groupoid_quotient G) :=
  begin
    have g : trunc 0 G, from !center,
    induction g with g,
    have p : Πh, ∥ g = h ∥,
    begin
      intro h, refine !tr_eq_tr_equiv _, apply is_prop.elim
    end,
    fapply is_contr.mk,
    { apply trunc_functor 0 elt (tr g)},
    { intro x, induction x with x,
      induction x using groupoid_quotient.prop_rec with b, esimp,
      induction p b with q, exact ap (tr ∘ elt) q}
  end

end

end groupoid_quotient

export groupoid_quotient
