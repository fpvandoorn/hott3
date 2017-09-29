/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

@[hott] def of general colimits and sequential colimits.
-/

/- @[hott] def of a general colimit -/
open eq nat quotient sigma equiv is_trunc

namespace colimit
section
  parameters {I J : Type _} (A : I → Type _) (dom cod : J → I)
             (f : Π(j : J), A (dom j) → A (cod j))
  variables {i : I} (a : A i) (j : J) (b : A (dom j))

  local abbreviation B := Σ(i : I), A i
  inductive colim_rel : B → B → Type _ :=
  | Rmk : Π{j : J} (a : A (dom j)), colim_rel ⟨cod j, f j a⟩ ⟨dom j, a⟩
  open colim_rel
  local abbreviation R := colim_rel

  -- TODO: define this in root namespace
  @[hott] def colimit : Type _ :=
  quotient colim_rel

  @[hott] def incl : colimit :=
  class_of R ⟨i, a⟩
  abbreviation ι := @incl

  @[hott] def cglue : ι (f j b) = ι b :=
  eq_of_rel colim_rel (Rmk f b)

   @[hott] protected def rec {P : colimit → Type _}
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x))
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) =[cglue j x] Pincl x)
      (y : colimit) : P y :=
  begin
    fapply (quotient.rec_on y),
    { intro a, cases a, apply Pincl},
    { intros a a' H, cases H, apply Pglue}
  end

  @[hott] protected def rec_on [reducible] {P : colimit → Type _} (y : colimit)
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x))
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) =[cglue j x] Pincl x) : P y :=
  rec Pincl Pglue y

  @[hott] theorem rec_cglue {P : colimit → Type _}
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x))
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) =[cglue j x] Pincl x)
      {j : J} (x : A (dom j)) : apd (rec Pincl Pglue) (cglue j x) = Pglue j x :=
  !rec_eq_of_rel

  @[hott] protected def elim {P : Type _} (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x) (y : colimit) : P :=
  rec Pincl (λj a, pathover_of_eq _ (Pglue j a)) y

  @[hott] protected def elim_on [reducible] {P : Type _} (y : colimit)
    (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x) : P :=
  elim Pincl Pglue y

  @[hott] theorem elim_cglue {P : Type _}
    (Pincl : Π⦃i : I⦄ (x : A i), P)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) = Pincl x)
      {j : J} (x : A (dom j)) : ap (elim Pincl Pglue) (cglue j x) = Pglue j x :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (cglue j x)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim,rec_cglue],
  end

  @[hott] protected def elim_type (Pincl : Π⦃i : I⦄ (x : A i), Type _)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x) (y : colimit) : Type _ :=
  elim Pincl (λj a, ua (Pglue j a)) y

  @[hott] protected def elim_type_on [reducible] (y : colimit)
    (Pincl : Π⦃i : I⦄ (x : A i), Type _)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x) : Type _ :=
  elim_type Pincl Pglue y

  @[hott] theorem elim_type_cglue (Pincl : Π⦃i : I⦄ (x : A i), Type _)
    (Pglue : Π(j : J) (x : A (dom j)), Pincl (f j x) ≃ Pincl x)
      {j : J} (x : A (dom j)) : transport (elim_type Pincl Pglue) (cglue j x) = Pglue j x :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_cglue];apply cast_ua_fn

  @[hott] protected def rec_prop {P : colimit → Type _} [H : Πx, is_prop (P x)]
    (Pincl : Π⦃i : I⦄ (x : A i), P (ι x)) (y : colimit) : P y :=
  rec Pincl (λa b, !is_prop.elimo) y

  @[hott] protected def elim_prop {P : Type _} [H : is_prop P] (Pincl : Π⦃i : I⦄ (x : A i), P)
    (y : colimit) : P :=
  elim Pincl (λa b, !is_prop.elim) y

end
end colimit

/- @[hott] def of a sequential colimit -/
namespace seq_colim
section
  /-
    we define it directly in terms of quotients. An alternative @[hott] def could be
    @[hott] def seq_colim := colimit.colimit A id succ f
  -/
  parameters {A : ℕ → Type _} (f : Π⦃n⦄, A n → A (succ n))
  variables {n : ℕ} (a : A n)

  local abbreviation B := Σ(n : ℕ), A n
  inductive seq_rel : B → B → Type _ :=
  | Rmk : Π{n : ℕ} (a : A n), seq_rel ⟨succ n, f a⟩ ⟨n, a⟩
  open seq_rel
  local abbreviation R := seq_rel

  -- TODO: define this in root namespace
  @[hott] def seq_colim : Type _ :=
  quotient seq_rel

  @[hott] def inclusion : seq_colim :=
  class_of R ⟨n, a⟩

  abbreviation sι := @inclusion

  @[hott] def glue : sι (f a) = sι a :=
  eq_of_rel seq_rel (Rmk f a)

  @[hott] protected def rec {P : seq_colim → Type _}
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π(n : ℕ) (a : A n), Pincl (f a) =[glue a] Pincl a) (aa : seq_colim) : P aa :=
  begin
    fapply (quotient.rec_on aa),
    { intro a, cases a, apply Pincl},
    { intros a a' H, cases H, apply Pglue}
  end

  @[hott] protected def rec_on [reducible] {P : seq_colim → Type _} (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue a] Pincl a)
      : P aa :=
  rec Pincl Pglue aa

  @[hott] theorem rec_glue {P : seq_colim → Type _} (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a))
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue a] Pincl a) {n : ℕ} (a : A n)
      : apd (rec Pincl Pglue) (glue a) = Pglue a :=
  !rec_eq_of_rel

  @[hott] protected def elim {P : Type _} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) : seq_colim → P :=
  rec Pincl (λn a, pathover_of_eq _ (Pglue a))

  @[hott] protected def elim_on [reducible] {P : Type _} (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) : P :=
  elim Pincl Pglue aa

  @[hott] theorem elim_glue {P : Type _} (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) = Pincl a) {n : ℕ} (a : A n)
      : ap (elim Pincl Pglue) (glue a) = Pglue a :=
  begin
    apply eq_of_fn_eq_fn_inv !(pathover_constant (glue a)),
    rewrite [▸*,-apd_eq_pathover_of_eq_ap,↑elim,rec_glue],
  end

  @[hott] protected def elim_type (Pincl : Π⦃n : ℕ⦄ (a : A n), Type _)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) : seq_colim → Type _ :=
  elim Pincl (λn a, ua (Pglue a))

  @[hott] protected def elim_type_on [reducible] (aa : seq_colim)
    (Pincl : Π⦃n : ℕ⦄ (a : A n), Type _)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) : Type _ :=
  elim_type Pincl Pglue aa

  @[hott] theorem elim_type_glue (Pincl : Π⦃n : ℕ⦄ (a : A n), Type _)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) {n : ℕ} (a : A n)
      : transport (elim_type Pincl Pglue) (glue a) = Pglue a :=
  by rewrite [tr_eq_cast_ap_fn,↑elim_type,elim_glue]; apply cast_ua_fn

  @[hott] theorem elim_type_glue_inv (Pincl : Π⦃n : ℕ⦄ (a : A n), Type _)
    (Pglue : Π⦃n : ℕ⦄ (a : A n), Pincl (f a) ≃ Pincl a) {n : ℕ} (a : A n)
    : transport (seq_colim.elim_type f Pincl Pglue) (glue a)⁻¹ = to_inv (Pglue a) :=
  by rewrite [tr_eq_cast_ap_fn, ↑seq_colim.elim_type, ap_inv, elim_glue]; apply cast_ua_inv_fn

  @[hott] protected def rec_prop {P : seq_colim → Type _} [H : Πx, is_prop (P x)]
    (Pincl : Π⦃n : ℕ⦄ (a : A n), P (sι a)) (aa : seq_colim) : P aa :=
  rec Pincl (λa b, !is_prop.elimo) aa

  @[hott] protected def elim_prop {P : Type _} [H : is_prop P] (Pincl : Π⦃n : ℕ⦄ (a : A n), P)
    : seq_colim → P :=
  elim Pincl (λa b, !is_prop.elim)


end
end seq_colim

attribute colimit.incl seq_colim.inclusion
attribute colimit.rec colimit.elim [recursor 10]
attribute colimit.elim_type
attribute colimit.rec_on colimit.elim_on
attribute colimit.elim_type_on
attribute seq_colim.rec seq_colim.elim [recursor 6]
attribute seq_colim.elim_type
attribute seq_colim.rec_on seq_colim.elim_on
attribute seq_colim.elim_type_on
