/-
Copyright (c) 2015 Haitao Zhang. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Haitao Zhang, Leonardo de Moura, Jakob von Raumer, Floris van Doorn

Finite ordinal types.
-/
import types.list algebra.bundled function logic types.prod types.sum types.nat.div
open eq function list equiv is_trunc algebra sigma sum nat

structure fin (n : nat) := (val : nat) (is_lt : val < n)

@[hott] def less_than [reducible] := fin

namespace fin

attribute fin.val [coercion]

section def_equal
variable {n : nat}

protected @[hott] def sigma_char : fin n ≃ Σ (val : nat), val < n :=
begin
  fapply equiv.MK,
    intro i, cases i with i ilt, apply dpair i ilt,
    intro s, cases s with i ilt, apply fin.mk i ilt,
    intro s, cases s with i ilt, reflexivity,
    intro i, cases i with i ilt, reflexivity
end

@[hott] def is_set_fin [instance] : is_set (fin n) :=
begin
  assert H : Πa, is_set (a < n), exact _, -- I don't know why this is necessary
  apply is_trunc_equiv_closed_rev, apply fin.sigma_char,
end

@[hott] def eq_of_veq : Π {i j : fin n}, (val i) = j → i = j :=
begin
  intros i j, cases i with i ilt, cases j with j jlt, esimp,
  intro p, induction p, apply ap (mk i), apply !is_prop.elim
end

@[hott] def fin_eq := @eq_of_veq

@[hott] def eq_of_veq_refl (i : fin n) : eq_of_veq (refl (val i)) = idp :=
!is_prop.elim

@[hott] def veq_of_eq : Π {i j : fin n}, i = j → (val i) = j :=
by intros i j P; apply ap val; exact P


@[hott] def eq_iff_veq {i j : fin n} : (val i) = j ↔ i = j :=
pair eq_of_veq veq_of_eq

@[hott] def val_inj := @eq_of_veq n

end def_equal

section decidable
open decidable

protected @[hott] def has_decidable_eq [instance] (n : nat) :
  Π (i j : fin n), decidable (i = j) :=
begin
  intros i j, apply decidable_of_decidable_of_iff,
  apply nat.has_decidable_eq i j, apply eq_iff_veq,
end

end decidable

/-@[hott] lemma dinj_lt (n : nat) : dinj (λ i, i < n) fin.mk :=
take a1 a2 Pa1 Pa2 Pmkeq, fin.no_confusion Pmkeq (λ Pe Pqe, Pe)

@[hott] lemma val_mk (n i : nat) (Plt : i < n) : fin.val (fin.mk i Plt) = i := rfl

@[hott] def upto [reducible] (n : nat) : list (fin n) :=
dmap (λ i, i < n) fin.mk (list.upto n)

@[hott] lemma nodup_upto (n : nat) : nodup (upto n) :=
dmap_nodup_of_dinj (dinj_lt n) (list.nodup_upto n)

@[hott] lemma mem_upto (n : nat) : Π (i : fin n), i ∈ upto n :=
take i, fin.destruct i
  (take ival Piltn,
    have ival ∈ list.upto n, from mem_upto_of_lt Piltn,
    mem_dmap Piltn this)

@[hott] lemma upto_zero : upto 0 = [] :=
by rewrite [↑upto, list.upto_nil, dmap_nil]

@[hott] lemma map_val_upto (n : nat) : map fin.val (upto n) = list.upto n :=
map_dmap_of_inv_of_pos (val_mk n) (@lt_of_mem_upto n)

@[hott] lemma length_upto (n : nat) : length (upto n) = n :=
calc
  length (upto n) = length (list.upto n) : (map_val_upto n ▸ length_map fin.val (upto n))⁻¹
              ... = n                    : list.length_upto n

@[hott] def is_fintype [instance] (n : nat) : fintype (fin n) :=
fintype.mk (upto n) (nodup_upto n) (mem_upto n)

section pigeonhole
open fintype

@[hott] lemma card_fin (n : nat) : card (fin n) = n := length_upto n

@[hott] theorem pigeonhole {n m : nat} (Pmltn : m < n) : ¬Σ f : fin n → fin m, injective f :=
assume Pex, absurd Pmltn (not_lt_of_ge
  (calc
       n = card (fin n) : card_fin
     ... ≤ card (fin m) : card_le_of_inj (fin n) (fin m) Pex
     ... = m : card_fin))

end pigeonhole-/

protected @[hott] def zero (n : nat) : fin (succ n) :=
mk 0 !zero_lt_succ

@[hott] def fin_has_zero [instance] (n : nat) : has_zero (fin (succ n)) :=
has_zero.mk (fin.zero n)

@[hott] def val_zero (n : nat) : val (0 : fin (succ n)) = 0 := rfl

@[hott] def mk_mod [reducible] (n i : nat) : fin (succ n) :=
mk (i % (succ n)) (mod_lt _ !zero_lt_succ)

@[hott] theorem mk_mod_zero_eq (n : nat) : mk_mod n 0 = 0 :=
apd011 fin.mk rfl !is_prop.elimo

variable {n : nat}

@[hott] theorem val_lt : Π i : fin n, val i < n
| (mk v h) := h

@[hott] lemma max_lt (i j : fin n) : max i j < n :=
max_lt (is_lt i) (is_lt j)

@[hott] def lift : fin n → Π m : nat, fin (n + m)
| (mk v h) m := mk v (lt_add_of_lt_right h m)

@[hott] def lift_succ (i : fin n) : fin (nat.succ n) :=
have r : fin (n+1), from lift i 1,
r

@[hott] def maxi [reducible] : fin (succ n) :=
mk n !lt_succ_self

@[hott] def val_lift : Π (i : fin n) (m : nat), val i = val (lift i m)
| (mk v h) m := rfl

@[hott] lemma mk_succ_ne_zero {i : nat} : Π {P}, mk (succ i) P ≠ (0 : fin (succ n)) :=
assume P Pe, absurd (veq_of_eq Pe) !succ_ne_zero

@[hott] lemma mk_mod_eq {i : fin (succ n)} : i = mk_mod n i :=
eq_of_veq begin rewrite [↑mk_mod, mod_eq_of_lt !is_lt] end

@[hott] lemma mk_mod_of_lt {i : nat} (Plt : i < succ n) : mk_mod n i = mk i Plt :=
begin esimp [mk_mod], congruence, exact mod_eq_of_lt Plt end

section lift_lower

@[hott] lemma lift_zero : lift_succ (0 : fin (succ n)) = (0 : fin (succ (succ n))) :=
by apply eq_of_veq; reflexivity

@[hott] lemma ne_max_of_lt_max {i : fin (succ n)} : i < n → i ≠ maxi :=
begin
  intros hlt he,
  have he' : maxi = i, by apply he⁻¹,
  induction he', apply nat.lt_irrefl n hlt,
end

@[hott] lemma lt_max_of_ne_max {i : fin (succ n)} : i ≠ maxi → i < n :=
assume hne  : i ≠ maxi,
have vne  : val i ≠ n, from
  assume he,
    have val (@maxi n) = n,   from rfl,
    have val i = val (@maxi n), from he ⬝ this⁻¹,
    absurd (eq_of_veq this) hne,
have val i < nat.succ n, from val_lt i,
lt_of_le_of_ne (le_of_lt_succ this) vne

@[hott] lemma lift_succ_ne_max {i : fin n} : lift_succ i ≠ maxi :=
begin
  cases i with v hlt, esimp [lift_succ, lift, max], intro he,
  injection he, substvars,
  exact absurd hlt (lt.irrefl v)
end

@[hott] lemma lift_succ_inj [instance] : is_embedding (@lift_succ n) :=
begin
  apply is_embedding_of_is_injective, intros i j,
  induction i with iv ilt, induction j with jv jlt, intro Pmkeq,
  apply eq_of_veq, apply veq_of_eq Pmkeq
end

@[hott] def lt_of_inj_of_max (f : fin (succ n) → fin (succ n)) :
  is_embedding f → (f maxi = maxi) → Π i : fin (succ n), i < n → f i < n :=
assume Pinj Peq, take i, assume Pilt,
have P1 : f i = f maxi → i = maxi, from assume Peq, is_injective_of_is_embedding Peq,
have f i ≠ maxi, from
     begin rewrite -Peq, intro P2, apply absurd (P1 P2) (ne_max_of_lt_max Pilt) end,
lt_max_of_ne_max this

@[hott] def lift_fun : (fin n → fin n) → (fin (succ n) → fin (succ n)) :=
λ f i, dite (i = maxi) (λ Pe, maxi) (λ Pne, lift_succ (f (mk i (lt_max_of_ne_max Pne))))

@[hott] def lower_inj (f : fin (succ n) → fin (succ n)) (inj : is_embedding f) :
  f maxi = maxi → fin n → fin n :=
assume Peq, take i, mk (f (lift_succ i)) (lt_of_inj_of_max f inj Peq (lift_succ i) (lt_max_of_ne_max lift_succ_ne_max))

@[hott] lemma lift_fun_max {f : fin n → fin n} : lift_fun f maxi = maxi :=
begin rewrite [↑lift_fun, dif_pos rfl] end

@[hott] lemma lift_fun_of_ne_max {f : fin n → fin n} {i} (Pne : i ≠ maxi) :
  lift_fun f i = lift_succ (f (mk i (lt_max_of_ne_max Pne))) :=
begin rewrite [↑lift_fun, dif_neg Pne] end

@[hott] lemma lift_fun_eq {f : fin n → fin n} {i : fin n} :
  lift_fun f (lift_succ i) = lift_succ (f i) :=
begin
  rewrite [lift_fun_of_ne_max lift_succ_ne_max], do 2 congruence,
  apply eq_of_veq, esimp, rewrite -val_lift,
end

@[hott] lemma lift_fun_of_inj {f : fin n → fin n} : is_embedding f → is_embedding (lift_fun f) :=
begin
  intro Pemb, apply is_embedding_of_is_injective, intros i j,
  have Pdi : decidable (i = maxi), by apply _,
  have Pdj : decidable (j = maxi), by apply _,
  cases Pdi with Pimax Pinmax,
    cases Pdj with Pjmax Pjnmax,
      substvars, intros, reflexivity,
      substvars, rewrite [lift_fun_max, lift_fun_of_ne_max Pjnmax],
        intro Plmax, apply absurd Plmax⁻¹ lift_succ_ne_max,
    cases Pdj with Pjmax Pjnmax,
      substvars, rewrite [lift_fun_max, lift_fun_of_ne_max Pinmax],
        intro Plmax, apply absurd Plmax lift_succ_ne_max,
      rewrite [lift_fun_of_ne_max Pinmax, lift_fun_of_ne_max Pjnmax],
        intro Peq, apply eq_of_veq,
        cases i with i ilt, cases j with j jlt, esimp at *,
        fapply veq_of_eq, apply is_injective_of_is_embedding,
        apply @is_injective_of_is_embedding _ _ lift_succ _ _ _ Peq,
end

@[hott] lemma lift_fun_inj : is_embedding (@lift_fun n) :=
begin
  apply is_embedding_of_is_injective, intros f f' Peq, apply eq_of_homotopy, intro i,
  have H : lift_fun f (lift_succ i) = lift_fun f' (lift_succ i), by apply congr_fun Peq _,
  revert H, rewrite [*lift_fun_eq], apply is_injective_of_is_embedding,
end

@[hott] lemma lower_inj_apply {f Pinj Pmax} (i : fin n) :
  val (lower_inj f Pinj Pmax i) = val (f (lift_succ i)) :=
by rewrite [↑lower_inj]

end lift_lower

section madd

@[hott] def madd (i j : fin (succ n)) : fin (succ n) :=
mk ((i + j) % (succ n)) (mod_lt _ !zero_lt_succ)

@[hott] def minv : Π i : fin (succ n), fin (succ n)
| (mk iv ilt) := mk ((succ n - iv) % succ n) (mod_lt _ !zero_lt_succ)

@[hott] lemma val_madd : Π i j : fin (succ n), val (madd i j) = (i + j) % (succ n)
| (mk iv ilt) (mk jv jlt) := by esimp

@[hott] lemma madd_inj : Π {i : fin (succ n)}, is_embedding (madd i)
| (mk iv ilt) := is_embedding_of_is_injective
(take j₁ j₂, fin.destruct j₁ (fin.destruct j₂ (λ jv₁ jlt₁ jv₂ jlt₂, begin
  rewrite [↑madd],
  intro Peq', note Peq := ap val Peq', congruence,
  rewrite [-(mod_eq_of_lt jlt₁), -(mod_eq_of_lt jlt₂)],
  apply mod_eq_mod_of_add_mod_eq_add_mod_left Peq
end)))

@[hott] lemma madd_mk_mod {i j : nat} : madd (mk_mod n i) (mk_mod n j) = mk_mod n (i+j) :=
eq_of_veq begin esimp [madd, mk_mod], rewrite [ mod_add_mod, add_mod_mod ] end

@[hott] lemma val_mod : Π i : fin (succ n), (val i) % (succ n) = val i
| (mk iv ilt) := by esimp; rewrite [(mod_eq_of_lt ilt)]

@[hott] lemma madd_comm (i j : fin (succ n)) : madd i j = madd j i :=
by apply eq_of_veq; rewrite [*val_madd, add.comm (val i)]

@[hott] lemma zero_madd (i : fin (succ n)) : madd 0 i = i :=
have H : madd (fin.zero n) i = i,
  by apply eq_of_veq; rewrite [val_madd, ↑fin.zero, nat.zero_add, mod_eq_of_lt (is_lt i)],
H

@[hott] lemma madd_zero (i : fin (succ n)) : madd i (fin.zero n) = i :=
!madd_comm ▸ zero_madd i

@[hott] lemma madd_assoc (i j k : fin (succ n)) : madd (madd i j) k = madd i (madd j k) :=
by apply eq_of_veq; rewrite [*val_madd, mod_add_mod, add_mod_mod, add.assoc (val i)]

@[hott] lemma madd_left_inv : Π i : fin (succ n), madd (minv i) i = fin.zero n
| (mk iv ilt) := eq_of_veq (by
  rewrite [val_madd, ↑minv, mod_add_mod, nat.sub_add_cancel (le_of_lt ilt), mod_self])

@[hott] def madd_is_ab_group [instance] : add_ab_group (fin (succ n)) :=
ab_group.mk _ madd madd_assoc (fin.zero n) zero_madd madd_zero minv madd_left_inv madd_comm

@[hott] def gfin (n : ℕ) [H : is_succ n] : AddAbGroup.{0} :=
by induction H with n; exact AddAbGroup.mk (fin (succ n)) _

end madd

@[hott] def pred : fin n → fin n
| (mk v h) := mk (nat.pred v) (pre_lt_of_lt h)

@[hott] lemma val_pred : Π (i : fin n), val (pred i) = nat.pred (val i)
| (mk v h) := rfl

@[hott] lemma pred_zero : pred (fin.zero n) = fin.zero n :=
begin
  induction n, reflexivity, apply eq_of_veq, reflexivity,
end

@[hott] def mk_pred (i : nat) (h : succ i < succ n) : fin n :=
mk i (lt_of_succ_lt_succ h)

@[hott] def succ : fin n → fin (succ n)
| (mk v h) := mk (nat.succ v) (succ_lt_succ h)

@[hott] lemma val_succ : Π (i : fin n), val (succ i) = nat.succ (val i)
| (mk v h) := rfl

@[hott] lemma succ_max : fin.succ maxi = (@maxi (nat.succ n)) := rfl

@[hott] lemma lift_succ.comm : lift_succ ∘ (@succ n) = succ ∘ lift_succ :=
eq_of_homotopy take i,
  eq_of_veq (begin rewrite [↑lift_succ, -val_lift, *val_succ, -val_lift] end)

@[hott] def elim0 {C : fin 0 → Type _} : Π i : fin 0, C i
| (mk v h) := absurd h !not_lt_zero

@[hott] def zero_succ_cases {C : fin (nat.succ n) → Type _} :
  C (fin.zero n) → (Π j : fin n, C (succ j)) → (Π k : fin (nat.succ n), C k) :=
begin
  intros CO CS k,
  induction k with [vk, pk],
  induction (nat.decidable_lt 0 vk) with [HT, HF],
  { show C (mk vk pk), from
    let vj := nat.pred vk in
    have vk = nat.succ vj, from
      inverse (succ_pred_of_pos HT),
    have vj < n, from
      lt_of_succ_lt_succ (eq.subst `vk = nat.succ vj` pk),
    have succ (mk vj `vj < n`) = mk vk pk, by apply val_inj; apply (succ_pred_of_pos HT),
    eq.rec_on this (CS (mk vj `vj < n`)) },
  { show C (mk vk pk), from
    have vk = 0, from
      eq_zero_of_le_zero (le_of_not_gt HF),
    have fin.zero n = mk vk pk, from
      val_inj (inverse this),
    eq.rec_on this CO }
end

@[hott] def succ_maxi_cases {C : fin (nat.succ n) → Type _} :
  (Π j : fin n, C (lift_succ j)) → C maxi → (Π k : fin (nat.succ n), C k) :=
begin
  intros CL CM k,
  induction k with [vk, pk],
  induction (nat.decidable_lt vk n) with [HT, HF],
  { show C (mk vk pk), from
    have HL : lift_succ (mk vk HT) = mk vk pk, from
      val_inj rfl,
    eq.rec_on HL (CL (mk vk HT)) },
  { show C (mk vk pk), from
    have HMv : vk = n, from
      le.antisymm (le_of_lt_succ pk) (le_of_not_gt HF),
    have HM : maxi = mk vk pk, from
      val_inj (inverse HMv),
    eq.rec_on HM CM }
end

open decidable

-- TODO there has to be a less painful way to do this
@[hott] def elim_succ_maxi_cases_lift_succ {C : fin (nat.succ n) → Type _}
  {Cls : Π j : fin n, C (lift_succ j)} {Cm : C maxi} (i : fin n) :
  succ_maxi_cases Cls Cm (lift_succ i) = Cls i :=
begin
  esimp[succ_maxi_cases], cases i with i ilt, esimp,
  apply decidable.rec,
  { intro ilt', esimp[val_inj], apply concat,
    apply ap (λ x, eq.rec_on x _), esimp[eq_of_veq, rfl], reflexivity,
    have H : ilt = ilt', by apply is_prop.elim, cases H,
    have H' : is_prop.elim (lt_add_of_lt_right ilt 1) (lt_add_of_lt_right ilt 1) = idp,
      by apply is_prop.elim,
    krewrite H' },
  { intro a, exact absurd ilt a },
end

@[hott] def elim_succ_maxi_cases_maxi {C : fin (nat.succ n) → Type _}
  {Cls : Π j : fin n, C (lift_succ j)} {Cm : C maxi} :
  succ_maxi_cases Cls Cm maxi = Cm :=
begin
  esimp[succ_maxi_cases, maxi],
  apply decidable.rec,
  { intro a, apply absurd a !nat.lt_irrefl },
  { intro a, esimp[val_inj], apply concat,
    have H : (le.antisymm (le_of_lt_succ (lt_succ_self n)) (le_of_not_gt a))⁻¹ = idp,
      by apply is_prop.elim,
    apply ap _ H, krewrite eq_of_veq_refl },
end

@[hott] def foldr {A B : Type _} (m : A → B → B) (b : B) : Π {n : nat}, (fin n → A) → B :=
  nat.rec (λ f, b) (λ n IH f, m (f (fin.zero n)) (IH (λ i : fin n, f (succ i))))

@[hott] def foldl {A B : Type _} (m : B → A → B) (b : B) : Π {n : nat}, (fin n → A) → B :=
  nat.rec (λ f, b) (λ n IH f, m (IH (λ i : fin n, f (lift_succ i))) (f maxi))

@[hott] theorem choice {C : fin n → Type _} :
  (Π i : fin n, nonempty (C i)) → nonempty (Π i : fin n, C i) :=
begin
  revert C,
  induction n with [n, IH],
  { intros C H,
    apply nonempty.intro,
    exact elim0 },
  { intros C H,
    fapply nonempty.elim (H (fin.zero n)),
    intro CO,
    fapply nonempty.elim (IH (λ i, C (succ i)) (λ i, H (succ i))),
    intro CS,
    apply nonempty.intro,
    exact zero_succ_cases CO CS }
end

/-section
open list
local postfix `+1`:100 := nat.succ

@[hott] lemma dmap_map_lift {n : nat} : Π l : list nat, (Π i, i ∈ l → i < n) → dmap (λ i, i < n +1) mk l = map lift_succ (dmap (λ i, i < n) mk l)
| []     := assume Plt, rfl
| (i::l) := assume Plt, begin
  rewrite [@dmap_cons_of_pos _ _ (λ i, i < n +1) _ _ _ (lt_succ_of_lt (Plt i !mem_cons)), @dmap_cons_of_pos _ _ (λ i, i < n) _ _ _ (Plt i !mem_cons), map_cons],
  congruence,
  apply dmap_map_lift,
  intros j Pjinl, apply Plt, apply mem_cons_of_mem, assumption end

@[hott] lemma upto_succ (n : nat) : upto (n +1) = maxi :: map lift_succ (upto n) :=
begin
  rewrite [↑fin.upto, list.upto_succ, @dmap_cons_of_pos _ _ (λ i, i < n +1) _ _ _ (nat.self_lt_succ n)],
  congruence,
  apply dmap_map_lift, apply @list.lt_of_mem_upto
end

@[hott] def upto_step : Π {n : nat}, fin.upto (n +1) = (map succ (upto n))++[0]
| 0      := rfl
| (i +1) := begin rewrite [upto_succ i, map_cons, append_cons, succ_max, upto_succ, -lift_zero],
  congruence, rewrite [map_map, -lift_succ.comm, -map_map, -(map_singleton _ 0), -map_append, -upto_step] end
end-/

open sum equiv decidable

@[hott] def fin_zero_equiv_empty : fin 0 ≃ empty :=
begin
  fapply equiv.MK, rotate 1, do 2 (intro x; contradiction),
  rotate 1, do 2 (intro x; apply elim0 x)
end

@[hott] def is_contr_fin_one [instance] : is_contr (fin 1) :=
begin
  fapply is_contr.mk, exact 0,
  intro x, induction x with v vlt,
  apply eq_of_veq, rewrite val_zero,
  apply inverse, apply eq_zero_of_le_zero, apply le_of_succ_le_succ, exact vlt,
end

@[hott] def fin_sum_equiv (n m : nat) : (fin n + fin m) ≃ fin (n+m) :=
begin
  fapply equiv.MK,
  { intro s, induction s with l r,
    induction l with v vlt, apply mk v, apply lt_add_of_lt_right, exact vlt,
    induction r with v vlt, apply mk (v + n), rewrite {n + m}add.comm,
    apply add_lt_add_of_lt_of_le vlt, apply nat.le_refl },
  { intro f, induction f with v vlt,
    exact if h : v < n
          then sum.inl (mk v h)
          else sum.inr (mk (v-n) (nat.sub_lt_of_lt_add vlt (le_of_not_gt h))) },
  { intro f, cases f with v vlt, esimp, apply @by_cases (v < n),
    intro vltn, rewrite [dif_pos vltn], apply eq_of_veq, reflexivity,
    intro nvltn, rewrite [dif_neg nvltn], apply eq_of_veq, esimp,
    apply nat.sub_add_cancel, apply le_of_not_gt, apply nvltn },
  { intro s, cases s with f g,
    cases f with v vlt, rewrite [dif_pos vlt],
    cases g with v vlt, esimp, have ¬ v + n < n, from
      suppose v + n < n,
      have v < n - n, from nat.lt_sub_of_add_lt this !le.refl,
      have v < 0, by rewrite [nat.sub_self at this]; exact this,
      absurd this !not_lt_zero,
    apply concat, apply dif_neg this, apply ap inr, apply eq_of_veq, esimp,
    apply nat.add_sub_cancel },
end

@[hott] def fin_succ_equiv (n : nat) : fin (n + 1) ≃ fin n + unit :=
begin
  fapply equiv.MK,
  { apply succ_maxi_cases, esimp, apply inl, apply inr unit.star },
  { intro d, cases d, apply lift_succ a, apply maxi },
  { intro d, cases d,
    cases a with a alt, esimp, apply elim_succ_maxi_cases_lift_succ,
    cases a, apply elim_succ_maxi_cases_maxi },
  { intro a, apply succ_maxi_cases, esimp,
    intro j, krewrite elim_succ_maxi_cases_lift_succ,
    krewrite elim_succ_maxi_cases_maxi },
end

open prod

@[hott] def fin_prod_equiv (n m : nat) : (fin n × fin m) ≃ fin (n*m) :=
begin
  induction n,
  { krewrite nat.zero_mul,
    calc fin 0 × fin m ≃ empty × fin m : fin_zero_equiv_empty
                   ... ≃ fin m × empty : prod_comm_equiv
                   ... ≃ empty : prod_empty_equiv
                   ... ≃ fin 0 : fin_zero_equiv_empty },
  { have H : (a + 1) * m = a * m + m, by rewrite [nat.right_distrib, one_mul],
    calc fin (a + 1) × fin m
         ≃ (fin a + unit) × fin m : prod.prod_equiv_prod_right !fin_succ_equiv
     ... ≃ (fin a × fin m) + (unit × fin m) : sum_prod_right_distrib
     ... ≃ (fin a × fin m) + (fin m × unit) : prod_comm_equiv
     ... ≃ fin (a * m) + (fin m × unit) : v_0
     ... ≃ fin (a * m) + fin m : prod_unit_equiv
     ... ≃ fin (a * m + m) : fin_sum_equiv
     ... ≃ fin ((a + 1) * m) : equiv_of_eq (ap fin H⁻¹) },
end

@[hott] def fin_two_equiv_bool : fin 2 ≃ bool :=
let H := equiv_unit_of_is_contr (fin 1) in
calc
  fin 2 ≃ fin (1 + 1)   : equiv.refl
   ...  ≃ fin 1 + fin 1 : fin_sum_equiv
   ...  ≃ unit + unit   : H
   ...  ≃ bool          : bool_equiv_unit_sum_unit

@[hott] def fin_sum_unit_equiv (n : nat) : fin n + unit ≃ fin (nat.succ n) :=
let H := equiv_unit_of_is_contr (fin 1) in
calc
  fin n + unit ≃ fin n + fin 1 : H
          ...  ≃ fin (nat.succ n)     : fin_sum_equiv

@[hott] def fin_sum_equiv_cancel {n : nat} {A B : Type _} (H : (fin n) + A ≃ (fin n) + B) :
  A ≃ B :=
begin
  induction n with n IH,
  { calc A ≃ A + empty : sum_empty_equiv
       ... ≃ empty + A : sum_comm_equiv
       ... ≃ fin 0 + A : fin_zero_equiv_empty
       ... ≃ fin 0 + B : H
       ... ≃ empty + B : fin_zero_equiv_empty
       ... ≃ B + empty : sum_comm_equiv
       ... ≃ B : sum_empty_equiv },
  { apply IH, apply unit_sum_equiv_cancel,
    calc unit + (fin n + A) ≃ (unit + fin n) + A : sum_assoc_equiv
                        ... ≃ (fin n + unit) + A : sum_comm_equiv
                        ... ≃ fin (nat.succ n) + A : fin_sum_unit_equiv
                        ... ≃ fin (nat.succ n) + B : H
                        ... ≃ (fin n + unit) + B : fin_sum_unit_equiv
                        ... ≃ (unit + fin n) + B : sum_comm_equiv
                        ... ≃ unit + (fin n + B) : sum_assoc_equiv },
end


@[hott] def eq_of_fin_equiv {m n : nat} (H :fin m ≃ fin n) : m = n :=
begin
  revert n H, induction m with m IH IH,
  { intros n H, cases n, reflexivity, exfalso,
    apply to_fun fin_zero_equiv_empty, apply to_inv H, apply fin.zero },
  { intros n H, cases n with n, exfalso,
    apply to_fun fin_zero_equiv_empty, apply to_fun H, apply fin.zero,
    have unit + fin m ≃ unit + fin n, from
    calc unit + fin m ≃ fin m + unit : sum_comm_equiv
                  ... ≃ fin (nat.succ m) : fin_succ_equiv
                  ... ≃ fin (nat.succ n) : H
                  ... ≃ fin n + unit : fin_succ_equiv
                  ... ≃ unit + fin n : sum_comm_equiv,
    have fin m ≃ fin n, from unit_sum_equiv_cancel this,
    apply ap nat.succ, apply IH _ this },
end

  @[hott] def cyclic_succ {n : ℕ} (x : fin n) : fin n :=
  begin
    cases n with n,
    { exfalso, apply not_lt_zero _ (is_lt x)},
    { exact
      if H : val x = n
        then fin.mk 0 !zero_lt_succ
        else fin.mk (nat.succ (val x))
               (succ_lt_succ (lt_of_le_of_ne (le_of_lt_succ (is_lt x)) H))}
  end

  @[hott] def cyclic_pred {n : ℕ} (x : fin n) : fin n :=
  begin
    cases n with n,
    { exfalso, apply not_lt_zero _ (is_lt x)},
    { cases x with m H, cases m with m,
      { exact fin.mk n (self_lt_succ n) },
      { exact fin.mk m (lt.trans (self_lt_succ m) H) }}
  end

  /-
    We want to say that fin (succ n) always has a 0 and 1. However, we want a bit more, because
    sometimes we want a zero of (fin a) where a is either
    - equal to a successor, but not definitionally a successor (e.g. (0 : fin (3 + n)))
    - definitionally equal to a successor, but not in a way that type class inference can infer.
      (e.g. (0 : fin 4). Note that 4 is bit0 (bit0 one), but (bit0 x) (defined as x + x),
        is not always a successor)
    To solve this we use an auxillary class `is_succ` which can solve whether a number is a
    successor.
  -/

  /- this is a version of `madd` which might compute better -/
  protected @[hott] def add {n : ℕ} (x y : fin n) : fin n :=
  iterate cyclic_succ (val y) x

  @[hott] def has_zero_fin [instance] (n : ℕ) [H : is_succ n] : has_zero (fin n) :=
  by induction H with n; exact has_zero.mk (fin.zero n)

  @[hott] def has_one_fin [instance] (n : ℕ) [H : is_succ n] : has_one (fin n) :=
  by induction H with n; exact has_one.mk (cyclic_succ (fin.zero n))

  @[hott] def has_add_fin [instance] (n : ℕ) : has_add (fin n) :=
  has_add.mk fin.add

end fin
