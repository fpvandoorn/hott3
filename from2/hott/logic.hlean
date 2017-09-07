/-
Copyright (c) Jakob von Raumer. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jakob von Raumer

Logic lemmas we don't want/need in the prelude.
-/
import types.pi

open eq is_trunc decidable

@[hott] theorem dif_pos {c : Type _} [H : decidable c] [P : is_prop c] (Hc : c)
  {A : Type _} {t : c → A} {e : ¬ c → A} : dite c t e = t Hc :=
by induction H with Hc Hnc; apply ap t; apply is_prop.elim; apply absurd Hc Hnc

@[hott] theorem dif_neg {c : Type _} [H : decidable c] (Hnc : ¬c)
  {A : Type _} {t : c → A} {e : ¬ c → A} : dite c t e = e Hnc :=
by induction H with Hc Hnc; apply absurd Hc Hnc; apply ap e; apply is_prop.elim
