/-
Copyright (c) 2017 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Floris van Doorn

Modalities

-/

import .init .tactic.instantiate_axioms
universes u v w u₁ u₂ u₃ u₄ 
hott_theory
namespace hott
variables {A : Type u} {B : Type v} 

structure extension_along (f : A → B) (P : B → Type w) (d : Πa, P (f a)) : Type (max u v w) :=
  (s : Πb, P b)
  (s_eq : Πa, s (f a) = d a)

@[hott] def extendable_along  : ℕ → (A → B) → (B → Type w) → Type (max u v w)
| 0     f C := ulift unit
| (n+1) f C := (Π(g : Πa, C (f a)), extension_along f C g) × (Π(h k : Πb, C b), extendable_along n f (λb, h b = k b))

@[hott] def inf_extendable_along {A : Type u} {B : Type v} (f : A → B) (C : B → Type w) : Type (max u v w) :=
Π(n : ℕ), extendable_along n f C

namespace reflective_subuniverse

constant O : Type u → Type u
constant is_modal : Type u → Type u
constant is_modal_O (A : Type u) : is_modal (O A)
constant eta : Π(A : Type u), A → O A
constant is_modal_equiv_closed {A : Type u} {B : Type v} (H : is_modal A) (f : A → B) (H : is_equiv f) : is_modal B
constant is_prop_is_modal (A : Type u) : is_prop (is_modal A)
attribute [instance] is_prop_is_modal
/- This is an equivalent way of stating that - ∘ η : (I A → B) → (A → B) is an equivalence, which is nicer when function extensionality is not available (or to avoid funext-redexes)-/
constant is_extendable_eta {A : Type u} {B : Type v} (H : is_modal B) : inf_extendable_along (eta A) (λx, B)

@[reducible] def η {A : Type u} : A → O A := eta A

def Type_O := ΣA, is_modal A
instance : has_coe_to_sort Type_O :=
{S := Type u, coe := sigma.fst}



end reflective_subuniverse


namespace modality

constant I : Type u → Type u
constant eta : Π(A : Type u), A → I A

@[hott] def is_modal (A : Type u) : Type u := is_equiv (eta A)

@[hott] def eta_inv {A : Type u} (H : is_modal A) : I A → A := @is_equiv.inv _ _ (eta A) H

end modality 

namespace prop_trunc
open trunc

def I : Type u → Type u := trunc (-1)
def eta : Π(A : Type u), A → I A := @tr (-1)

end prop_trunc
end hott
