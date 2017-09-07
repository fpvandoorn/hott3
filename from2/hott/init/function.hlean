/-
Copyright (c) 2014 Microsoft Corporation. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Author: Leonardo de Moura

General operations on functions.
-/

prelude
import init.reserved_notation .types

open prod

namespace function

variables {A B C D E : Type _}

@[hott] def compose [reducible] (f : B → C) (g : A → B) : A → C :=
λx, f (g x)

@[hott] def compose_right [reducible] (f : B → B → B) (g : A → B) : B → A → B :=
λ b a, f b (g a)

@[hott] def compose_left [reducible] (f : B → B → B) (g : A → B) : A → B → B :=
λ a b, f (g a) b

@[hott] def on_fun [reducible] (f : B → B → C) (g : A → B) : A → A → C :=
λx y, f (g x) (g y)

@[hott] def combine [reducible] (f : A → B → C) (op : C → D → E) (g : A → B → D)
  : A → B → E :=
λx y, op (f x y) (g x y)

@[hott] def const [reducible] (B : Type _) (a : A) : B → A :=
λx, a

@[hott] def dcompose [reducible] {B : A → Type _} {C : Π {x : A}, B x → Type _}
  (f : Π {x : A} (y : B x), C y) (g : Πx, B x) : Πx, C (g x) :=
λx, f (g x)

@[hott] def flip [reducible] {C : A → B → Type _} (f : Πx y, C x y) : Πy x, C x y :=
λy x, f x y

@[hott] def app [reducible] {B : A → Type _} (f : Πx, B x) (x : A) : B x :=
f x

@[hott] def curry [reducible] : (A × B → C) → A → B → C :=
λ f a b, f (a, b)

@[hott] def uncurry [reducible] : (A → B → C) → (A × B → C) :=
λ f p, match p with (a, b) := f a b end


infixr  ` ∘ `            := compose
infixr  ` ∘' `:60        := dcompose
infixl  ` on `:1         := on_fun
infixr  ` $ `:1          := app
notation f ` -[` op `]- ` g  := combine f op g

end function

-- copy reducible annotations to top-level
export [reducible] function
