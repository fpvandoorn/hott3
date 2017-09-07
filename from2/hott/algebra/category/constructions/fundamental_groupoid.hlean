/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn
-/

import ..groupoid ..functor.basic

open eq is_trunc iso trunc functor

namespace category

  @[hott] def fundamental_precategory (A : Type _) : Precategory :=
  precategory.MK A
                 (λa a', trunc 0 (a = a'))
                 _
                 (λa₁ a₂ a₃ q p, tconcat p q)
                 (λa, tidp)
                 (λa₁ a₂ a₃ a₄ r q p, tassoc p q r)
                 (λa₁ a₂, tcon_tidp)
                 (λa₁ a₂, tidp_tcon)

  @[hott] def fundamental_groupoid (A : Type _) : Groupoid :=
  groupoid.MK (fundamental_precategory A)
              (λa b p, is_iso.mk (tinverse p) (right_tinv p) (left_tinv p))

  @[hott] def fundamental_groupoid_functor {A B : Type _} (f : A → B) :
    fundamental_groupoid A ⇒ fundamental_groupoid B :=
  functor.mk f (λa a', tap f) (λa, tap_tidp f) (λa₁ a₂ a₃ q p, tap_tcon f p q)

  notation `Π₁` := fundamental_groupoid

  notation `Π₁⇒` := fundamental_groupoid_functor

end category
