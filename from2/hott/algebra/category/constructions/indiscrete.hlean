/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.

Authors: Floris van Doorn

Indiscrete category
-/

import .opposite

open functor is_trunc unit eq

namespace category

  variable (X : Type _)

  @[hott] def indiscrete_precategory : precategory X :=
  precategory.mk (λx y, unit)
                 (λx y z f g, star)
                 (λx, star)
                 (λx y z w f g h, idp)
                 (λx y f, by induction f; reflexivity)
                 (λx y f, by induction f; reflexivity)

  @[hott] def Indiscrete_precategory : Precategory :=
  precategory.Mk (indiscrete_precategory X)

  @[hott] def indiscrete_op : (Indiscrete_precategory X)ᵒᵖ = Indiscrete_precategory X := idp

end category
