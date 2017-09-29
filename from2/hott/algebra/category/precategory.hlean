/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn
-/
import types.trunc types.pi arity

open eq is_trunc pi equiv

namespace category

/-
  Just as in Coq-HoTT we add two redundant fields to precategories: assoc' and id_id.
  The first is to make (Cᵒᵖ)ᵒᵖ = C definitionally when C is a constructor.
  The second is to ensure that the functor from the terminal category 1 ⇒ Cᵒᵖ is
    opposite to the functor 1 ⇒ C.
-/

  structure precategory [class] (ob : Type _) : Type _ :=
  mk' ::
    (hom : ob → ob → Type _)
    (comp : Π⦃a b c : ob⦄, hom b c → hom a b → hom a c)
    (ID : Π (a : ob), hom a a)
    (assoc  : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
       comp h (comp g f) = comp (comp h g) f)
    (assoc' : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
       comp (comp h g) f = comp h (comp g f))
    (id_left : Π ⦃a b : ob⦄ (f : hom a b), comp !ID f = f)
    (id_right : Π ⦃a b : ob⦄ (f : hom a b), comp f !ID = f)
    (id_id : Π (a : ob), comp !ID !ID = ID a)
    (is_set_hom : Π(a b : ob), is_set (hom a b))

  attribute precategory.is_set_hom [instance]

  infixr ∘ := precategory.comp
  -- input ⟶ using \--> (this is a different arrow than \-> (→))
  infixl [parsing_only] ` ⟶ `:60 := precategory.hom
  namespace hom
    infixl ` ⟶ `:60 := precategory.hom -- if you open this namespace, hom a b is printed as a ⟶ b
  end hom

  abbreviation hom         := @precategory.hom
  abbreviation comp        := @precategory.comp
  abbreviation ID          := @precategory.ID
  abbreviation assoc       := @precategory.assoc
  abbreviation assoc'      := @precategory.assoc'
  abbreviation id_left     := @precategory.id_left
  abbreviation id_right    := @precategory.id_right
  abbreviation id_id       := @precategory.id_id
  abbreviation is_set_hom := @precategory.is_set_hom

  @[hott] def is_prop_hom_eq {ob : Type _} [C : precategory ob] {x y : ob} (f g : x ⟶ y)
    : is_prop (f = g) :=
  _

  -- the constructor you want to use in practice
  @[hott] protected def precategory.mk {ob : Type _} (hom : ob → ob → Type _)
    [set : Π (a b : ob), is_set (hom a b)]
    (comp : Π ⦃a b c : ob⦄, hom b c → hom a b → hom a c) (ID : Π (a : ob), hom a a)
    (ass : Π ⦃a b c d : ob⦄ (h : hom c d) (g : hom b c) (f : hom a b),
       comp h (comp g f) = comp (comp h g) f)
    (idl : Π ⦃a b : ob⦄ (f : hom a b), comp (ID b) f = f)
    (idr : Π ⦃a b : ob⦄ (f : hom a b), comp f (ID a) = f) : precategory ob :=
  precategory.mk' hom comp ID ass (λa b c d h g f, !ass⁻¹) idl idr (λa, !idl) set

  section basic_lemmas
    variables {ob : Type _} [C : precategory ob]
    variables {a b c d : ob} {h : c ⟶ d} {g g' : hom b c} {f f' : hom a b} {i : a ⟶ a}
    include C

    @[hott] def id [reducible] := ID a

    @[hott] def id_leftright       (f : hom a b) : id ∘ f ∘ id = f := !id_left ⬝ !id_right
    @[hott] def comp_id_eq_id_comp (f : hom a b) : f ∘ id = id ∘ f := !id_right ⬝ !id_left⁻¹
    @[hott] def id_comp_eq_comp_id (f : hom a b) : id ∘ f = f ∘ id := !id_left ⬝ !id_right⁻¹

    @[hott] def hom_whisker_left (g : b ⟶ c) (p : f = f') : g ∘ f = g ∘ f' :=
    ap (λx, g ∘ x) p

    @[hott] def hom_whisker_right (g : c ⟶ a) (p : f = f') : f ∘ g = f' ∘ g :=
    ap (λx, x ∘ g) p

    /- many variants of hom_pathover are defined in .iso and .functor.basic -/

    @[hott] def left_id_unique (H : Π{b} {f : hom b a}, i ∘ f = f) : i = id :=
    calc i = i ∘ id : by rewrite id_right
       ... = id     : by rewrite H

    @[hott] def right_id_unique (H : Π{b} {f : hom a b}, f ∘ i = f) : i = id :=
    calc i = id ∘ i : by rewrite id_left
       ... = id     : by rewrite H

    @[hott] def homset [reducible] (x y : ob) : Set :=
    Set.mk (hom x y) _

    @[hott] def comp2 (p : g = g') (q : f = f') : g ∘ f = g' ∘ f' :=
    ap011 (λg f, comp g f) p q

    infix ` ∘2 `:79 := comp2
  end basic_lemmas
  section squares
    parameters {ob : Type _} [C : precategory ob]
    local infixl ` ⟶ `:25 := @precategory.hom ob C
    local infixr ∘    := @precategory.comp ob C _ _ _
    @[hott] def compose_squares {xa xb xc ya yb yc : ob}
      {xg : xb ⟶ xc} {xf : xa ⟶ xb} {yg : yb ⟶ yc} {yf : ya ⟶ yb}
      {wa : xa ⟶ ya} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (xyab : wb ∘ xf = yf ∘ wa) (xybc : wc ∘ xg = yg ∘ wb)
        : wc ∘ (xg ∘ xf) = (yg ∘ yf) ∘ wa :=
    calc
      wc ∘ (xg ∘ xf) = (wc ∘ xg) ∘ xf : by rewrite assoc
        ... = (yg ∘ wb) ∘ xf : by rewrite xybc
        ... = yg ∘ (wb ∘ xf) : by rewrite assoc
        ... = yg ∘ (yf ∘ wa) : by rewrite xyab
        ... = (yg ∘ yf) ∘ wa : by rewrite assoc

    @[hott] def compose_squares_2x2 {xa xb xc ya yb yc za zb zc : ob}
      {xg : xb ⟶ xc} {xf : xa ⟶ xb} {yg : yb ⟶ yc} {yf : ya ⟶ yb} {zg : zb ⟶ zc} {zf : za ⟶ zb}
      {va : ya ⟶ za} {vb : yb ⟶ zb} {vc : yc ⟶ zc} {wa : xa ⟶ ya} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (xyab : wb ∘ xf = yf ∘ wa) (xybc : wc ∘ xg = yg ∘ wb)
      (yzab : vb ∘ yf = zf ∘ va) (yzbc : vc ∘ yg = zg ∘ vb)
        : (vc ∘ wc) ∘ (xg ∘ xf) = (zg ∘ zf) ∘ (va ∘ wa) :=
    calc
      (vc ∘ wc) ∘ (xg ∘ xf) = vc ∘ (wc ∘ (xg ∘ xf)) : by rewrite (assoc vc wc _)
        ... = vc ∘ ((yg ∘ yf) ∘ wa) : by rewrite (compose_squares xyab xybc)
        ... = (vc ∘ (yg ∘ yf)) ∘ wa : by rewrite assoc
        ... = ((zg ∘ zf) ∘ va) ∘ wa : by rewrite (compose_squares yzab yzbc)
        ... = (zg ∘ zf) ∘ (va ∘ wa) : by rewrite assoc

    @[hott] def square_precompose {xa xb xc yb yc : ob}
      {xg : xb ⟶ xc} {yg : yb ⟶ yc} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (H : wc ∘ xg = yg ∘ wb) (xf : xa ⟶ xb) : wc ∘ xg ∘ xf = yg ∘ wb ∘ xf :=
    calc
      wc ∘ xg ∘ xf = (wc ∘ xg) ∘ xf : by rewrite assoc
        ... = (yg ∘ wb) ∘ xf        : by rewrite H
        ... = yg ∘ wb ∘ xf          : by rewrite assoc

    @[hott] def square_postcompose {xb xc yb yc yd : ob}
      {xg : xb ⟶ xc} {yg : yb ⟶ yc} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (H : wc ∘ xg = yg ∘ wb) (yh : yc ⟶ yd) : (yh ∘ wc) ∘ xg = (yh ∘ yg) ∘ wb :=
    calc
      (yh ∘ wc) ∘ xg = yh ∘ wc ∘ xg : by rewrite assoc
        ... = yh ∘ yg ∘ wb          : by rewrite H
        ... = (yh ∘ yg) ∘ wb        : by rewrite assoc

    @[hott] def square_prepostcompose {xa xb xc yb yc yd : ob}
      {xg : xb ⟶ xc} {yg : yb ⟶ yc} {wb : xb ⟶ yb} {wc : xc ⟶ yc}
      (H : wc ∘ xg = yg ∘ wb) (yh : yc ⟶ yd) (xf : xa ⟶ xb)
        : (yh ∘ wc) ∘ (xg ∘ xf) = (yh ∘ yg) ∘ (wb ∘ xf)  :=
    square_precompose (square_postcompose H yh) xf

  end squares

  structure Precategory : Type _ :=
    (carrier : Type _)
    (struct : precategory carrier)

  @[hott] def precategory.Mk [reducible] {ob} (C) : Precategory := Precategory.mk ob C
  @[hott] def precategory.MK [reducible] (a b c d e f g h) : Precategory :=
  Precategory.mk a (@precategory.mk a b c d e f g h)

  abbreviation carrier := @Precategory.carrier

  attribute Precategory.carrier [coercion]
  attribute Precategory.struct [instance] [priority 10000] [coercion]
  -- @[hott] def precategory.carrier [coercion] [reducible] := Precategory.carrier
  -- @[hott] def precategory.struct [instance] [coercion] := Precategory.struct
  notation g ` ∘[`:60 C:0 `] `:0 f:60 :=
  @comp (Precategory.carrier C) (Precategory.struct C) _ _ _ g f
  -- TODO: make this left associative

  @[hott] def Precategory.eta (C : Precategory) : Precategory.mk C C = C :=
  Precategory.rec (λob c, idp) C

  /-Characterization of paths between precategories-/
  -- introduction tule for paths between precategories

  @[hott] def precategory_eq {ob : Type _}
    {C D : precategory ob}
    (p : Π{a b}, @hom ob C a b = @hom ob D a b)
    (q : Πa b c g f, cast p (@comp ob C a b c g f) = @comp ob D a b c (cast p g) (cast p f))
      : C = D :=
  begin
    induction C with hom1 c1 ID1 a b il ir, induction D with hom2 c2 ID2 a' b' il' ir',
    esimp at *,
    revert q, eapply homotopy2.rec_on @p, esimp, clear p, intros p q, induction p,
    esimp at *,
    have H : c1 = c2,
    begin apply eq_of_homotopy3, intros, apply eq_of_homotopy2, intros, apply q end,
    induction H,
    have K : ID1 = ID2,
    begin apply eq_of_homotopy, intro a, exact !ir'⁻¹ ⬝ !il end,
    induction K,
    apply ap0111111 (precategory.mk' hom1 c1 ID1): apply is_prop.elim
  end


  @[hott] def precategory_eq_of_equiv {ob : Type _}
    {C D : precategory ob}
    (p : Π⦃a b⦄, @hom ob C a b ≃ @hom ob D a b)
    (q : Π{a b c} g f, p (@comp ob C a b c g f) = @comp ob D a b c (p g) (p f))
      : C = D :=
  begin
    fapply precategory_eq,
    { intros a b, exact ua !@p},
    { intros, refine !cast_ua ⬝ !q ⬝ _, apply ap011 !@comp !cast_ua⁻¹ !cast_ua⁻¹},
  end

/- if we need to prove properties about precategory_eq, it might be easier with the following proof:
  begin
    induction C with hom1 comp1 ID1, induction D with hom2 comp2 ID2, esimp at *,
    have H : Σ(s : hom1 = hom2), (λa b, equiv_of_eq (apd100 s a b)) = p,
    begin
      fconstructor,
      { apply eq_of_homotopy2, intros, apply ua, apply p},
      { apply eq_of_homotopy2, intros, rewrite [to_right_inv !eq_equiv_homotopy2, equiv_of_eq_ua]}
    end,
    induction H with H1 H2, induction H1, esimp at H2,
    have K : (λa b, equiv.refl) = p,
    begin refine _ ⬝ H2, apply eq_of_homotopy2, intros, exact !equiv_of_eq_refl⁻¹ end,
    induction K, clear H2,
    esimp at *,
    have H : comp1 = comp2,
    begin apply eq_of_homotopy3, intros, apply eq_of_homotopy2, intros, apply q end,
    have K : ID1 = ID2,
    begin apply eq_of_homotopy, intros, apply r end,
    induction H, induction K,
    apply ap0111111 (precategory.mk' hom1 comp1 ID1): apply is_prop.elim
  end
-/

  @[hott] def Precategory_eq {C D : Precategory}
    (p : carrier C = carrier D)
    (q : Π{a b : C}, a ⟶ b = cast p a ⟶ cast p b)
    (r : Π{a b c : C} (g : b ⟶ c) (f : a ⟶ b), cast q (g ∘ f) = cast q g ∘ cast q f)
       : C = D :=
  begin
    induction C with X C, induction D with Y D, esimp at *, induction p,
    esimp at *,
    apply ap (Precategory.mk X),
    apply precategory_eq @q @r
  end

  @[hott] def Precategory_eq_of_equiv {C D : Precategory}
    (p : carrier C ≃ carrier D)
    (q : Π⦃a b : C⦄, a ⟶ b ≃ p a ⟶ p b)
    (r : Π{a b c : C} (g : b ⟶ c) (f : a ⟶ b), q (g ∘ f) = q g ∘ q f)
       : C = D :=
  begin
    induction C with X C, induction D with Y D, esimp at *,
    revert q r, eapply equiv.rec_on_ua p, clear p, intro p, induction p, esimp,
    intros,
    apply ap (Precategory.mk X),
    apply precategory_eq_of_equiv @q @r
  end

  -- elimination rules for paths between precategories.
  -- The first elimination rule is "ap carrier"

  @[hott] def Precategory_eq_hom {C D : Precategory} (p : C = D) (a b : C)
    : hom a b = hom (cast (ap carrier p) a) (cast (ap carrier p) b) :=
  by induction p; reflexivity
  --(ap10 (ap10 (apdt (λx, @hom (carrier x) (Precategory.struct x)) p⁻¹ᵖ) a) b)⁻¹ᵖ ⬝ _


  -- beta/eta rules
  @[hott] def ap_Precategory_eq' {C D : Precategory}
    (p : carrier C = carrier D)
    (q : Π{a b : C}, a ⟶ b = cast p a ⟶ cast p b)
    (r : Π{a b c : C} (g : b ⟶ c) (f : a ⟶ b), cast q (g ∘ f) = cast q g ∘ cast q f)
    (s : Πa, cast q (ID a) = ID (cast p a)) : ap carrier (Precategory_eq p @q @r) = p :=
  begin
    induction C with X C, induction D with Y D, esimp at *, induction p,
    rewrite [↑Precategory_eq, -ap_compose,↑function.compose,ap_constant]
  end

  /-
  @[hott] theorem Precategory_eq'_eta {C D : Precategory} (p : C = D) :
    Precategory_eq
      (ap carrier p)
      (Precategory_eq_hom p)
      (by induction p; intros; reflexivity) = p :=
  begin
    induction p, induction C with X C, unfold Precategory_eq,
    induction C, unfold precategory_eq, exact sorry
  end
  -/

/-
  @[hott] theorem Precategory_eq2 {C D : Precategory} (p q : C = D)
    (r : ap carrier p = ap carrier q)
    (s : Precategory_eq_hom p =[r] Precategory_eq_hom q)
      : p = q :=
  begin

  end
-/

end category
