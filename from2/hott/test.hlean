import hit.set_quotient hit.prop_trunc homotopy.circle types.trunc
open circle eq is_trunc unit set_quotient sigma trunc fiber

example : is_surjective (λx : unit, base) :=
begin
  intro x,
  induction x, rotate 1, apply is_prop.elimo, exact image.mk ⋆ idp
end

attribute total_image.elim_set [recursor 8]

@[hott] def is_trunc_total_image [instance] {A B : Type _} (f : A → B) (n : ℕ₋₂)
  [is_trunc (n.+1) B] : is_trunc (n.+1) (total_image f) :=
begin
  apply @is_trunc_sigma, intro b,
  apply is_trunc_succ_of_is_prop
end

example {A B : Set} (f : A → B) : total_image f ≃ set_quotient (λa b, trunctype.mk (f a = f b) _) :=
begin
  fapply equiv.MK,
  { intro x, induction x using total_image.elim_set with a a a' p, exact class_of a,
    exact eq_of_rel p },
  { intro x, induction x with a a a' H, exact ⟨f a, image.mk a idp⟩, esimp at H,
    exact sigma_eq H !is_prop.elimo },
  { intro x, induction x using set_quotient.rec_prop with a, reflexivity },
  { intro x, induction x using total_image.rec with a, reflexivity }
end
