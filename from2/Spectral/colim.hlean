-- authors: Floris van Doorn, Egbert Rijke, Stefano Piceghello

import hit.colimit types.fin homotopy.chain_complex types.pointed2
open seq_colim pointed algebra eq is_trunc nat is_equiv equiv sigma sigma.ops chain_complex

namespace seq_colim

  @[hott] def pseq_colim {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) : Type* :=
  pointed.MK (seq_colim f) (@sι _ _ 0 pt)

  @[hott] def inclusion_pt {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) (n : ℕ)
    : inclusion f (Point (X n)) = Point (pseq_colim f) :=
  begin
    induction n with n p,
      reflexivity,
      exact (ap (sι f) (respect_pt _))⁻¹ᵖ ⬝ (!glue ⬝ p)
  end

  @[hott] def pinclusion {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) (n : ℕ)
    : X n →* pseq_colim f :=
  pmap.mk (inclusion f) (inclusion_pt f n)

  @[hott] def seq_diagram [reducible] (A : ℕ → Type _) : Type _ := Π⦃n⦄, A n → A (succ n)
  @[hott] def pseq_diagram [reducible] (A : ℕ → Type*) : Type _ := Π⦃n⦄, A n →* A (succ n)

  structure Seq_diagram : Type _ :=
    (carrier : ℕ → Type _)
    (struct : seq_diagram carrier)

  @[hott] def is_equiseq [reducible] {A : ℕ → Type _} (f : seq_diagram A) : Type _ :=
  forall (n : ℕ), is_equiv (@f n)

  structure Equi_seq : Type _ :=
    (carrier : ℕ → Type _)
    (maps : seq_diagram carrier)
    (prop : is_equiseq maps)

  protected abbreviation Mk := Seq_diagram.mk
  attribute Seq_diagram.carrier [coercion]
  attribute Seq_diagram.struct [coercion]

  variables {A : ℕ → Type _} (f : seq_diagram A)
  include f

  @[hott] def rep0 [reducible] (k : ℕ) : A 0 → A k :=
  begin
    intro a,
    induction k with k x,
      exact a,
      exact f x
  end

  @[hott] def is_equiv_rep0 [H : is_equiseq f] (k : ℕ) :
    is_equiv (rep0 f k) :=
  begin
    induction k with k IH,
    { apply is_equiv_id},
    { apply is_equiv_compose (@f _) (rep0 f k)},
  end

  local attribute is_equiv_rep0 [instance]
  @[hott] def rep0_back [reducible] [H : is_equiseq f] (k : ℕ) : A k → A 0 :=
  (rep0 f k)⁻¹

  section generalized_rep
  variable {n : ℕ}

  @[hott] def rep [reducible] (k : ℕ) (a : A n) : A (n + k) :=
  by induction k with k x; exact a; exact f x

  @[hott] def rep_f (k : ℕ) (a : A n) : pathover A (rep f k (f a)) (succ_add n k) (rep f (succ k) a) :=
  begin
    induction k with k IH,
    { constructor},
    { apply pathover_ap, exact apo f IH}
  end

  @[hott] def rep_back [H : is_equiseq f] (k : ℕ) (a : A (n + k)) : A n :=
  begin
    induction k with k g,
    exact a,
    exact g ((@f (n + k))⁻¹ a),
  end

  @[hott] def is_equiv_rep [H : is_equiseq f] (k : ℕ) :
    is_equiv (λ (a : A n), rep f k a) :=
  begin
    fapply adjointify,
    { exact rep_back f k},
    { induction k with k IH: intro b,
      { reflexivity},
      unfold rep,
      unfold rep_back,
      fold [rep f k (rep_back f k ((@f (n+k))⁻¹ b))],
      refine ap (@f (n+k)) (IH ((@f (n+k))⁻¹ b)) ⬝ _,
      apply right_inv (@f (n+k))},
    induction k with k IH: intro b,
    exact rfl,
    unfold rep_back,
    unfold rep,
    fold [rep f k b],
    refine _ ⬝ IH b,
    exact ap (rep_back f k) (left_inv (@f (n+k)) (rep f k b))
  end

  @[hott] def rep_rep (k l : ℕ) (a : A n) :
    pathover A (rep f k (rep f l a)) (nat.add_assoc n l k) (rep f (l + k) a) :=
  begin
    induction k with k IH,
    { constructor},
    { apply pathover_ap, exact apo f IH}
  end

  @[hott] def f_rep (k : ℕ) (a : A n) : f (rep f k a) = rep f (succ k) a := idp
  end generalized_rep

  section shift

  @[hott] def shift_diag : seq_diagram (λn, A (succ n)) :=
  λn a, f a

  @[hott] def kshift_diag (k : ℕ) : seq_diagram (λn, A (k + n)) :=
  λn a, f a

  @[hott] def kshift_diag' (k : ℕ) : seq_diagram (λn, A (n + k)) :=
  λn a, transport A (succ_add n k)⁻¹ (f a)
  end shift

  section constructions

    omit f

    @[hott] def constant_seq (X : Type _) : seq_diagram (λ n, X) :=
    λ n x, x

    @[hott] def seq_diagram_arrow_left (X : Type _) : seq_diagram (λn, X → A n) :=
    λn g x, f (g x)

    -- inductive finset : ℕ → Type _ :=
    -- | fin : forall n, finset n → finset (succ n)
    -- | ftop : forall n, finset (succ n)

    @[hott] def seq_diagram_fin : seq_diagram fin :=
    λn, fin.lift_succ

    @[hott] def id0_seq (x y : A 0) : ℕ → Type _ :=
    λ k, rep0 f k x = rep0 f k y

    @[hott] def id0_seq_diagram (x y : A 0) : seq_diagram (id0_seq f x y) :=
    λ (k : ℕ) (p : rep0 f k x = rep0 f k y), ap (@f k) p

    @[hott] def id_seq (n : ℕ) (x y : A n) : ℕ → Type _ :=
    λ k, rep f k x = rep f k y

    @[hott] def id_seq_diagram (n : ℕ) (x y : A n) : seq_diagram (id_seq f n x y) :=
    λ (k : ℕ) (p : rep f k x = rep f k y), ap (@f (n + k)) p

  end constructions

  section over

    variable {A}
    variable (P : Π⦃n⦄, A n → Type _)

    @[hott] def seq_diagram_over : Type _ := Π⦃n⦄ {a : A n}, P a → P (f a)

    variable (g : seq_diagram_over f P)
    variables {f P}

    @[hott] def seq_diagram_of_over {n : ℕ} (a : A n) :
      seq_diagram (λk, P (rep f k a)) :=
    λk p, g p

    @[hott] def seq_diagram_sigma : seq_diagram (λn, Σ(x : A n), P x) :=
    λn v, ⟨f v.1, g v.2⟩

    variables {n : ℕ} (f P)

    @[hott] theorem rep_f_equiv (a : A n) (k : ℕ) :
      P (rep f k (f a)) ≃ P (rep f (succ k) a) :=
    equiv_apd011 P (rep_f f k a)

    @[hott] theorem rep_rep_equiv (a : A n) (k l : ℕ) :
      P (rep f (l + k) a) ≃ P (rep f k (rep f l a)) :=
    (equiv_apd011 P (rep_rep f k l a))⁻¹ᵉ

  end over

  omit f
  -- do we need to generalize this to the case where the bottom sequence consists of equivalences?
  @[hott] def seq_diagram_pi {X : Type _} {A : X → ℕ → Type _} (g : Π⦃x n⦄, A x n → A x (succ n)) :
    seq_diagram (λn, Πx, A x n) :=
  λn f x, g (f x)

  namespace ops
  abbreviation ι  := @inclusion
  abbreviation pι  {A} (f) {n} := @pinclusion A f n
  abbreviation pι'  [parsing_only] := @pinclusion
  abbreviation ι' [parsing_only] {A} (f n) := @inclusion A f n
  end ops
  open seq_colim.ops

  @[hott] def rep0_glue (k : ℕ) (a : A 0) : ι f (rep0 f k a) = ι f a :=
  begin
    induction k with k IH,
    { reflexivity},
    { exact glue f (rep0 f k a) ⬝ IH}
  end

  @[hott] def shift_up (x : seq_colim f) : seq_colim (shift_diag f) :=
  begin
    induction x,
    { exact ι _ (f a)},
    { exact glue _ (f a)}
  end

  @[hott] def shift_down (x : seq_colim (shift_diag f)) : seq_colim f :=
  begin
    induction x,
    { exact ι f a},
    { exact glue f a}
  end

  @[hott] def shift_equiv : seq_colim f ≃ seq_colim (shift_diag f) :=
  equiv.MK (shift_up f)
           (shift_down f)
           abstract begin
             intro x, induction x,
             { esimp, exact glue _ a},
             { apply eq_pathover,
               rewrite [▸*, ap_id, ap_compose (shift_up f) (shift_down f), ↑shift_down,
                        elim_glue],
               apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
           end end
           abstract begin
             intro x, induction x,
             { exact glue _ a},
             { apply eq_pathover,
               rewrite [▸*, ap_id, ap_compose (shift_down f) (shift_up f), ↑shift_up,
                        elim_glue],
               apply square_of_eq, apply whisker_right, exact !elim_glue⁻¹}
           end end

  @[hott] def pshift_equiv {A : ℕ → Type*} (f : Πn, A n →* A (succ n)) :
    pseq_colim f ≃* pseq_colim (λn, f (n+1)) :=
  begin
    fapply pequiv_of_equiv,
    { apply shift_equiv },
    { exact ap (ι _) (respect_pt (f 0)) }
  end

  @[hott] def pshift_equiv_pinclusion {A : ℕ → Type*} (f : Πn, A n →* A (succ n)) (n : ℕ) :
    psquare (pinclusion f n) (pinclusion (λn, f (n+1)) n) (f n) (pshift_equiv f)  :=
  phomotopy.mk homotopy.rfl begin
    refine !idp_con ⬝ _, esimp,
    induction n with n IH,
    { esimp[inclusion_pt], esimp[shift_diag], exact !idp_con⁻¹ },
    { esimp[inclusion_pt], refine !con_inv_cancel_left ⬝ _,
      rewrite ap_con, rewrite ap_con,
      refine _ ⬝ whisker_right _ !con.assoc,
      refine _ ⬝ (con.assoc (_ ⬝ _) _ _)⁻¹,
      xrewrite [-IH],
      esimp[shift_up], rewrite [elim_glue,  ap_inv, -ap_compose'], esimp,
      rewrite [-+con.assoc], apply whisker_right,
      rewrite con.assoc, apply !eq_inv_con_of_con_eq,
      symmetry, exact eq_of_square !natural_square
  }
  end

  section functor
  variable {f}
  variables {A' : ℕ → Type _} {f' : seq_diagram A'}
  variables (g : Π⦃n⦄, A n → A' n) (p : Π⦃n⦄ (a : A n), g (f a) = f' (g a))
  include p

  @[hott] def seq_colim_functor : seq_colim f → seq_colim f' :=
  begin
    intro x, induction x with n a n a,
    { exact ι f' (g a)},
    { exact ap (ι f') (p a) ⬝ glue f' (g a)}
  end

  @[hott] theorem seq_colim_functor_glue {n : ℕ} (a : A n)
    : ap (seq_colim_functor g p) (glue f a) = ap (ι f') (p a) ⬝ glue f' (g a) :=
  !elim_glue

  omit p
  @[hott] def is_equiv_seq_colim_functor [H : Πn, is_equiv (@g n)]
     : is_equiv (seq_colim_functor @g p) :=
  adjointify _ (seq_colim_functor (λn, (@g _)⁻¹) (λn a, inv_commute' g f f' p a))
             abstract begin
               intro x, induction x,
               { esimp, exact ap (ι _) (right_inv (@g _) a)},
               { apply eq_pathover,
                 rewrite [ap_id, ap_compose (seq_colim_functor g p) (seq_colim_functor _ _),
                   seq_colim_functor_glue _ _ a, ap_con, ▸*,
                   seq_colim_functor_glue _ _ ((@g _)⁻¹ a), -ap_compose, ↑[function.compose],
                   ap_compose (ι _) (@g _),ap_inv_commute',+ap_con, con.assoc,
                   +ap_inv, inv_con_cancel_left, con.assoc, -ap_compose],
                 apply whisker_tl, apply move_left_of_top, esimp,
                 apply transpose, apply square_of_pathover, apply apd}
             end end
             abstract begin
               intro x, induction x,
               { esimp, exact ap (ι _) (left_inv (@g _) a)},
               { apply eq_pathover,
                 rewrite [ap_id, ap_compose (seq_colim_functor _ _) (seq_colim_functor _ _),
                   seq_colim_functor_glue _ _ a, ap_con,▸*, seq_colim_functor_glue _ _ (g a),
                   -ap_compose, ↑[function.compose], ap_compose (ι f) (@g _)⁻¹, inv_commute'_fn,
                   +ap_con, con.assoc, con.assoc, +ap_inv, con_inv_cancel_left, -ap_compose],
                 apply whisker_tl, apply move_left_of_top, esimp,
                 apply transpose, apply square_of_pathover, apply apd}
             end end

  @[hott] def seq_colim_equiv (g : Π{n}, A n ≃ A' n)
    (p : Π⦃n⦄ (a : A n), g (f a) = f' (g a)) : seq_colim f ≃ seq_colim f' :=
  equiv.mk _ (is_equiv_seq_colim_functor @g p)

  @[hott] def seq_colim_rec_unc {P : seq_colim f → Type _}
    (v : Σ(Pincl : Π ⦃n : ℕ⦄ (a : A n), P (ι f a)),
                   Π ⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue f a] Pincl a)
    : Π(x : seq_colim f), P x :=
  by induction v with Pincl Pglue; exact seq_colim.rec f Pincl Pglue

  @[hott] def pseq_colim_pequiv' {A A' : ℕ → Type*} {f : Πn, A n →* A (n+1)}
    {f' : Πn, A' n →* A' (n+1)} (g : Πn, A n ≃* A' n)
    (p : Π⦃n⦄, g (n+1) ∘* f n ~ f' n ∘* g n) : pseq_colim @f ≃* pseq_colim @f' :=
  pequiv_of_equiv (seq_colim_equiv g p) (ap (ι _) (respect_pt (g _)))

  @[hott] def pseq_colim_pequiv {A A' : ℕ → Type*} {f : Πn, A n →* A (n+1)}
    {f' : Πn, A' n →* A' (n+1)} (g : Πn, A n ≃* A' n)
    (p : Πn, g (n+1) ∘* f n ~* f' n ∘* g n) : pseq_colim @f ≃* pseq_colim @f' :=
  pseq_colim_pequiv' g (λn, @p n)

  @[hott] def seq_colim_equiv_constant {A : ℕ → Type*} {f f' : Π⦃n⦄, A n → A (n+1)}
    (p : Π⦃n⦄ (a : A n), f a = f' a) : seq_colim f ≃ seq_colim f' :=
  seq_colim_equiv (λn, erfl) p

  @[hott] def pseq_colim_equiv_constant' {A : ℕ → Type*} {f f' : Πn, A n →* A (n+1)}
    (p : Π⦃n⦄, f n ~ f' n) : pseq_colim @f ≃* pseq_colim @f' :=
  pseq_colim_pequiv' (λn, pequiv.rfl) p

  @[hott] def pseq_colim_equiv_constant {A : ℕ → Type*} {f f' : Πn, A n →* A (n+1)}
    (p : Πn, f n ~* f' n) : pseq_colim @f ≃* pseq_colim @f' :=
  pseq_colim_pequiv (λn, pequiv.rfl) (λn, !pid_pcompose ⬝* p n ⬝* !pcompose_pid⁻¹*)

  @[hott] def pseq_colim_pequiv_pinclusion {A A' : ℕ → Type*} {f : Πn, A n →* A (n+1)}
    {f' : Πn, A' n →* A' (n+1)} (g : Πn, A n ≃* A' n)
    (p : Π⦃n⦄, g (n+1) ∘* f n ~* f' n ∘* g n) (n : ℕ) :
    psquare (pinclusion f n) (pinclusion f' n) (g n) (pseq_colim_pequiv g p) :=
  phomotopy.mk homotopy.rfl begin
    esimp, refine !idp_con ⬝ _,
    induction n with n IH,
    { esimp[inclusion_pt], exact !idp_con⁻¹ },
    { esimp[inclusion_pt], rewrite [+ap_con, -+ap_inv, +con.assoc, +seq_colim_functor_glue],
      xrewrite[-IH],
      rewrite[-+ap_compose', -+con.assoc],
      apply whisker_right, esimp,
      rewrite[(eq_con_inv_of_con_eq (to_homotopy_pt (@p _)))],
      rewrite[ap_con], esimp,
      rewrite[-+con.assoc, ap_con, -ap_compose', +ap_inv],
      rewrite[-+con.assoc],
      refine _ ⬝ whisker_right _ (whisker_right _ (whisker_right _ (whisker_right _ !con.left_inv⁻¹))),
      rewrite[idp_con, +con.assoc], apply whisker_left,
      rewrite[ap_con, -ap_compose', con_inv, +con.assoc], apply whisker_left,
      refine eq_inv_con_of_con_eq _,
      symmetry, exact eq_of_square !natural_square
    }
  end

  @[hott] def seq_colim_equiv_constant_pinclusion {A : ℕ → Type*} {f f' : Πn, A n →* A (n+1)}
    (p : Πn, f n ~* f' n) (n : ℕ) :
    pseq_colim_equiv_constant p ∘* pinclusion f n ~* pinclusion f' n  :=
  begin
    transitivity pinclusion f' n ∘* !pid,
    refine phomotopy_of_psquare !pseq_colim_pequiv_pinclusion,
    exact !pcompose_pid
  end

/-
  @[hott] def seq_colim_equiv_zigzag (g : Π⦃n⦄, A n → A' n) (h : Π⦃n⦄, A' n → A (succ n))
    (p : Π⦃n⦄ (a : A n), h (g a) = f a) (q : Π⦃n⦄ (a : A' n), g (h a) = f' a) :
    seq_colim f ≃ seq_colim f' :=
  sorry
-/

  @[hott] def is_equiv_seq_colim_rec (P : seq_colim f → Type _) :
    is_equiv (seq_colim_rec_unc :
      (Σ(Pincl : Π ⦃n : ℕ⦄ (a : A n), P (ι f a)),
        Π ⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue f a] Pincl a)
          → (Π (aa : seq_colim f), P aa)) :=
  begin
    fapply adjointify,
    { intro s, exact ⟨λn a, s (ι f a), λn a, apd s (glue f a)⟩},
    { intro s, apply eq_of_homotopy, intro x, induction x,
      { reflexivity},
      { apply eq_pathover_dep, esimp, apply hdeg_squareover, apply rec_glue}},
    { intro v, induction v with Pincl Pglue, fapply ap (sigma.mk _),
      apply eq_of_homotopy2, intros n a, apply rec_glue},
  end

  /- universal property -/
  @[hott] def equiv_seq_colim_rec (P : seq_colim f → Type _) :
    (Σ(Pincl : Π ⦃n : ℕ⦄ (a : A n), P (ι f a)),
       Π ⦃n : ℕ⦄ (a : A n), Pincl (f a) =[glue f a] Pincl a) ≃ (Π (aa : seq_colim f), P aa) :=
  equiv.mk _ !is_equiv_seq_colim_rec
  end functor

  @[hott] def pseq_colim.elim' {A : ℕ → Type*} {B : Type*} {f : Πn, A n →* A (n+1)}
    (g : Πn, A n →* B) (p : Πn, g (n+1) ∘* f n ~ g n) : pseq_colim f →* B :=
  begin
    fapply pmap.mk,
    { intro x, induction x with n a n a,
      { exact g n a },
      { exact p n a }},
    { esimp, apply respect_pt }
  end

  @[hott] def pseq_colim.elim {A : ℕ → Type*} {B : Type*} {f : Πn, A n →* A (n+1)}
    (g : Πn, A n →* B) (p : Πn, g (n+1) ∘* f n ~* g n) : pseq_colim @f →* B :=
  pseq_colim.elim' g p

  @[hott] def pseq_colim.elim_pinclusion {A : ℕ → Type*} {B : Type*} {f : Πn, A n →* A (n+1)}
    (g : Πn, A n →* B) (p : Πn, g (n+1) ∘* f n ~* g n) (n : ℕ) :
  pseq_colim.elim g p ∘* pinclusion f n ~* g n :=
  begin
    refine phomotopy.mk phomotopy.rfl _,
    refine !idp_con ⬝ _,
    esimp,
    induction n with n IH,
    { esimp, esimp[inclusion_pt], exact !idp_con⁻¹ },
    { esimp, esimp[inclusion_pt],
      rewrite ap_con, rewrite ap_con,
      rewrite elim_glue,
      rewrite [-ap_inv],
      rewrite [-ap_compose'], esimp,
      rewrite [(eq_con_inv_of_con_eq (!to_homotopy_pt))],
      rewrite [IH],
      rewrite [con_inv],
      rewrite [-+con.assoc],
      refine _ ⬝ whisker_right _ !con.assoc⁻¹,
      rewrite [con.left_inv], esimp,
      refine _ ⬝ !con.assoc⁻¹,
      rewrite [con.left_inv], esimp,
      rewrite [ap_inv],
      rewrite [-con.assoc],
      refine !idp_con⁻¹ ⬝ whisker_right _ !con.left_inv⁻¹,
    }
  end

  @[hott] def prep0 {A : ℕ → Type*} (f : pseq_diagram A) (k : ℕ) : A 0 →* A k :=
  pmap.mk (rep0 (λn x, f x) k)
          begin induction k with k p, reflexivity, exact ap (@f k) p ⬝ !respect_pt end

  @[hott] def respect_pt_prep0_succ {A : ℕ → Type*} (f : pseq_diagram A) (k : ℕ)
    : respect_pt (prep0 f (succ k)) = ap (@f k) (respect_pt (prep0 f k)) ⬝ respect_pt (@f k) :=
  by reflexivity

  @[hott] theorem prep0_succ_@[hott] lemma {A : ℕ → Type*} (f : pseq_diagram A) (n : ℕ)
    (p : rep0 (λn x, f x) n pt = rep0 (λn x, f x) n pt)
    (q : prep0 f n (Point (A 0)) = Point (A n))

    : loop_equiv_eq_closed (ap (@f n) q ⬝ respect_pt (@f n))
    (ap (@f n) p) = Ω→(@f n) (loop_equiv_eq_closed q p) :=
  by rewrite [▸*, con_inv, ↑ap1_gen, +ap_con, ap_inv, +con.assoc]

  @[hott] def succ_add_tr_rep {n : ℕ} (k : ℕ) (x : A n)
    : transport A (succ_add n k) (rep f k (f x)) = rep f (succ k) x :=
  begin
    induction k with k p,
      reflexivity,
      exact tr_ap A succ (succ_add n k) _ ⬝ (fn_tr_eq_tr_fn (succ_add n k) f _)⁻¹ ⬝ ap (@f _) p,
  end

  @[hott] def succ_add_tr_rep_succ {n : ℕ} (k : ℕ) (x : A n)
    : succ_add_tr_rep f (succ k) x = tr_ap A succ (succ_add n k) _ ⬝
        (fn_tr_eq_tr_fn (succ_add n k) f _)⁻¹ ⬝ ap (@f _) (succ_add_tr_rep f k x) :=
  by reflexivity

  @[hott] def code_glue_equiv {n : ℕ} (k : ℕ) (x y : A n)
    : rep f k (f x) = rep f k (f y) ≃ rep f (succ k) x = rep f (succ k) y :=
  begin
    refine eq_equiv_fn_eq_of_equiv (equiv_ap A (succ_add n k)) _ _ ⬝e _,
    apply eq_equiv_eq_closed,
      exact succ_add_tr_rep f k x,
      exact succ_add_tr_rep f k y
  end

  @[hott] theorem code_glue_equiv_ap {n : ℕ} {k : ℕ} {x y : A n} (p : rep f k (f x) = rep f k (f y))
    : code_glue_equiv f (succ k) x y (ap (@f _) p) = ap (@f _) (code_glue_equiv f k x y p) :=
  begin
    rewrite [▸*, +ap_con, ap_inv, +succ_add_tr_rep_succ, con_inv, inv_con_inv_right, +con.assoc],
    apply whisker_left,
    rewrite [- +con.assoc], apply whisker_right, rewrite [- +ap_compose'],
    note s := (eq_top_of_square (natural_square_tr
      (λx, fn_tr_eq_tr_fn (succ_add n k) f x ⬝ (tr_ap A succ (succ_add n k) (f x))⁻¹) p))⁻¹ᵖ,
    rewrite [inv_con_inv_right at s, -con.assoc at s], exact s
  end

  section
  parameters {X : ℕ → Type _} (g : seq_diagram X) (x : X 0)

  @[hott] def rep_eq_diag ⦃n : ℕ⦄ (y : X n) : seq_diagram (λk, rep g k (rep0 g n x) = rep g k y) :=
  proof λk, ap (@g (n + k)) qed

  @[hott] def code_incl ⦃n : ℕ⦄ (y : X n) : Type _ :=
  seq_colim (rep_eq_diag y)

  @[hott] def code : seq_colim g → Type _ :=
  seq_colim.elim_type g code_incl
  begin
    intros n y,
    refine _ ⬝e !shift_equiv⁻¹ᵉ,
    fapply seq_colim_equiv,
    { intro k, exact code_glue_equiv g k (rep0 g n x) y },
    { intros k p, exact code_glue_equiv_ap g p }
  end

  @[hott] def encode (y : seq_colim g) (p : ι g x = y) : code y :=
  transport code p (ι' _ 0 idp)

  @[hott] def decode (y : seq_colim g) (c : code y) : ι g x = y :=
  begin
    induction y,
    { esimp at c, exact sorry },
    { exact sorry }
  end

  @[hott] def decode_encode (y : seq_colim g) (p : ι g x = y) : decode y (encode y p) = p :=
  sorry

  @[hott] def encode_decode (y : seq_colim g) (c : code y) : encode y (decode y c) = c :=
  sorry

  @[hott] def seq_colim_eq_equiv_code (y : seq_colim g) : (ι g x = y) ≃ code y :=
  equiv.MK (encode y) (decode y) (encode_decode y) (decode_encode y)

  @[hott] def seq_colim_eq {n : ℕ} (y : X n) : (ι g x = ι g y) ≃ seq_colim (rep_eq_diag y) :=
  proof seq_colim_eq_equiv_code (ι g y) qed

  end

  @[hott] def rep0_eq_diag {X : ℕ → Type _} (f : seq_diagram X) (x y : X 0)
    : seq_diagram (λk, rep0 f k x = rep0 f k y) :=
  proof λk, ap (@f k) qed

  @[hott] def seq_colim_eq0 {X : ℕ → Type _} (f : seq_diagram X) (x y : X 0) :
    (ι f x = ι f y) ≃ seq_colim (rep0_eq_diag f x y)  :=
  begin
    refine !seq_colim_eq ⬝e _,
    fapply seq_colim_equiv,
    { intro n, exact sorry},
    { intros n p, exact sorry }
  end


  @[hott] def pseq_colim_loop {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) :
    Ω (pseq_colim f) ≃* pseq_colim (λn, Ω→(f n)) :=
  begin
    fapply pequiv_of_equiv,
    { refine !seq_colim_eq0 ⬝e _,
      fapply seq_colim_equiv,
      { intro n, exact loop_equiv_eq_closed (respect_pt (prep0 f n)) },
      { intros n p, apply prep0_succ_@[hott] lemma }},
    { exact sorry }
  end

  @[hott] def pseq_colim_loop_pinclusion {X : ℕ → Type*} (f : Πn, X n →* X (n+1)) (n : ℕ) :
    pseq_colim_loop f ∘* Ω→ (pinclusion f n) ~* pinclusion (λn, Ω→(f n)) n :=
  sorry

  -- open succ_str
  -- @[hott] def pseq_colim_succ_str_change_index' {N : succ_str} {B : N → Type*} (n : N) (m : ℕ)
  --   (h : Πn, B n →* B (S n)) :
  --   pseq_colim (λk, h (n +' (m + succ k))) ≃* pseq_colim (λk, h (S n +' (m + k))) :=
  -- sorry

  -- @[hott] def pseq_colim_succ_str_change_index {N : succ_str} {B : ℕ → N → Type*} (n : N)
  --   (h : Π(k : ℕ) n, B k n →* B k (S n)) :
  --   pseq_colim (λk, h k (n +' succ k)) ≃* pseq_colim (λk, h k (S n +' k)) :=
  -- sorry

  -- @[hott] def pseq_colim_index_eq_general {N : succ_str} (B : N → Type*) (f g : ℕ → N) (p : f ~ g)
  --   (pf : Πn, S (f n) = f (n+1)) (pg : Πn, S (g n) = g (n+1)) (h : Πn, B n →* B (S n)) :
  --   @pseq_colim (λn, B (f n)) (λn, ptransport B (pf n) ∘* h (f n)) ≃*
  --   @pseq_colim (λn, B (g n)) (λn, ptransport B (pg n) ∘* h (g n)) :=
  -- sorry


end seq_colim
