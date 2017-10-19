/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

We define the fiber sequence of a pointed map f : X →* Y. We mostly follow the proof in section 8.4
of the book.

PART 1:
We define a sequence fiber_sequence as in @[hott] def 8.4.3.
It has types X(n) : Type*
X(0)   := Y,
X(1)   := X,
X(n+1) := fiber (f(n))
with functions f(n) : X(n+1) →* X(n)
f(0)   := f
f(n+1) := point (f(n)) [this is the first projection]
We prove that this is an exact sequence.
Then we prove @[hott] lemma 8.4.3, by showing that X(n+3) ≃* Ω(X(n)) and that this equivalence sends
the pointed map f(n+3) to -Ω(f(n)), i.e. the composition of Ω(f(n)) with path inversion.
Using this equivalence we get a boundary_map : Ω(Y) → pfiber f.

PART 2:
Now we can define a new fiber sequence X'(n) : Type*, and here we slightly diverge from the book.
We define it as
X'(0)   := Y,
X'(1)   := X,
X'(2)   := fiber f
X'(n+3) := Ω(X'(n))
with maps f'(n) : X'(n+1) →* X'(n)
f'(0) := f
f'(1) := point f
f'(2) := boundary_map
f'(n+3) := Ω(f'(n))

This sequence is not equivalent to the previous sequence. The difference is in the signs.
The sequence f has negative signs (i.e. is composed with the inverse maps) for n ≡ 3, 4, 5 mod 6.
This sign information is captured by e : X'(n) ≃* X'(n) such that
e(k)   := 1               for k = 0,1,2,3
e(k+3) := Ω(e(k)) ∘ (-)⁻¹ for k > 0

Now the sequence (X', f' ∘ e) is equivalent to (X, f), Hence (X', f' ∘ e) is an exact sequence.
We then prove that (X', f') is an exact sequence by using that there are other equivalences
eₗ and eᵣ such that
f' = eᵣ ∘ f' ∘ e
f' ∘ eₗ = e ∘ f'.
(this fact is type_chain_complex_cancel_aut and is_exact_at_t_cancel_aut in the file chain_complex)
eₗ and eᵣ are almost the same as e, except that the places where the inverse is taken is
slightly shifted:
eᵣ = (-)⁻¹ for n ≡ 3, 4, 5 mod 6                       and eᵣ = 1 otherwise
e  = (-)⁻¹ for n ≡ 4, 5, 6 mod 6 (except for n = 0)    and e  = 1 otherwise
eₗ = (-)⁻¹ for n ≡ 5, 6, 7 mod 6 (except for n = 0, 1) and eₗ = 1 otherwise

PART 3:
We change the type over which the sequence of types and maps are indexed from ℕ to ℕ × 3
(where 3 is the finite type with 3 elements). The reason is that we have that X'(3n) = Ωⁿ(Y), but
this equality is not definitionally true. Hence we cannot even state whether f'(3n) = Ωⁿ(f) without
using transports. This gets ugly. However, if we use as index type ℕ × 3, we can do this. We can
define
Y : ℕ × 3 → Type* as
Y(n, 0) := Ωⁿ(Y)
Y(n, 1) := Ωⁿ(X)
Y(n, 2) := Ωⁿ(fiber f)
with maps g(n) : Y(S n) →* Y(n) (where the successor is defined in the obvious way)
g(n, 0) := Ωⁿ(f)
g(n, 1) := Ωⁿ(point f)
g(n, 2) := Ωⁿ(boundary_map) ∘ cast

Here "cast" is the transport over the equality Ωⁿ⁺¹(Y) = Ωⁿ(Ω(Y)). We show that the sequence
(ℕ, X', f') is equivalent to (ℕ × 3, Y, g).

PART 4:
We get the long exact sequence of homotopy groups by taking the set-truncation of (Y, g).
-/

import .chain_complex algebra.homotopy_group eq2

open eq pointed sigma fiber equiv is_equiv is_trunc nat trunc algebra function
/--------------
    PART 1
 --------------/

namespace chain_complex
  section
  open sigma.ops

  @[hott] def fiber_sequence_helper (v : Σ(X Y : Type*), X →* Y)
    : Σ(Z X : Type*), Z →* X :=
  ⟨pfiber v.2.2, v.1, ppoint v.2.2⟩

  @[hott] def fiber_sequence_helpern (v : Σ(X Y : Type*), X →* Y) (n : ℕ)
    : Σ(Z X : Type*), Z →* X :=
  iterate fiber_sequence_helper n v

  end

  section
  open sigma.ops
  universe variable u
  parameters {X Y : pType.{u}} (f : X →* Y)
  include f

  @[hott] def fiber_sequence_carrier (n : ℕ) : Type* :=
  (fiber_sequence_helpern ⟨X, Y, f⟩ n).2.1

  @[hott] def fiber_sequence_fun (n : ℕ)
    : fiber_sequence_carrier (n + 1) →* fiber_sequence_carrier n :=
  (fiber_sequence_helpern ⟨X, Y, f⟩ n).2.2

  /- @[hott] def 8.4.3 -/
  @[hott] def fiber_sequence : type_chain_complex.{0 u} +ℕ :=
  begin
    fconstructor,
    { exact fiber_sequence_carrier },
    { exact fiber_sequence_fun },
    { intros n x, cases n with n,
      { exact point_eq x },
      { exact point_eq x }}
  end

  @[hott] def is_exact_fiber_sequence : is_exact_t fiber_sequence :=
  λn x p, fiber.mk (fiber.mk x p) rfl

  /- (generalization of) @[hott] lemma 8.4.4(i)(ii) -/
  @[hott] def fiber_sequence_carrier_pequiv (n : ℕ)
    : fiber_sequence_carrier (n+3) ≃* Ω(fiber_sequence_carrier n) :=
  pfiber_ppoint_pequiv (fiber_sequence_fun n)

  @[hott] def fiber_sequence_carrier_pequiv_eq (n : ℕ)
    (x : fiber_sequence_carrier (n+1)) (p : fiber_sequence_fun n x = pt)
    (q : fiber_sequence_fun (n+1) (fiber.mk x p) = pt)
    : fiber_sequence_carrier_pequiv n (fiber.mk (fiber.mk x p) q)
      = !respect_pt⁻¹ ⬝ ap (fiber_sequence_fun n) q⁻¹ ⬝ p :=
  fiber_ppoint_equiv_eq p q

  @[hott] def fiber_sequence_carrier_pequiv_inv_eq (n : ℕ)
    (p : Ω(fiber_sequence_carrier n)) : (fiber_sequence_carrier_pequiv n)⁻¹ᵉ* p =
      fiber.mk (fiber.mk pt (respect_pt (fiber_sequence_fun n) ⬝ p)) idp :=
  fiber_ppoint_equiv_inv_eq (fiber_sequence_fun n) p

  /- TODO: prove naturality of pfiber_ppoint_pequiv in general -/

  /- @[hott] lemma 8.4.4(iii) -/
  @[hott] def fiber_sequence_fun_eq_helper (n : ℕ)
    (p : Ω(fiber_sequence_carrier (n + 1))) :
    fiber_sequence_carrier_pequiv n
      (fiber_sequence_fun (n + 3)
        ((fiber_sequence_carrier_pequiv (n + 1))⁻¹ᵉ* p)) =
          Ω→ (fiber_sequence_fun n) p⁻¹ :=
  begin
    refine ap (λx, fiber_sequence_carrier_pequiv n (fiber_sequence_fun (n + 3) x))
              (fiber_sequence_carrier_pequiv_inv_eq (n+1) p) ⬝ _,
    /- the following three lines are rewriting some reflexivities: -/
    -- replace (n + 3) with (n + 2 + 1),
    -- refine ap (fiber_sequence_carrier_pequiv n)
    --           (fiber_sequence_fun_eq1 (n+2) _ idp) ⬝ _,
    refine fiber_sequence_carrier_pequiv_eq n pt (respect_pt (fiber_sequence_fun n)) _ ⬝ _,
    esimp,
    apply whisker_right,
    apply whisker_left,
    apply ap02, apply inverse2, apply idp_con,
  end

  @[hott] theorem fiber_sequence_carrier_pequiv_eq_point_eq_idp (n : ℕ) :
    fiber_sequence_carrier_pequiv_eq n
      (Point (fiber_sequence_carrier (n+1)))
      (respect_pt (fiber_sequence_fun n))
      (respect_pt (fiber_sequence_fun (n + 1))) = idp :=
  begin
    apply con_inv_eq_idp,
    refine ap (λx, whisker_left _ (_ ⬝ x)) _ ⬝ _,
    { reflexivity},
    { reflexivity},
    refine ap (whisker_left _)
              (eq_transport_Fl_idp_left (fiber_sequence_fun n)
                                        (respect_pt (fiber_sequence_fun n))) ⬝ _,
    apply whisker_left_idp_con_eq_assoc
  end

  @[hott] theorem fiber_sequence_fun_phomotopy_helper (n : ℕ) :
    (fiber_sequence_carrier_pequiv n ∘*
      fiber_sequence_fun (n + 3)) ∘*
        (fiber_sequence_carrier_pequiv (n + 1))⁻¹ᵉ* ~*
          Ω→ (fiber_sequence_fun n) ∘* pinverse :=
  begin
    fapply phomotopy.mk,
    { exact chain_complex.fiber_sequence_fun_eq_helper f n},
    { esimp, rewrite [idp_con], refine _ ⬝ whisker_left _ !idp_con⁻¹,
      apply whisker_right,
      apply whisker_left,
      exact chain_complex.fiber_sequence_carrier_pequiv_eq_point_eq_idp f n}
  end

  @[hott] theorem fiber_sequence_fun_eq (n : ℕ) : Π(x : fiber_sequence_carrier (n + 4)),
    fiber_sequence_carrier_pequiv n (fiber_sequence_fun (n + 3) x) =
      Ω→ (fiber_sequence_fun n) (fiber_sequence_carrier_pequiv (n + 1) x)⁻¹ :=
  begin
    refine @(homotopy_of_inv_homotopy_pre (fiber_sequence_carrier_pequiv (n + 1)))
             !pequiv.to_is_equiv _ _ _,
    apply fiber_sequence_fun_eq_helper n
  end

  @[hott] theorem fiber_sequence_fun_phomotopy (n : ℕ) :
    fiber_sequence_carrier_pequiv n ∘*
      fiber_sequence_fun (n + 3) ~*
          (Ω→ (fiber_sequence_fun n) ∘* pinverse) ∘* fiber_sequence_carrier_pequiv (n + 1) :=
  begin
    apply phomotopy_of_pinv_right_phomotopy,
    apply fiber_sequence_fun_phomotopy_helper
  end

  @[hott] def boundary_map : Ω Y →* pfiber f :=
  fiber_sequence_fun 2 ∘* (fiber_sequence_carrier_pequiv 0)⁻¹ᵉ*

/--------------
    PART 2
 --------------/

  /- Now we are ready to define the long exact sequence of loop spaces.
     First we define its carrier -/
  @[hott] def loop_spaces : ℕ → Type*
  | 0     := Y
  | 1     := X
  | 2     := pfiber f
  | (k+3) := Ω (loop_spaces k)

  /- The maps between the homotopy groups -/
  @[hott] def loop_spaces_fun : Π(n : ℕ), loop_spaces (n+1) →* loop_spaces n
  | 0     := proof f qed
  | 1     := proof ppoint f qed
  | 2     := proof boundary_map qed
  | (k+3) := proof Ω→ (loop_spaces_fun k) qed

  @[hott] def loop_spaces_fun_add3 (n : ℕ) :
    loop_spaces_fun (n + 3) = Ω→ (loop_spaces_fun n) :=
  idp

  @[hott] def fiber_sequence_pequiv_loop_spaces :
    Πn, fiber_sequence_carrier n ≃* loop_spaces n
  | 0     := by reflexivity
  | 1     := by reflexivity
  | 2     := by reflexivity
  | (k+3) :=
    begin
      refine fiber_sequence_carrier_pequiv k ⬝e* _,
      apply loop_pequiv_loop,
      exact fiber_sequence_pequiv_loop_spaces k
    end

  @[hott] def fiber_sequence_pequiv_loop_spaces_add3 (n : ℕ)
    : fiber_sequence_pequiv_loop_spaces (n + 3) =
      Ω→ (fiber_sequence_pequiv_loop_spaces n) ∘* fiber_sequence_carrier_pequiv n :=
  by reflexivity

  @[hott] def fiber_sequence_pequiv_loop_spaces_3_phomotopy
    : fiber_sequence_pequiv_loop_spaces 3 ~* fiber_sequence_carrier_pequiv 0 :=
  begin
    refine pwhisker_right _ ap1_pid ⬝* _,
    apply pid_pcompose
  end

  @[hott] def pid_or_pinverse : Π(n : ℕ), loop_spaces n ≃* loop_spaces n
  | 0     := pequiv.rfl
  | 1     := pequiv.rfl
  | 2     := pequiv.rfl
  | 3     := pequiv.rfl
  | (k+4) := !pequiv_pinverse ⬝e* loop_pequiv_loop (pid_or_pinverse (k+1))

  @[hott] def pid_or_pinverse_add4 (n : ℕ)
    : pid_or_pinverse (n + 4) = !pequiv_pinverse ⬝e* loop_pequiv_loop (pid_or_pinverse (n + 1)) :=
  by reflexivity

  @[hott] def pid_or_pinverse_add4_rev (n : ℕ) :
    pid_or_pinverse (n + 4) ~* pinverse ∘* Ω→(pid_or_pinverse (n + 1)) :=
  !ap1_pcompose_pinverse

  @[hott] theorem fiber_sequence_phomotopy_loop_spaces : Π(n : ℕ),
    fiber_sequence_pequiv_loop_spaces n ∘* fiber_sequence_fun n ~*
      (loop_spaces_fun n ∘* pid_or_pinverse (n + 1)) ∘* fiber_sequence_pequiv_loop_spaces (n + 1)
  | 0     := proof proof phomotopy.rfl qed ⬝* pwhisker_right _ !pcompose_pid⁻¹* qed
  | 1     := by reflexivity
  | 2     :=
    begin
      refine !pid_pcompose ⬝* _,
      replace loop_spaces_fun 2 with boundary_map,
      refine _ ⬝* pwhisker_left _ fiber_sequence_pequiv_loop_spaces_3_phomotopy⁻¹*,
      apply phomotopy_of_pinv_right_phomotopy,
      exact !pcompose_pid⁻¹*
    end
  | (k+3) :=
    begin
      replace (k + 3 + 1) with (k + 1 + 3),
      rewrite [fiber_sequence_pequiv_loop_spaces_add3 k,
               fiber_sequence_pequiv_loop_spaces_add3 (k+1)],
      refine !passoc ⬝* _,
      refine pwhisker_left _ (fiber_sequence_fun_phomotopy k) ⬝* _,
      refine !passoc⁻¹* ⬝* _ ⬝* !passoc,
      apply pwhisker_right,
      replace (k + 1 + 3) with (k + 4),
      xrewrite [loop_spaces_fun_add3, pid_or_pinverse_add4, to_pmap_pequiv_trans],
      refine _ ⬝* !passoc⁻¹*,
      refine _ ⬝* pwhisker_left _ !passoc⁻¹*,
      refine _ ⬝* pwhisker_left _ (pwhisker_left _ !ap1_pcompose_pinverse),
      refine !passoc⁻¹* ⬝* _ ⬝* !passoc ⬝* !passoc,
      apply pwhisker_right,
      refine !ap1_pcompose⁻¹* ⬝* _ ⬝* !ap1_pcompose ⬝* pwhisker_right _ !ap1_pcompose,
      apply ap1_phomotopy,
      exact fiber_sequence_phomotopy_loop_spaces k
    end

  @[hott] def pid_or_pinverse_right : Π(n : ℕ), loop_spaces n →* loop_spaces n
  | 0     := !pid
  | 1     := !pid
  | 2     := !pid
  | (k+3) := Ω→(pid_or_pinverse_right k) ∘* pinverse

  @[hott] def pid_or_pinverse_left : Π(n : ℕ), loop_spaces n →* loop_spaces n
  | 0     := pequiv.rfl
  | 1     := pequiv.rfl
  | 2     := pequiv.rfl
  | 3     := pequiv.rfl
  | 4     := pequiv.rfl
  | (k+5) := Ω→(pid_or_pinverse_left (k+2)) ∘* pinverse

  @[hott] def pid_or_pinverse_right_add3 (n : ℕ)
    : pid_or_pinverse_right (n + 3) = Ω→(pid_or_pinverse_right n) ∘* pinverse :=
  by reflexivity

  @[hott] def pid_or_pinverse_left_add5 (n : ℕ)
    : pid_or_pinverse_left (n + 5) = Ω→(pid_or_pinverse_left (n+2)) ∘* pinverse :=
  by reflexivity

  @[hott] theorem pid_or_pinverse_commute_right : Π(n : ℕ),
    loop_spaces_fun n ~* pid_or_pinverse_right n ∘* loop_spaces_fun n ∘* pid_or_pinverse (n + 1)
  | 0     := proof !pcompose_pid⁻¹* ⬝* !pid_pcompose⁻¹* qed
  | 1     := proof !pcompose_pid⁻¹* ⬝* !pid_pcompose⁻¹* qed
  | 2     := proof !pcompose_pid⁻¹* ⬝* !pid_pcompose⁻¹* qed
  | (k+3) :=
    begin
      replace (k + 3 + 1) with (k + 4),
      rewrite [pid_or_pinverse_right_add3, loop_spaces_fun_add3],
      refine _ ⬝* pwhisker_left _ (pwhisker_left _ !pid_or_pinverse_add4_rev⁻¹*),
      refine ap1_phomotopy (pid_or_pinverse_commute_right k) ⬝* _,
      refine !ap1_pcompose ⬝* _ ⬝* !passoc⁻¹*,
      apply pwhisker_left,
      refine !ap1_pcompose ⬝* _ ⬝* !passoc ⬝* !passoc,
      apply pwhisker_right,
      refine _ ⬝* pwhisker_right _ !ap1_pcompose_pinverse,
      refine _ ⬝* !passoc⁻¹*,
      refine !pcompose_pid⁻¹* ⬝* pwhisker_left _ _,
      symmetry, apply pinverse_pinverse
    end

  @[hott] theorem pid_or_pinverse_commute_left : Π(n : ℕ),
    loop_spaces_fun n ∘* pid_or_pinverse_left (n + 1) ~* pid_or_pinverse n ∘* loop_spaces_fun n
  | 0     := proof !pcompose_pid ⬝* !pid_pcompose⁻¹* qed
  | 1     := proof !pcompose_pid ⬝* !pid_pcompose⁻¹* qed
  | 2     := proof !pcompose_pid ⬝* !pid_pcompose⁻¹* qed
  | 3     := proof !pcompose_pid ⬝* !pid_pcompose⁻¹* qed
  | (k+4) :=
    begin
      replace (k + 4 + 1) with (k + 5),
      rewrite [pid_or_pinverse_left_add5, pid_or_pinverse_add4],
      replace (k + 4) with (k + 1 + 3),
      rewrite [loop_spaces_fun_add3],
      refine !passoc⁻¹* ⬝* _ ⬝* !passoc⁻¹*,
      refine _ ⬝* pwhisker_left _ !ap1_pcompose_pinverse,
      refine _ ⬝* !passoc,
      apply pwhisker_right,
      refine !ap1_pcompose⁻¹* ⬝* _ ⬝* !ap1_pcompose,
      exact ap1_phomotopy (pid_or_pinverse_commute_left (k+1))
    end

  @[hott] def LES_of_loop_spaces' : type_chain_complex +ℕ :=
  transfer_type_chain_complex
    fiber_sequence
    (λn, loop_spaces_fun n ∘* pid_or_pinverse (n + 1))
    fiber_sequence_pequiv_loop_spaces
    fiber_sequence_phomotopy_loop_spaces

  @[hott] def LES_of_loop_spaces : type_chain_complex +ℕ :=
  type_chain_complex_cancel_aut
    LES_of_loop_spaces'
    loop_spaces_fun
    pid_or_pinverse
    pid_or_pinverse_right
    (λn x, idp)
    pid_or_pinverse_commute_right

  @[hott] def is_exact_LES_of_loop_spaces : is_exact_t LES_of_loop_spaces :=
  begin
    intro n,
    refine is_exact_at_t_cancel_aut n pid_or_pinverse_left _ _ pid_or_pinverse_commute_left _,
    apply is_exact_at_t_transfer,
    apply is_exact_fiber_sequence
  end

  open prod succ_str fin

  /--------------
      PART 3
   --------------/

  @[hott] def fibration_sequence : fin 3 → Type*
  | (fin.mk 0 H)     := Y
  | (fin.mk 1 H)     := X
  | (fin.mk 2 H)     := pfiber f
  | (fin.mk (n+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  @[hott] def loop_spaces2 [reducible] : +3ℕ → Type*
  | (n, m) := Ω[n] (fibration_sequence m)

  @[hott] def loop_spaces2_add1 (n : ℕ) : Π(x : fin 3),
    loop_spaces2 (n+1, x) = Ω (loop_spaces2 (n, x))
  | (fin.mk 0 H) := by reflexivity
  | (fin.mk 1 H) := by reflexivity
  | (fin.mk 2 H) := by reflexivity
  | (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  @[hott] def loop_spaces_fun2 : Π(n : +3ℕ), loop_spaces2 (S n) →* loop_spaces2 n
  | (n, fin.mk 0 H) := proof Ω→[n] f qed
  | (n, fin.mk 1 H) := proof Ω→[n] (ppoint f) qed
  | (n, fin.mk 2 H) := proof Ω→[n] boundary_map ∘* loopn_succ_in Y n qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  @[hott] def loop_spaces_fun2_add1_0 (n : ℕ) (H : 0 < succ 2)
    : loop_spaces_fun2 (n+1, fin.mk 0 H) ~*
      cast proof idp qed ap1 (loop_spaces_fun2 (n, fin.mk 0 H)) :=
  by reflexivity

  @[hott] def loop_spaces_fun2_add1_1 (n : ℕ) (H : 1 < succ 2)
    : loop_spaces_fun2 (n+1, fin.mk 1 H) ~*
      cast proof idp qed ap1 (loop_spaces_fun2 (n, fin.mk 1 H)) :=
  by reflexivity

  @[hott] def loop_spaces_fun2_add1_2 (n : ℕ) (H : 2 < succ 2)
    : loop_spaces_fun2 (n+1, fin.mk 2 H) ~*
      cast proof idp qed ap1 (loop_spaces_fun2 (n, fin.mk 2 H)) :=
  proof !ap1_pcompose⁻¹* qed

  @[hott] def nat_of_str [reducible] {n : ℕ} : ℕ × fin (succ n) → ℕ :=
  λx, succ n * pr1 x + val (pr2 x)

  @[hott] def str_of_nat {n : ℕ} : ℕ → ℕ × fin (succ n) :=
  λm, (m / (succ n), mk_mod n m)

  @[hott] def nat_of_str_3S [reducible]
    : Π(x : stratified +ℕ 2), nat_of_str x + 1 = nat_of_str (@S (stratified +ℕ 2) x)
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := by reflexivity
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  @[hott] def fin_prod_nat_equiv_nat (n : ℕ) : ℕ × fin (succ n) ≃ ℕ :=
  equiv.MK nat_of_str str_of_nat
    abstract begin
      intro m, unfold [nat_of_str, str_of_nat, mk_mod],
      refine _ ⬝ (eq_div_mul_add_mod m (succ n))⁻¹,
      rewrite [mul.comm]
    end end
    abstract begin
      intro x, cases x with m k,
      cases k with k H,
      apply prod_eq: esimp [str_of_nat],
      { rewrite [add.comm, add_mul_div_self_left _ _ (!zero_lt_succ), ▸*,
                 div_eq_zero_of_lt H, zero_add]},
      { apply eq_of_veq, esimp [mk_mod],
        rewrite [add.comm, add_mul_mod_self_left, ▸*, mod_eq_of_lt H]}
    end end

  /-
    note: in the following @[hott] theorem the (n+1) case is 3 times the same,
    so maybe this can be simplified
  -/
  @[hott] def loop_spaces2_pequiv' : Π(n : ℕ) (x : fin (nat.succ 2)),
    loop_spaces (nat_of_str (n, x)) ≃* loop_spaces2 (n, x)
  |  0    (fin.mk 0 H)     := by reflexivity
  |  0    (fin.mk 1 H)     := by reflexivity
  |  0    (fin.mk 2 H)     := by reflexivity
  | (n+1) (fin.mk 0 H)     :=
    begin
      apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 0 H)
    end
  | (n+1) (fin.mk 1 H)     :=
    begin
      apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 1 H)
    end
  | (n+1) (fin.mk 2 H)     :=
    begin
      apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 2 H)
    end
  | n     (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  @[hott] def loop_spaces2_pequiv : Π(x : +3ℕ),
    loop_spaces (nat_of_str x) ≃* loop_spaces2 x
  | (n, x) := loop_spaces2_pequiv' n x

  local attribute loop_pequiv_loop [reducible]

  /- all cases where n>0 are basically the same -/
  @[hott] def loop_spaces_fun2_phomotopy (x : +3ℕ) :
    loop_spaces2_pequiv x ∘* loop_spaces_fun (nat_of_str x) ~*
      (loop_spaces_fun2 x ∘* loop_spaces2_pequiv (S x))
    ∘* pcast (ap (loop_spaces) (nat_of_str_3S x)) :=
  begin
    cases x with n x, cases x with k H,
    do 3 (cases k with k; rotate 1),
    { /-k≥3-/ exfalso, apply lt_le_antisymm H, apply le_add_left},
    { /-k=0-/
      induction n with n IH,
      { refine !pid_pcompose ⬝* _ ⬝* !pcompose_pid⁻¹* ⬝* !pcompose_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !pcompose_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ !loop_spaces_fun2_add1_0⁻¹*,
        refine !ap1_pcompose⁻¹* ⬝* _ ⬝* !ap1_pcompose, apply ap1_phomotopy,
        exact IH ⬝* !pcompose_pid}},
    { /-k=1-/
      induction n with n IH,
      { refine !pid_pcompose ⬝* _ ⬝* !pcompose_pid⁻¹* ⬝* !pcompose_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !pcompose_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ !loop_spaces_fun2_add1_1⁻¹*,
        refine !ap1_pcompose⁻¹* ⬝* _ ⬝* !ap1_pcompose, apply ap1_phomotopy,
        exact IH ⬝* !pcompose_pid}},
    { /-k=2-/
      induction n with n IH,
      { refine !pid_pcompose ⬝* _ ⬝* !pcompose_pid⁻¹*,
        refine !pcompose_pid⁻¹* ⬝* pconcat2 _ _,
        { exact (pcompose_pid (chain_complex.boundary_map f))⁻¹*},
        { refine !loop_pequiv_loop_rfl⁻¹* }},
      { refine _ ⬝* !pcompose_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ !loop_spaces_fun2_add1_2⁻¹*,
        refine !ap1_pcompose⁻¹* ⬝* _ ⬝* !ap1_pcompose, apply ap1_phomotopy,
        exact IH ⬝* !pcompose_pid}},
  end

  @[hott] def LES_of_loop_spaces2 : type_chain_complex +3ℕ :=
  transfer_type_chain_complex2
    LES_of_loop_spaces
    !fin_prod_nat_equiv_nat
    nat_of_str_3S
    @loop_spaces_fun2
    @loop_spaces2_pequiv
    begin
      intros m x,
      refine loop_spaces_fun2_phomotopy m x ⬝ _,
      apply ap (loop_spaces_fun2 m), apply ap (loop_spaces2_pequiv (S m)),
      esimp, exact ap010 cast !ap_compose⁻¹ x
    end

  @[hott] def is_exact_LES_of_loop_spaces2 : is_exact_t LES_of_loop_spaces2 :=
  begin
    intro n,
    apply is_exact_at_t_transfer2,
    apply is_exact_LES_of_loop_spaces
  end

  @[hott] def LES_of_homotopy_groups' : chain_complex +3ℕ :=
  trunc_chain_complex LES_of_loop_spaces2

/--------------
    PART 4
 --------------/
  open prod.ops

  @[hott] def homotopy_groups [reducible] : +3ℕ → Set* :=
  λnm, π[nm.1] (fibration_sequence nm.2)

  @[hott] def homotopy_groups_pequiv_loop_spaces2 [reducible]
    : Π(n : +3ℕ), ptrunc 0 (loop_spaces2 n) ≃* homotopy_groups n
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := by reflexivity
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  @[hott] def homotopy_groups_fun : Π(n : +3ℕ), homotopy_groups (S n) →* homotopy_groups n
  | (n, fin.mk 0 H) := proof π→[n] f qed
  | (n, fin.mk 1 H) := proof π→[n] (ppoint f) qed
  | (n, fin.mk 2 H) :=
    proof π→[n] boundary_map ∘* homotopy_group_succ_in Y n qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  @[hott] def homotopy_groups_fun_phomotopy_loop_spaces_fun2 [reducible]
    : Π(n : +3ℕ), homotopy_groups_pequiv_loop_spaces2 n ∘* ptrunc_functor 0 (loop_spaces_fun2 n) ~*
      homotopy_groups_fun n ∘* homotopy_groups_pequiv_loop_spaces2 (S n)
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) :=
    begin
      refine !pid_pcompose ⬝* _ ⬝* !pcompose_pid⁻¹*,
      refine !ptrunc_functor_pcompose
    end
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  @[hott] def LES_of_homotopy_groups : chain_complex +3ℕ :=
  transfer_chain_complex
    LES_of_homotopy_groups'
    homotopy_groups_fun
    homotopy_groups_pequiv_loop_spaces2
    homotopy_groups_fun_phomotopy_loop_spaces_fun2

  @[hott] def is_exact_LES_of_homotopy_groups : is_exact LES_of_homotopy_groups :=
  begin
    intro n,
    apply is_exact_at_transfer,
    apply is_exact_at_trunc,
    apply is_exact_LES_of_loop_spaces2
  end

  variable (n : ℕ)

  /- the carrier of the fiber sequence is definitionally what we want (as pointed sets) -/
  example : LES_of_homotopy_groups (str_of_nat 6)  = π[2] Y          :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 7)  = π[2] X          :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 8)  = π[2] (pfiber f) :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 9)  = π[3] Y          :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 10) = π[3] X          :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 11) = π[3] (pfiber f) :> Set* := by reflexivity

  @[hott] def LES_of_homotopy_groups_0 : LES_of_homotopy_groups (n, 0) = π[n] Y :=
  by reflexivity
  @[hott] def LES_of_homotopy_groups_1 : LES_of_homotopy_groups (n, 1) = π[n] X :=
  by reflexivity
  @[hott] def LES_of_homotopy_groups_2 : LES_of_homotopy_groups (n, 2) = π[n] (pfiber f) :=
  by reflexivity

  /-
    the functions of the fiber sequence is definitionally what we want (as pointed function).
  -/

  @[hott] def LES_of_homotopy_groups_fun_0 :
    cc_to_fn LES_of_homotopy_groups (n, 0) = π→[n] f :=
  by reflexivity
  @[hott] def LES_of_homotopy_groups_fun_1 :
    cc_to_fn LES_of_homotopy_groups (n, 1) = π→[n] (ppoint f) :=
  by reflexivity
  @[hott] def LES_of_homotopy_groups_fun_2 : cc_to_fn LES_of_homotopy_groups (n, 2) =
    π→[n] boundary_map ∘* homotopy_group_succ_in Y n :=
  by reflexivity

  open group

  @[hott] def group_LES_of_homotopy_groups (n : ℕ) [is_succ n] (x : fin (succ 2)) :
    group (LES_of_homotopy_groups (n, x)) :=
  group_homotopy_group n (fibration_sequence x)

  @[hott] def pgroup_LES_of_homotopy_groups (n : ℕ) [H : is_succ n] (x : fin (succ 2)) :
    pgroup (LES_of_homotopy_groups (n, x)) :=
  by induction H with n; exact @pgroup_of_group _ (group_LES_of_homotopy_groups (n+1) x) idp

  @[hott] def ab_group_LES_of_homotopy_groups (n : ℕ) [is_at_least_two n] (x : fin (succ 2)) :
    ab_group (LES_of_homotopy_groups (n, x)) :=
  ab_group_homotopy_group n (fibration_sequence x)

  @[hott] def Group_LES_of_homotopy_groups (n : +3ℕ) : Group.{u} :=
  πg[n.1+1] (fibration_sequence n.2)

  @[hott] def AbGroup_LES_of_homotopy_groups (n : +3ℕ) : AbGroup.{u} :=
  πag[n.1+2] (fibration_sequence n.2)

  @[hott] def homomorphism_LES_of_homotopy_groups_fun : Π(k : +3ℕ),
    Group_LES_of_homotopy_groups (S k) →g Group_LES_of_homotopy_groups k
  | (k, fin.mk 0 H) :=
    proof homomorphism.mk (cc_to_fn LES_of_homotopy_groups (k + 1, 0))
                          (homotopy_group_functor_mul _ _) qed
  | (k, fin.mk 1 H) :=
    proof homomorphism.mk (cc_to_fn LES_of_homotopy_groups (k + 1, 1))
                          (homotopy_group_functor_mul _ _) qed
  | (k, fin.mk 2 H) :=
    begin
      apply homomorphism.mk (cc_to_fn LES_of_homotopy_groups (k + 1, 2)),
      exact abstract begin rewrite [LES_of_homotopy_groups_fun_2],
      refine homomorphism.struct ((π→g[k+1] boundary_map) ∘g ghomotopy_group_succ_in Y k),
      end end
    end
  | (k, fin.mk (l+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  @[hott] def LES_is_equiv_of_trivial (n : ℕ) (x : fin (succ 2)) [H : is_succ n]
    (HX1 : is_contr (LES_of_homotopy_groups (stratified_pred snat' (n, x))))
    (HX2 : is_contr (LES_of_homotopy_groups (stratified_pred snat' (n+1, x))))
    : is_equiv (cc_to_fn LES_of_homotopy_groups (n, x)) :=
  begin
    induction H with n,
    induction x with m H, cases m with m,
    { rexact @is_equiv_of_trivial +3ℕ LES_of_homotopy_groups (n, 2) (is_exact_LES_of_homotopy_groups (n, 2))
        proof (is_exact_LES_of_homotopy_groups (n+1, 0)) qed HX1 proof HX2 qed
        proof pgroup_LES_of_homotopy_groups (n+1) 0 qed proof pgroup_LES_of_homotopy_groups (n+1) 1 qed
        proof homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun (n, 0)) qed },
    cases m with m,
    { rexact @is_equiv_of_trivial +3ℕ LES_of_homotopy_groups (n+1, 0) (is_exact_LES_of_homotopy_groups (n+1, 0))
        proof (is_exact_LES_of_homotopy_groups (n+1, 1)) qed HX1 proof HX2 qed
        proof pgroup_LES_of_homotopy_groups (n+1) 1 qed proof pgroup_LES_of_homotopy_groups (n+1) 2 qed
        proof homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun (n, 1)) qed }, cases m with m,
    { rexact @is_equiv_of_trivial +3ℕ LES_of_homotopy_groups (n+1, 1) (is_exact_LES_of_homotopy_groups (n+1, 1))
        proof (is_exact_LES_of_homotopy_groups (n+1, 2)) qed HX1 proof HX2 qed
        proof pgroup_LES_of_homotopy_groups (n+1) 2 qed proof pgroup_LES_of_homotopy_groups (n+2) 0 qed
        proof homomorphism.struct (homomorphism_LES_of_homotopy_groups_fun (n, 2)) qed },
    exfalso, apply lt_le_antisymm H, apply le_add_left
  end

  @[hott] def LES_isomorphism_of_trivial_cod (n : ℕ) [H : is_succ n]
    (HX1 : is_contr (πg[n] Y)) (HX2 : is_contr (πg[n+1] Y)) : πg[n] (pfiber f) ≃g πg[n] X :=
  begin
    induction H with n,
    refine isomorphism.mk (homomorphism_LES_of_homotopy_groups_fun (n, 1)) _,
    apply LES_is_equiv_of_trivial, apply HX1, apply HX2
  end

  @[hott] def LES_isomorphism_of_trivial_dom (n : ℕ) [H : is_succ n]
    (HX1 : is_contr (πg[n] X)) (HX2 : is_contr (πg[n+1] X)) : πg[n+1] Y ≃g πg[n] (pfiber f) :=
  begin
    induction H with n,
    refine isomorphism.mk (homomorphism_LES_of_homotopy_groups_fun (n, 2)) _,
    apply LES_is_equiv_of_trivial, apply HX1, apply HX2
  end

  @[hott] def LES_isomorphism_of_trivial_pfiber (n : ℕ)
    (HX1 : is_contr (π[n] (pfiber f))) (HX2 : is_contr (πg[n+1] (pfiber f))) : πg[n+1] X ≃g πg[n+1] Y :=
  begin
    refine isomorphism.mk (homomorphism_LES_of_homotopy_groups_fun (n, 0)) _,
    apply LES_is_equiv_of_trivial, apply HX1, apply HX2
  end

  end

  /-
    Fibration sequences

    This is a similar construction, but with as input data two pointed maps,
    and a pointed equivalence between the domain of the second map and the fiber of the first map,
    and a pointed homotopy.
  -/

  section
  universe variable u
  parameters {F X Y : pType.{u}} (f : X →* Y) (g : F →* X) (e : pfiber f ≃* F)
             (p : ppoint f ~* g ∘* e)
  include f p
  open succ_str prod nat
  @[hott] def fibration_sequence_car [reducible] : +3ℕ → Type*
  | (n, fin.mk 0 H) := Ω[n] Y
  | (n, fin.mk 1 H) := Ω[n] X
  | (n, fin.mk k H) := Ω[n] F

  @[hott] def fibration_sequence_fun
    : Π(n : +3ℕ), fibration_sequence_car (S n) →* fibration_sequence_car n
  | (n, fin.mk 0 H) := proof Ω→[n] f qed
  | (n, fin.mk 1 H) := proof Ω→[n] g qed
  | (n, fin.mk 2 H) := proof Ω→[n] (e ∘* boundary_map f) ∘* loopn_succ_in Y n qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  @[hott] def fibration_sequence_pequiv : Π(x : +3ℕ),
     loop_spaces2 f x ≃* fibration_sequence_car x
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := loopn_pequiv_loopn n e
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  @[hott] def fibration_sequence_fun_phomotopy : Π(x : +3ℕ),
    fibration_sequence_pequiv x ∘* loop_spaces_fun2 f x ~*
      (fibration_sequence_fun x ∘* fibration_sequence_pequiv (S x))
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) :=
    begin refine !pid_pcompose ⬝* _, refine apn_phomotopy n p ⬝* _,
      refine !apn_pcompose ⬝* _, reflexivity end
  | (n, fin.mk 2 H) := begin refine !passoc⁻¹* ⬝* _ ⬝* !pcompose_pid⁻¹*, apply pwhisker_right,
      refine _ ⬝* !apn_pcompose⁻¹*, reflexivity end
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  @[hott] def type_LES_fibration_sequence : type_chain_complex +3ℕ :=
  transfer_type_chain_complex
    (LES_of_loop_spaces2 f)
    fibration_sequence_fun
    fibration_sequence_pequiv
    fibration_sequence_fun_phomotopy

  @[hott] def is_exact_type_fibration_sequence : is_exact_t type_LES_fibration_sequence :=
  begin
    intro n,
    apply is_exact_at_t_transfer,
    apply is_exact_LES_of_loop_spaces2
  end

  @[hott] def LES_fibration_sequence : chain_complex +3ℕ :=
  trunc_chain_complex type_LES_fibration_sequence

  end


end chain_complex
