/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import Mathlib.Algebra.Order.BigOperators.Expect
public import Mathlib.Basic.Real.Basic
public import Mathlib.Data.Fintype.BigOperators
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.NormNum
public import Mathlib.Tactic.Ring

/-!
# Finite averages for the invariant-subspace argument
-/

@[expose] public section

namespace AlmostInvariant

/-- The mean of a function on a finite type. -/
noncomputable def avg {ι : Type} [Fintype ι] (φ : ι → ℝ) : ℝ :=
  Finset.expect Finset.univ φ

section avg
variable {ι : Type} [Fintype ι]

theorem avg_eq_sum_div_card (φ : ι → ℝ) : avg φ = (∑ i, φ i) / (Fintype.card ι : ℝ) :=
  Fintype.expect_eq_sum_div_card φ

theorem avg_add (φ ψ : ι → ℝ) : avg (fun i => φ i + ψ i) = avg φ + avg ψ :=
  Finset.expect_add_distrib _ φ ψ

theorem avg_sub (φ ψ : ι → ℝ) : avg (fun i => φ i - ψ i) = avg φ - avg ψ :=
  Finset.expect_sub_distrib _ φ ψ

theorem avg_mul (c : ℝ) (φ : ι → ℝ) : avg (fun i => c * φ i) = c * avg φ :=
  (Finset.mul_expect _ φ c).symm

theorem avg_const [Nonempty ι] (c : ℝ) : avg (fun _ : ι => c) = c :=
  Fintype.expect_const c

theorem avg_mono {φ ψ : ι → ℝ} (h : ∀ i, φ i ≤ ψ i) : avg φ ≤ avg ψ :=
  Finset.expect_le_expect fun i _ => h i

theorem avg_sum {κ : Type} (s : Finset κ) (φ : κ → ι → ℝ) :
    avg (fun i => ∑ k ∈ s, φ k i) = ∑ k ∈ s, avg (φ k) :=
  Finset.expect_sum_comm _ _ fun i k => φ k i

theorem avg_comm {κ : Type} [Fintype κ] (φ : ι → κ → ℝ) :
    avg (fun i => avg (φ i)) = avg (fun k => avg (fun i => φ i k)) :=
  Finset.expect_comm _ _ φ

theorem avg_double [Nonempty ι] (φ ψ : ι → ℝ) : avg (Sum.elim φ ψ) = (avg φ + avg ψ) / 2 := by
  have h : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avg_eq_sum_div_card, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
    Fintype.card_sum, Nat.cast_add]
  field_simp
  ring

end avg

end AlmostInvariant
