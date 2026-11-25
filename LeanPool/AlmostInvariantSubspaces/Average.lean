/-
Copyright (c) 2026 Jack Ryan. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jack Ryan
-/

/- Modified for Lean Pool. -/

module

public import Mathlib.Algebra.BigOperators.Field
public import Mathlib.Algebra.Order.BigOperators.Ring.Finset
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
noncomputable def avg {ι : Type} [Fintype ι] (φ : ι → ℝ) : ℝ := (∑ i, φ i) / (Fintype.card ι : ℝ)

section avg
variable {ι : Type} [Fintype ι]

theorem avg_add (φ ψ : ι → ℝ) : avg (fun i => φ i + ψ i) = avg φ + avg ψ := by
  simp only [avg, Finset.sum_add_distrib, add_div]

theorem avg_sub (φ ψ : ι → ℝ) : avg (fun i => φ i - ψ i) = avg φ - avg ψ := by
  simp only [avg, Finset.sum_sub_distrib, sub_div]

theorem avg_mul (c : ℝ) (φ : ι → ℝ) : avg (fun i => c * φ i) = c * avg φ := by
  simp only [avg, ← Finset.mul_sum, mul_div_assoc]

theorem avg_const [Nonempty ι] (c : ℝ) : avg (fun _ : ι => c) = c := by
  have h : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avg, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  field_simp

theorem avg_mono {φ ψ : ι → ℝ} (h : ∀ i, φ i ≤ ψ i) : avg φ ≤ avg ψ :=
  div_le_div_of_nonneg_right (Finset.sum_le_sum fun i _ => h i) (Nat.cast_nonneg _)

theorem avg_sum {κ : Type} (s : Finset κ) (φ : κ → ι → ℝ) :
    avg (fun i => ∑ k ∈ s, φ k i) = ∑ k ∈ s, avg (φ k) := by
  simp only [avg]
  rw [Finset.sum_comm, Finset.sum_div]

theorem avg_double [Nonempty ι] (φ ψ : ι → ℝ) : avg (Sum.elim φ ψ) = (avg φ + avg ψ) / 2 := by
  have h : (Fintype.card ι : ℝ) ≠ 0 := by exact_mod_cast Fintype.card_ne_zero
  simp only [avg, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Fintype.card_sum, Nat.cast_add]
  field_simp
  ring

end avg

end AlmostInvariant
