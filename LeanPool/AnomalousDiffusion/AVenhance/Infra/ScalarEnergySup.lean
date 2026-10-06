/-
Copyright (c) 2026 Scott Armstrong and Vlad Vicol. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong and Vlad Vicol
-/
module

public import Mathlib.Basic.Real.Basic
public import Mathlib.Tactic.FieldSimp
public import Mathlib.Tactic.Linarith

/-! Supremum absorption for scalar energy estimates. -/

@[expose] public section

noncomputable section

open Set

namespace AVenhance.Infra.ScalarEnergySup

/-- Absorb an attained supremum from a quadratic energy bound. -/
theorem cell_sup_le_of_quadratic_bound
    {f : ℝ → ℝ} {cell : Set ℝ} {H L D : ℝ}
    (hnonneg : ∀ t ∈ cell, 0 ≤ f t)
    (hLD : 0 ≤ L * D)
    (hFTC : ∀ t ∈ cell, f t ^ 2 ≤ 2 * L * D * H)
    (hH : ∃ t₀ ∈ cell, H = f t₀ ∧ ∀ t ∈ cell, f t ≤ f t₀) :
    ∀ t ∈ cell, f t ≤ 2 * L * D := by
  obtain ⟨t₀, ht₀, hHval, hmax⟩ := hH
  have hHnonneg : 0 ≤ H := by rw [hHval]; exact hnonneg t₀ ht₀
  have hupper : ∀ t ∈ cell, f t ≤ H := by
    intro t ht
    rw [hHval]
    exact hmax t ht
  by_cases hHzero : H = 0
  · intro t ht
    have hle := hupper t ht
    have hge := hnonneg t ht
    rw [hHzero] at hle
    have hzero : f t = 0 := le_antisymm hle hge
    rw [hzero]
    nlinarith [hLD]
  · have hHpos : 0 < H := lt_of_le_of_ne hHnonneg (Ne.symm hHzero)
    have hHFTC : H ^ 2 ≤ 2 * L * D * H := by
      rw [hHval]
      have h := hFTC t₀ ht₀
      rw [hHval] at h
      exact h
    have habsorb : H ≤ 2 * L * D := by
      have hdiv := div_le_div_of_nonneg_right hHFTC (le_of_lt hHpos)
      have hleft : H ^ 2 / H = H := by field_simp [hHpos.ne']
      have hright : (2 * L * D * H) / H = 2 * L * D := by
        field_simp [hHpos.ne']
      rw [hleft, hright] at hdiv
      exact hdiv
    intro t ht
    exact (hupper t ht).trans habsorb

end AVenhance.Infra.ScalarEnergySup
