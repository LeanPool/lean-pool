/-
Copyright (c) 2026 Yimin Zhong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Yimin Zhong
-/

-- Modified for Lean Pool.

module

public import LeanPool.NoncommutativeAMGM.CosineRootNodes

/-! # Folding the full periodic cosine grid onto the Chebyshev extrema -/

@[expose] public section
namespace NoncommutativeAMGM
open scoped BigOperators

/-- Endpoint multiplicity is one, while interior cosine nodes occur twice. -/
noncomputable def cosineEndpointFactor (m j : ℕ) : ℝ := if j = 0 ∨ j = m then 1 / 2 else 1

theorem sum_reflected_grid {m : ℕ} (hm : 0 < m) (g : ℕ → ℝ)
    (hreflect : ∀ j, 1 ≤ j → j < m → g (2 * m - j) = g j) :
    (∑ j ∈ Finset.range (2 * m), g j) =
      g 0 + g m + 2 * ∑ j ∈ Finset.range (m - 1), g (j + 1) := by
  have hfirst : (∑ j ∈ Finset.range m, g j) =
      (∑ j ∈ Finset.range (m - 1), g (j + 1)) + g 0 := by
    simpa only [Nat.sub_add_cancel hm] using Finset.sum_range_succ' g (m - 1)
  have hsecond : (∑ j ∈ Finset.range m, g (m + j)) =
      (∑ j ∈ Finset.range (m - 1), g (m + (j + 1))) + g m := by
    simpa only [Nat.sub_add_cancel hm, Nat.add_zero] using
      Finset.sum_range_succ' (fun j ↦ g (m + j)) (m - 1)
  have hrev : (∑ j ∈ Finset.range (m - 1), g (m + (j + 1))) =
      ∑ j ∈ Finset.range (m - 1), g (j + 1) := by
    rw [← Finset.sum_range_reflect (fun j ↦ g (m + (j + 1))) (m - 1)]
    apply Finset.sum_congr rfl
    intro j hj
    have hjm : j < m - 1 := Finset.mem_range.mp hj
    rw [show m + (m - 1 - 1 - j + 1) = 2 * m - (j + 1) by omega]
    exact hreflect (j + 1) (by omega) (by omega)
  rw [show 2 * m = m + m by omega, Finset.sum_range_add, hfirst, hsecond, hrev]
  ring

theorem sum_endpointFactors {m : ℕ} (hm : 0 < m) (g : ℕ → ℝ) :
    (∑ j ∈ Finset.range (m + 1), cosineEndpointFactor m j * g j) =
      g 0 / 2 + g m / 2 + ∑ j ∈ Finset.range (m - 1), g (j + 1) := by
  have hfirst : (∑ j ∈ Finset.range m, cosineEndpointFactor m j * g j) =
      (∑ j ∈ Finset.range (m - 1), cosineEndpointFactor m (j + 1) * g (j + 1)) +
        cosineEndpointFactor m 0 * g 0 := by
    simpa only [Nat.sub_add_cancel hm] using
      Finset.sum_range_succ' (fun j ↦ cosineEndpointFactor m j * g j) (m - 1)
  have hinner : (∑ j ∈ Finset.range (m - 1), cosineEndpointFactor m (j + 1) * g (j + 1)) =
      ∑ j ∈ Finset.range (m - 1), g (j + 1) := by
    apply Finset.sum_congr rfl
    intro j hj
    have hjm := Finset.mem_range.mp hj
    simp [cosineEndpointFactor, show j + 1 ≠ m by omega]
  rw [Finset.sum_range_succ, hfirst, hinner]
  simp only [cosineEndpointFactor, true_or, or_true, ite_true]
  ring

theorem sum_reflected_endpointFactors {m : ℕ} (hm : 0 < m) (g : ℕ → ℝ)
    (hreflect : ∀ j, 1 ≤ j → j < m → g (2 * m - j) = g j) :
    (∑ j ∈ Finset.range (2 * m), g j) =
      2 * ∑ j ∈ Finset.range (m + 1), cosineEndpointFactor m j * g j := by
  rw [sum_reflected_grid hm g hreflect, sum_endpointFactors hm g]
  ring

/-- The even or odd half-grid has the expected endpoint/interior multiplicities. -/
theorem cosine_grid_parity_fold {m : ℕ} (hm : 0 < m) (F : ℝ → ℝ) (s : ℕ) (hs : s ≤ 1) :
    (∑ i ∈ Finset.range m, F (chebyshevNode m (2 * i + s))) =
      2 * ∑ j ∈ Finset.range (m + 1), cosineEndpointFactor m j *
        (if j % 2 = s then F (chebyshevNode m j) else 0) := by
  let g (j : ℕ) := if j % 2 = s then F (chebyshevNode m j) else 0
  have hreflect (j : ℕ) (hj : 1 ≤ j) (hjm : j < m) : g (2 * m - j) = g j := by
    have hmod : (2 * m - j) % 2 = j % 2 := by omega
    simp only [g, hmod, chebyshevNode_reflect (j := j) hm (by omega)]
  have hfull := sum_reflected_endpointFactors hm g hreflect
  have hleft : (∑ i ∈ Finset.range m, F (chebyshevNode m (2 * i + s))) =
      ∑ j ∈ Finset.range (2 * m), g j := by
    rw [sum_range_double]
    dsimp only [g]
    interval_cases s <;> simp [Nat.add_mod]
  rw [hleft]
  exact hfull

end NoncommutativeAMGM
