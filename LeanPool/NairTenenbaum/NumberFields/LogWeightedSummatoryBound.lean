/-
Copyright (c) 2026 Jason Davies. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Jason Davies
-/

-- Modified for Lean Pool integration and compatibility maintenance.
module

public import LeanPool.NairTenenbaum.Arithmetic.SummatoryAbel

/-! # Logarithmically weighted sums under a power-saving mean estimate -/

@[expose] public section

namespace NairTenenbaum

open Finset Real MeasureTheory intervalIntegral

theorem arithmeticSummatory_log_le_of_power_error {a : ℕ → ℝ} (ha0 : a 0 = 0)
    (ha : ∀ n, 0 ≤ a n) {κ E θ x : ℝ} (hE : 0 ≤ E)
    (hbound : arithmeticSummatory a x ≤ κ * x + E * x ^ θ)
    (hθ : θ < 1) (hx : 1 ≤ x) :
    arithmeticSummatory (fun n => a n * Real.log n) x ≤
      κ * x * Real.log x + E / (1 - θ) * x := by
  have hx0 : 0 < x := lt_of_lt_of_le zero_lt_one hx
  have hc : ContinuousOn (fun t : ℝ => t⁻¹) (Set.Icc 1 x) :=
    continuousOn_id.inv₀ (fun t ht => by dsimp; linarith [ht.1])
  have hd (t : ℝ) (ht : t ∈ Set.Icc 1 x) : HasDerivAt Real.log t⁻¹ t :=
    Real.hasDerivAt_log (by linarith [ht.1])
  have H := arithmeticSummatory_mul_eq_sub_integral ha0 hx hd hc
  have hint : 0 ≤ ∫ t in (1 : ℝ)..x, t⁻¹ * arithmeticSummatory a t := by
    apply integral_nonneg hx
    intro t ht
    exact mul_nonneg (inv_nonneg.mpr (by linarith [ht.1])) (sum_nonneg (fun n _ => ha n))
  have heq : arithmeticSummatory (fun n => a n * Real.log n) x =
      arithmeticSummatory (fun n => Real.log n * a n) x := by
    apply sum_congr rfl
    intro n _
    exact mul_comm _ _
  have hpow : x ^ θ * Real.log x ≤ x / (1 - θ) := by
    calc
      _ ≤ x ^ θ * (x ^ (1 - θ) / (1 - θ)) :=
        mul_le_mul_of_nonneg_left (Real.log_le_rpow_div hx0.le (by
          linarith)) (Real.rpow_nonneg hx0.le _)
      _ = _ := by
        rw [← mul_div_assoc, ← Real.rpow_add hx0, show θ + (1 - θ) = 1 by ring, Real.rpow_one]
  rw [heq, H]
  have hb := mul_le_mul_of_nonneg_left hbound (Real.log_nonneg hx)
  have hp := mul_le_mul_of_nonneg_left hpow hE
  calc
    _ ≤ Real.log x * (κ * x + E * x ^ θ) := by linarith
    _ = κ * x * Real.log x + E * (x ^ θ * Real.log x) := by ring
    _ ≤ κ * x * Real.log x + E * (x / (1 - θ)) := add_le_add le_rfl hp
    _ = _ := by ring

end NairTenenbaum
