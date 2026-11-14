/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real

/-!
# SepEnvelope

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Logarithmic square-root estimates

This module contains the elementary real inequalities used to absorb the
logarithmic factor in the deterministic separation envelope.  The estimates
reduce the calculation to `-(t log t) ≤ 1` and then apply it at an eighth root.

## Main results

* `Algsuperdiff.Probability.neg_mul_log_le_one`
* `Algsuperdiff.Probability.gamma_quarter_log_sq_le`
* `Algsuperdiff.Probability.sqrt_mul_log_sq_le_quarter`

## References

* ABK26, `l.minimal.scale.sep`.
-/

namespace Algsuperdiff.Probability

variable {cstar s γ C K L Cbig t : ℝ}

/-- `-(t log t) ≤ 1` for every `t > 0` (on `(0,1]` this is the useful half of
`|t log t| ≤ 1`). Proof: `t·(-log t) ≤ t·(t⁻¹ − 1) = 1 − t ≤ 1`. -/
theorem neg_mul_log_le_one (ht : 0 < t) : -(t * Real.log t) ≤ 1 := by
  have h1 : Real.log t⁻¹ ≤ t⁻¹ - 1 := Real.log_le_sub_one_of_pos (inv_pos.mpr ht)
  rw [Real.log_inv] at h1
  have h2 : t * -Real.log t ≤ t * (t⁻¹ - 1) := mul_le_mul_of_nonneg_left h1 ht.le
  have h3 : t * (t⁻¹ - 1) = 1 - t := by rw [mul_sub, mul_inv_cancel₀ ht.ne', mul_one]
  linarith only [h2, h3, ht.le]

/-- The `t = γ^{1/8}` core of `gamma_quarter_log_sq_le`, over abstract reals: for
`t ∈ (0,1]`, `t² · (8 log t)² = 64 (t log t)² ≤ 64`. -/
theorem quarter_log_sq_aux (ht : 0 < t) (ht1 : t ≤ 1) :
    t * t * (8 * Real.log t) ^ 2 ≤ 64 := by
  have hlog : Real.log t ≤ 0 := Real.log_nonpos ht.le ht1
  have h0 : 0 ≤ -(t * Real.log t) := by
    have h := mul_nonneg ht.le (neg_nonneg.mpr hlog)
    linarith only [h]
  have h1 : -(t * Real.log t) ≤ 1 := neg_mul_log_le_one ht
  have h2 : (-(t * Real.log t)) ^ 2 ≤ 1 := pow_le_one₀ h0 h1
  have h3 : t * t * (8 * Real.log t) ^ 2 = 64 * (-(t * Real.log t)) ^ 2 := by ring
  linarith only [h2, h3]

/-- **The scale-free log bound.** `γ^{1/4} (log γ)² ≤ 64` for `γ ∈ (0,1]`. -/
theorem gamma_quarter_log_sq_le (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    γ ^ ((1 : ℝ) / 4) * (Real.log γ) ^ 2 ≤ 64 := by
  have ht : (0 : ℝ) < γ ^ ((1 : ℝ) / 8) := Real.rpow_pos_of_pos hγ _
  have ht1 : γ ^ ((1 : ℝ) / 8) ≤ 1 := Real.rpow_le_one hγ.le hγ1 (by norm_num)
  have hlog : Real.log (γ ^ ((1 : ℝ) / 8)) = 1 / 8 * Real.log γ := Real.log_rpow hγ _
  have hqq : γ ^ ((1 : ℝ) / 8) * γ ^ ((1 : ℝ) / 8) = γ ^ ((1 : ℝ) / 4) := by
    rw [← Real.rpow_add hγ, show (1 : ℝ) / 8 + (1 : ℝ) / 8 = (1 : ℝ) / 4 by norm_num]
  have h := quarter_log_sq_aux ht ht1
  rw [hqq, hlog, show (8 : ℝ) * (1 / 8 * Real.log γ) = Real.log γ by ring] at h
  exact h

/-- `√γ = γ^{1/4} · γ^{1/4}`. -/
theorem sqrt_eq_quarter_mul_quarter (hγ : 0 < γ) :
    Real.sqrt γ = γ ^ ((1 : ℝ) / 4) * γ ^ ((1 : ℝ) / 4) := by
  rw [Real.sqrt_eq_rpow, ← Real.rpow_add hγ,
    show (1 : ℝ) / 4 + (1 : ℝ) / 4 = 1 / (2 : ℝ) by norm_num]

/-- `√γ (log γ)² ≤ 64 γ^{1/4}` on `(0,1]`. -/
theorem sqrt_mul_log_sq_le_quarter (hγ : 0 < γ) (hγ1 : γ ≤ 1) :
    Real.sqrt γ * (Real.log γ) ^ 2 ≤ 64 * γ ^ ((1 : ℝ) / 4) := by
  have h := gamma_quarter_log_sq_le hγ hγ1
  have hq0 : (0 : ℝ) ≤ γ ^ ((1 : ℝ) / 4) := Real.rpow_nonneg hγ.le _
  calc Real.sqrt γ * (Real.log γ) ^ 2
      = γ ^ ((1 : ℝ) / 4) * (γ ^ ((1 : ℝ) / 4) * (Real.log γ) ^ 2) := by
        rw [sqrt_eq_quarter_mul_quarter hγ]; ring
    _ ≤ γ ^ ((1 : ℝ) / 4) * 64 := mul_le_mul_of_nonneg_left h hq0
    _ = 64 * γ ^ ((1 : ℝ) / 4) := mul_comm _ _

end Algsuperdiff.Probability
