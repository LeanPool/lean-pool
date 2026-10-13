/-
Copyright (c) 2026 Scott Armstrong, Tuomo Kuusi. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Tuomo Kuusi
-/

module

public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.Analysis.Complex.ExponentialBounds
public import Mathlib.Basic.ENNReal.Real

/-!
# Numerics

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section

/-!
# Elementary numerical facts for the percolation estimates

The ABK26 percolation estimates of `s.percolation.estimate` are quantitative:
every bound is an explicit exponential in the scale parameters.  This module
collects the small real-analysis facts that the quantitative modules
`Induction.lean` and `DiameterBound.lean` share, so that the probabilistic
arguments there are not interleaved with numerical bookkeeping.

Three groups of statements appear.

* Crude numerical bounds on `log 3` and on powers of three. Only `1 ≤ log 3`
  and `log 3 ≤ 2` are ever used, which keeps every downstream constant rational.
* Monotonicity and the tangent-line bound for the real power `3 ^ x`, and the
  fact that two exponentials whose exponents are one unit below a common value
  sum to at most the exponential of that value.

## References

* ABK26, `s.percolation.estimate`.
-/

namespace Algsuperdiff.Section3.Provider.Percolation

/-! ### Elementary numerical facts -/

theorem one_le_log_three : (1 : ℝ) ≤ Real.log 3 := by
  rw [Real.le_log_iff_exp_le (by norm_num : (0 : ℝ) < 3)]
  have h : Real.exp 1 < 2.7182818286 := Real.exp_one_lt_d9
  norm_num at h ⊢
  linarith

theorem log_three_le_two : Real.log 3 ≤ 2 := by
  have h := Real.log_le_sub_one_of_pos (by norm_num : (0 : ℝ) < 3)
  linarith

theorem succ_le_three_pow (n : ℕ) : n + 1 ≤ 3 ^ n := by
  induction n with
  | zero => norm_num
  | succ m ih =>
      have hstep : (3 : ℕ) ^ (m + 1) = 3 ^ m * 3 := pow_succ 3 m
      omega

theorem one_le_three_rpow {x : ℝ} (hx : 0 ≤ x) : (1 : ℝ) ≤ (3 : ℝ) ^ x := by
  have h := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num) hx
  rwa [Real.rpow_zero] at h

theorem three_rpow_le_one {x : ℝ} (hx : x ≤ 0) : (3 : ℝ) ^ x ≤ 1 := by
  have h := Real.rpow_le_rpow_of_exponent_le (x := (3 : ℝ)) (by norm_num) hx
  rwa [Real.rpow_zero] at h

theorem one_add_le_three_rpow {x : ℝ} (hx : 0 ≤ x) : 1 + x ≤ (3 : ℝ) ^ x := by
  have hexp := Real.add_one_le_exp (Real.log 3 * x)
  have hmul : x ≤ Real.log 3 * x := by nlinarith [one_le_log_three]
  rw [Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3)]
  linarith

theorem exp_natMul (M : ℕ) (E : ℝ) : Real.exp ((M : ℝ) * E) = Real.exp E ^ M := by
  induction M with
  | zero => simp
  | succ m ih =>
      have hcast : ((m + 1 : ℕ) : ℝ) * E = (m : ℝ) * E + E := by push_cast; ring
      rw [hcast, Real.exp_add, ih, pow_succ]

/-- Two exponentials, each at least one unit below the target exponent, sum to at
most the target exponential. -/
theorem exp_add_exp_le {E₁ E₂ G : ℝ} (h₁ : E₁ + 1 ≤ G) (h₂ : E₂ + 1 ≤ G) :
    Real.exp E₁ + Real.exp E₂ ≤ Real.exp G := by
  have he : (2 : ℝ) ≤ Real.exp 1 := by linarith [Real.add_one_le_exp (1 : ℝ)]
  have hb : ∀ E : ℝ, E + 1 ≤ G → Real.exp E ≤ Real.exp G / 2 := by
    intro E hE
    have h1 : Real.exp E * Real.exp 1 = Real.exp (E + 1) := (Real.exp_add E 1).symm
    have h2 : Real.exp (E + 1) ≤ Real.exp G := Real.exp_le_exp.mpr hE
    have h3 : 0 < Real.exp E := Real.exp_pos E
    nlinarith
  linarith [hb E₁ h₁, hb E₂ h₂]

/-! ### Passing between products and real exponentials -/

theorem exp_natMul_log_three (n : ℕ) :
    Real.exp ((n : ℝ) * Real.log 3) = (3 : ℝ) ^ n := by
  rw [mul_comm, ← Real.rpow_def_of_pos (by norm_num : (0 : ℝ) < 3), Real.rpow_natCast]

theorem enn_three_pow (n : ℕ) :
    (3 : ENNReal) ^ n = ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 3)) := by
  rw [exp_natMul_log_three, ENNReal.ofReal_pow (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

theorem enn_mul_ofReal_exp (n : ℕ) (P : ℝ) :
    (3 : ENNReal) ^ n * ENNReal.ofReal (Real.exp P)
      = ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 3 + P)) := by
  rw [enn_three_pow, ← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]

theorem enn_pow_ofReal_exp (M : ℕ) (E : ℝ) :
    ENNReal.ofReal (Real.exp E) ^ M = ENNReal.ofReal (Real.exp ((M : ℝ) * E)) := by
  rw [exp_natMul, ENNReal.ofReal_pow (Real.exp_nonneg _)]

theorem enn_three_pow_mul_natCast_mul_le (n m : ℕ) (Q : ℝ) :
    (3 : ENNReal) ^ n * (m : ENNReal) * ENNReal.ofReal (Real.exp Q)
      ≤ ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 3 + (m : ℝ) + Q)) := by
  have hm : (m : ENNReal) ≤ ENNReal.ofReal (Real.exp (m : ℝ)) := by
    rw [← ENNReal.ofReal_natCast]
    exact ENNReal.ofReal_le_ofReal (by linarith [Real.add_one_le_exp (m : ℝ)])
  calc (3 : ENNReal) ^ n * (m : ENNReal) * ENNReal.ofReal (Real.exp Q)
      ≤ (3 : ENNReal) ^ n * ENNReal.ofReal (Real.exp (m : ℝ))
          * ENNReal.ofReal (Real.exp Q) := by gcongr
    _ = ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 3 + (m : ℝ)))
          * ENNReal.ofReal (Real.exp Q) := by rw [enn_mul_ofReal_exp]
    _ = ENNReal.ofReal (Real.exp ((n : ℝ) * Real.log 3 + (m : ℝ) + Q)) := by
        rw [← ENNReal.ofReal_mul (Real.exp_nonneg _), ← Real.exp_add]

end Algsuperdiff.Section3.Provider.Percolation
