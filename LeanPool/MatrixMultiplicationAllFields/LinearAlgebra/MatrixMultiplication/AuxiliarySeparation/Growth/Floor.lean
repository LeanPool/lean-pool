/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import Mathlib.Analysis.SpecificLimits.Basic
public import Mathlib.Analysis.SpecialFunctions.Log.Base
public import Mathlib.Analysis.SpecialFunctions.Pow.Continuity

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Growth rates of floor-rounded exponents

The integer exponents obtained by rounding a nonnegative multiple of the tensor
power have the intended normalized growth rate. Applying a positive base to
these exponents preserves that rate after taking roots.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields



namespace MatrixMultiplication.AuxiliarySeparation

open Filter
open scoped Topology

/-- Rounding a nonnegative linear exponent down has vanishing normalized error. -/
theorem tendsto_floor_mul_div {c : ℝ} (hc : 0 ≤ c) :
    Tendsto (fun j : ℕ => (⌊(j : ℝ) * c⌋₊ : ℝ) / (j : ℝ))
      atTop (𝓝 c) := by
  simpa only [Function.comp_def, mul_comm] using
    (tendsto_nat_floor_mul_div_atTop hc).comp
      (tendsto_natCast_atTop_atTop (R := ℝ))

/-- A floor-rounded exponent diverges when its linear coefficient is positive. -/
theorem tendsto_floor_mul_atTop {c : ℝ} (hc : 0 < c) :
    Tendsto (fun j : ℕ => ⌊(j : ℝ) * c⌋₊) atTop atTop := by
  simpa only [mul_comm] using tendsto_nat_floor_mul_atTop c hc

/-- The root growth rate of powers with floor-rounded exponents. -/
theorem tendsto_pow_floor_rpow_inv {u c : ℝ} (hu : 0 < u) (hc : 0 ≤ c) :
    Tendsto (fun j : ℕ => (u ^ ⌊(j : ℝ) * c⌋₊) ^ (1 / (j : ℝ)))
      atTop (𝓝 (u ^ c)) := by
  have h := (Real.continuousAt_const_rpow hu.ne').tendsto.comp
    (tendsto_floor_mul_div hc)
  convert h using 1
  funext j
  simp only [Function.comp_def, div_eq_mul_inv, one_mul]
  rw [Real.rpow_mul hu.le, Real.rpow_natCast]

/-- The logarithmic choice of exponent gives the prescribed root growth rate.
In the tensor application, `s` is the exponent bound with a positive slack. -/
theorem tendsto_pow_floor_logb_div_rpow_inv {u n s : ℝ}
    (hu : 1 < u) (hn : 1 ≤ n) (hs : 0 < s) :
    Tendsto
      (fun j : ℕ => (u ^ ⌊(j : ℝ) * (Real.logb u n / s)⌋₊) ^ (1 / (j : ℝ)))
      atTop (𝓝 (n ^ (1 / s))) := by
  have hu₀ : 0 < u := zero_lt_one.trans hu
  have hn₀ : 0 < n := zero_lt_one.trans_le hn
  have h := tendsto_pow_floor_rpow_inv hu₀
    (div_nonneg (Real.logb_nonneg hu hn) hs.le)
  have hrate : u ^ (Real.logb u n / s) = n ^ (1 / s) := by
    rw [div_eq_mul_inv, Real.rpow_mul hu₀.le, Real.rpow_logb hu₀ hu.ne' hn₀,
      one_div]
  rw [hrate] at h
  exact h

end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
