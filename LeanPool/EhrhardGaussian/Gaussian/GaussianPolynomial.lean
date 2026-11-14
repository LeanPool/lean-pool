/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

/-
Ported from RegularityStructures-dev, commit 852e51c64f977a7cdd3eacab66e0188bc0ed75a2.
Modified for EhrhardGaussian, 2026.
-/
module

public import LeanPool.EhrhardGaussian.Gaussian.GaussianLaw
public import Mathlib.Probability.Distributions.Gaussian.Fernique
public import Mathlib.MeasureTheory.Function.LpSeminorm.Basic
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Probability.Distributions.Gaussian.Real
public import Mathlib.MeasureTheory.Function.LpSpace.Basic
public import Mathlib.MeasureTheory.Function.LpSeminorm.CompareExp

/-! Polynomially bounded measurable functions are square integrable under Gaussian laws. -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory

namespace EhrhardGaussian.Gaussian

/-- Every nonnegative integer power of one plus the norm is square integrable under a Gaussian law.
-/
theorem memLp_one_add_norm_pow_of_gaussian {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E]
    {μ : Measure E} [IsGaussian μ] (N : ℕ) :
    MemLp (fun x : E => (1 + ‖x‖) ^ N) 2 μ := by
  induction N with
  | zero => simpa using (memLp_const (μ := μ) (p := 2) (1 : ℝ))
  | succ N ih =>
      have hid : MemLp (id : E → E) ((2 * (N + 1) : ℕ) : ENNReal) μ := by
        apply IsGaussian.memLp_id μ
        exact ENNReal.natCast_ne_top _
      have hbase : MemLp (fun x : E => 1 + ‖x‖) ((2 * (N + 1) : ℕ) : ENNReal) μ := by
        have hconst : MemLp (fun _ : E => (1 : ℝ)) ((2 * (N + 1) : ℕ) : ENNReal) μ :=
          memLp_const 1
        exact hconst.add hid.norm
      have hpow := hbase.norm_rpow_div ((N + 1 : ℕ) : ENNReal)
      have hpow' : MemLp (fun x : E => (1 + ‖x‖) ^ (N + 1 : ℕ)) 2 μ := by
        convert hpow using 1
        · funext x
          have hq : ((N + 1 : ℕ) : ENNReal).toReal = (N + 1 : ℝ) := by
            simp [ENNReal.toReal_add]
          rw [Real.norm_eq_abs, abs_of_nonneg]
          · rw [hq]
            have hq' : (↑N + 1 : ℝ) = (N + 1 : ℕ) := by norm_num
            rw [hq', Real.rpow_natCast]
          · positivity
        · have hcalc : (↑N + 1 : ENNReal)⁻¹ * (2 * (↑N + 1)) = 2 := by
            have hden : (↑N + 1 : ENNReal) ≠ 0 := by simp
            calc
              (↑N + 1 : ENNReal)⁻¹ * (2 * (↑N + 1)) =
                  2 * ((↑N + 1 : ENNReal)⁻¹ * (↑N + 1)) := by ring
              _ = 2 := by rw [ENNReal.inv_mul_cancel hden ENNReal.coe_ne_top, mul_one]
          simpa [ENNReal.div_eq_inv_mul] using hcalc.symm
      exact hpow'

/-- A measurable real function with polynomial growth is square integrable under a Gaussian law. -/
theorem memLp_of_polynomial_bound_gaussian {E : Type*} [NormedAddCommGroup E]
    [NormedSpace ℝ E] [CompleteSpace E] [SecondCountableTopology E]
    [MeasurableSpace E] [BorelSpace E] {μ : Measure E} [IsGaussian μ]
    {f : E → ℝ} (hf : AEStronglyMeasurable f μ)
    (hgrowth : ∃ C : ℝ, ∃ N : ℕ, 0 ≤ C ∧
      ∀ x : E, |f x| ≤ C * (1 + ‖x‖) ^ N) : MemLp f 2 μ := by
  rcases hgrowth with ⟨C, N, hC, hbound⟩
  have hpoly : MemLp (fun x : E => (1 + ‖x‖) ^ N) 2 μ :=
    memLp_one_add_norm_pow_of_gaussian N
  have hmajor : MemLp (fun x : E => C * (1 + ‖x‖) ^ N) 2 μ :=
    hpoly.const_mul C
  refine hmajor.mono' hf ?_
  filter_upwards [] with x
  simpa only [Real.norm_eq_abs] using hbound x


end EhrhardGaussian.Gaussian

end
