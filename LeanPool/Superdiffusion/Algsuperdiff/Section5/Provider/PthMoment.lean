/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/

module

public import LeanPool.Superdiffusion.Algsuperdiff.Section3.Provider.Orlicz.WeightedSubgaussian
public import LeanPool.Superdiffusion.Algsuperdiff.Section5.Provider.EarlyExitPrinted

/-!
# PthMoment

Ported from scottnarmstrong/Superdiffusion at 7f20476385d4af418f110303085ad0740c9eba46.
Module imports, support namespace and local option directives adapted for Lean Pool.
-/

@[expose] public section


/-!
# Moment integration for the displacement tail

This module isolates the integration step behind ABK26
`e.pth.moment.process`.  A normalized exponential tail gives the displayed
`p^p` moment dependence with the explicit constant `6`.
-/

namespace Algsuperdiff.Section5.Provider

open MeasureTheory
open HCPolySupport MarkovProcess
open scoped ENNReal

noncomputable section

variable {Omega : Type*} [MeasurableSpace Omega]

/-- A nonnegative random variable with tail at most `2 exp (-s)` has moments
bounded by `(6p)^p`, for every real exponent `p >= 1`. -/
theorem integral_rpow_le_of_exp_tail (mu : Measure Omega) [IsProbabilityMeasure mu]
    {W : Omega → ℝ} (hW : AEMeasurable W mu) (hWnn : 0 ≤ᵐ[mu] W)
    (htail : ∀ s : ℝ, 0 < s → mu.real {omega | s < W omega} ≤ 2 * Real.exp (-s))
    {p : ℝ} (hp : 1 ≤ p) :
    Integrable (fun omega => W omega ^ p) mu ∧
      ∫ omega, W omega ^ p ∂mu ≤ (6 * p) ^ p := by
  obtain ⟨hexpInt, hexp⟩ :=
    Algsuperdiff.Section3.Provider.Orlicz.integral_exp_smul_le_of_tail hW hWnn htail
      (l := (1 / 2 : ℝ)) (by norm_num) (by norm_num)
  have hpoint : ∀ᵐ omega ∂mu,
      W omega ^ p ≤ (2 * p) ^ p * Real.exp ((1 / 2 : ℝ) * W omega) := by
    filter_upwards [hWnn] with omega homega
    have hpnonneg : 0 ≤ p := le_trans zero_le_one hp
    have hraw := ProbabilityTheory.rpow_abs_le_mul_exp_abs (W omega) hpnonneg
      (show (1 / 2 : ℝ) ≠ 0 by norm_num)
    have habs : |(1 / 2 : ℝ)| = 1 / 2 := abs_of_pos (by norm_num)
    have hdiv : p / (1 / 2 : ℝ) = 2 * p := by ring
    rw [abs_of_nonneg homega, habs, hdiv] at hraw
    exact hraw
  have hp0 : 0 < p := lt_of_lt_of_le zero_lt_one hp
  have hfactor : 0 ≤ (2 * p) ^ p := Real.rpow_nonneg (by positivity) _
  have hdomInt : Integrable (fun omega =>
      (2 * p) ^ p * Real.exp ((1 / 2 : ℝ) * W omega)) mu := hexpInt.const_mul _
  have hpointNorm : ∀ᵐ omega ∂mu,
      ‖W omega ^ p‖ ≤ (2 * p) ^ p * Real.exp ((1 / 2 : ℝ) * W omega) := by
    filter_upwards [hWnn, hpoint] with omega hWnonneg homega
    rw [Real.norm_of_nonneg (Real.rpow_nonneg hWnonneg p)]
    exact homega
  have hpowInt : Integrable (fun omega => W omega ^ p) mu :=
    hdomInt.mono' (hW.pow_const p).aestronglyMeasurable hpointNorm
  refine ⟨hpowInt, ?_⟩
  calc
    ∫ omega, W omega ^ p ∂mu ≤
        ∫ omega, (2 * p) ^ p * Real.exp ((1 / 2 : ℝ) * W omega) ∂mu :=
      integral_mono_ae hpowInt hdomInt hpoint
    _ = (2 * p) ^ p * ∫ omega, Real.exp ((1 / 2 : ℝ) * W omega) ∂mu :=
      MeasureTheory.integral_const_mul _ _
    _ ≤ (2 * p) ^ p * 3 := by
      refine mul_le_mul_of_nonneg_left ?_ hfactor
      norm_num at hexp ⊢
      exact hexp
    _ ≤ (6 * p) ^ p := by
      have hthree : (3 : ℝ) ≤ 3 ^ p := by
        calc
          (3 : ℝ) = (3 : ℝ) ^ (1 : ℝ) := (Real.rpow_one 3).symm
          _ ≤ (3 : ℝ) ^ p :=
            Real.rpow_le_rpow_of_exponent_le (x := 3) (by norm_num) hp
      calc
        (2 * p) ^ p * 3 ≤ (2 * p) ^ p * 3 ^ p := mul_le_mul_of_nonneg_left hthree hfactor
        _ = (6 * p) ^ p := by
          rw [← Real.mul_rpow (by positivity : (0 : ℝ) ≤ 2 * p) (by norm_num : (0 : ℝ) ≤ 3)]
          congr 1
          ring

end

end Algsuperdiff.Section5.Provider
