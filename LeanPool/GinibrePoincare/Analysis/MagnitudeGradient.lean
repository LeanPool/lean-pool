/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MagnitudeGradient.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.RadialMagnitudeProfile

/-!
# Magnitude Gradient
-/


@[expose] public section

open MeasureTheory
open scoped BigOperators ContDiff
namespace GinibrePoincare
noncomputable section

def magnitudeDerivative {n : ℕ} (z : Configuration n) :
    Configuration n →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.pi (fun i =>
    ((z i).re / ‖z i‖) • (Complex.reCLM.comp (ContinuousLinearMap.proj i)) +
    ((z i).im / ‖z i‖) • (Complex.imCLM.comp (ContinuousLinearMap.proj i)))

theorem hasFDerivAt_magnitudeVector {n : ℕ} (z : Configuration n)
    (hz : ∀ i, z i ≠ 0) : HasFDerivAt magnitudeVector (magnitudeDerivative z) z := by
  apply hasFDerivAt_pi.mpr
  intro i
  have hr := Complex.reCLM.hasFDerivAt.comp z (ContinuousLinearMap.proj i).hasFDerivAt
  have hi := Complex.imCLM.hasFDerivAt.comp z (ContinuousLinearMap.proj i).hasFDerivAt
  have h := ((hr.mul hr).add (hi.mul hi)).sqrt
    (by simpa [Complex.normSq_apply] using (Complex.normSq_pos.mpr (hz i)).ne')
  have hn : ‖z i‖ ≠ 0 := norm_ne_zero_iff.mpr (hz i)
  convert h using 1
  · funext v
    simp only [magnitudeVector, Function.comp_apply, ContinuousLinearMap.proj_apply,
      Complex.reCLM_apply, Complex.imCLM_apply, Pi.add_apply, Pi.mul_apply]
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
  · ext v
    simp only [add_apply, smul_apply,
      ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply, Complex.reCLM_apply,
      Complex.imCLM_apply, smul_eq_mul, Function.comp_apply, Pi.add_apply, Pi.mul_apply]
    rw [← Complex.normSq_apply, Complex.normSq_eq_norm_sq, Real.sqrt_sq (norm_nonneg _)]
    field_simp
    ring

private theorem magnitudeDerivative_direction {n : ℕ} (z : Configuration n)
    (i : Fin n) (w : ℂ) :
    magnitudeDerivative z (coordinateDirection i w) =
      (((z i).re * w.re + (z i).im * w.im) / ‖z i‖) •
        (Pi.single i 1 : Fin n → ℝ) := by
  ext j
  by_cases hj : j = i
  · subst j
    simp [magnitudeDerivative, coordinateDirection]
    ring
  · simp [magnitudeDerivative, coordinateDirection, hj]

/-- Magnitude-coordinate energy has no radius weight. -/
def magnitudeEnergyDensity {n : ℕ} (F : (Fin n → ℝ) → ℝ) (r : Fin n → ℝ) : ℝ :=
  ∑ i, radiusPartial F r i ^ 2

theorem realGradientNormSq_magnitude {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : Differentiable ℝ F) (z : Configuration n) (hz : ∀ i, z i ≠ 0) :
    realGradientNormSq (fun z => F (magnitudeVector z)) z =
      magnitudeEnergyDensity F (magnitudeVector z) := by
  have hd := ((hF _).hasFDerivAt.comp z (hasFDerivAt_magnitudeVector z hz)).fderiv
  change fderiv ℝ (fun z => F (magnitudeVector z)) z = _ at hd
  unfold realGradientNormSq
  rw [hd]
  simp only [ContinuousLinearMap.comp_apply, realCoordinateDirection,
    imaginaryCoordinateDirection, magnitudeDerivative_direction, map_smul, smul_eq_mul,
    Complex.one_re, Complex.one_im, Complex.I_re, Complex.I_im, mul_one, mul_zero,
    add_zero, zero_add]
  unfold magnitudeEnergyDensity radiusPartial
  apply Finset.sum_congr rfl
  intro i hi
  have hn : ‖z i‖ ≠ 0 := norm_ne_zero_iff.mpr (hz i)
  have hs : (z i).re ^ 2 + (z i).im ^ 2 = ‖z i‖ ^ 2 := by
    simpa only [Complex.normSq_apply, pow_two] using Complex.normSq_eq_norm_sq (z i)
  field_simp
  nlinarith [hs]

theorem magnitudeEnergyDensity_symmetric {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : Differentiable ℝ F) (hS : IsSymmetricRadiusTest n F) :
    IsSymmetricRadiusTest n (magnitudeEnergyDensity F) := by
  intro σ r
  unfold magnitudeEnergyDensity
  simp only [radiusPartial_permutation F hF hS σ r]
  exact Equiv.sum_comp σ (fun i => radiusPartial F r i ^ 2)

theorem magnitudeEnergyDensity_regular {n : ℕ} (F : (Fin n → ℝ) → ℝ)
    (hF : ContDiff ℝ ∞ F) (hc : HasCompactSupport F) :
    Continuous (magnitudeEnergyDensity F) ∧ HasCompactSupport (magnitudeEnergyDensity F) := by
  constructor
  · unfold magnitudeEnergyDensity radiusPartial
    apply continuous_finsetSum
    intro i hi
    exact ((hF.continuous_fderiv (by simp)).clm_apply continuous_const).pow 2
  · apply (hc.fderiv (𝕜 := ℝ)).mono
    intro r hr hz
    apply hr
    simp [magnitudeEnergyDensity, radiusPartial, hz]

end
end GinibrePoincare
