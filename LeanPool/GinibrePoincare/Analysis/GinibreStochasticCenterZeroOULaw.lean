/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/GinibreStochasticCenterZeroOULaw.lean.
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

public import LeanPool.GinibrePoincare.Analysis.GinibreStochasticCenterZeroGaussian
public import LeanPool.GinibrePoincare.Analysis.GinibreDrivenPathOUProjection

/-! Gaussian real center laws of the genuine n-particle original process,
including zero initial center and every positive time. -/

@[expose] public section
open MeasureTheory ProbabilityTheory Filter
open scoped NNReal Topology
namespace GinibrePoincare
noncomputable section

/-- The rate `2α/n` of the center-of-mass Ornstein–Uhlenbeck process. -/
def ginibreCenterOURate (n : ℕ) (α : ℝ≥0) : ℝ≥0 := 2*α/n

@[simp] theorem ginibreCenterOURate_coe (n : ℕ) (α : ℝ≥0) :
    (ginibreCenterOURate n α : ℝ)=2*(α : ℝ)/(n : ℝ) := by
  simp [ginibreCenterOURate]

theorem ginibre_center_noise_scaling {n : ℕ} (hn : 0 < n) (α : ℝ≥0) :
    Real.sqrt (2*(α : ℝ)/(n : ℝ)^2) =
      Real.sqrt (ginibreCenterOURate n α : ℝ)*(Real.sqrt (n : ℝ))⁻¹ := by
  have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
  have hsn : Real.sqrt (n : ℝ) ≠ 0 := (Real.sqrt_pos.mpr hnR).ne'
  have ha : (Real.sqrt (2*(α : ℝ)/(n : ℝ)^2))^2 = 2*(α : ℝ)/(n : ℝ)^2 := Real.sq_sqrt (div_nonneg
      (mul_nonneg (by norm_num) α.coe_nonneg) (sq_nonneg (n : ℝ)))
  have hb : (Real.sqrt (ginibreCenterOURate n α : ℝ))^2 = (ginibreCenterOURate n α : ℝ) :=
      Real.sq_sqrt (ginibreCenterOURate n α).coe_nonneg
  have hc := Real.sq_sqrt hnR.le
  have hsq : (Real.sqrt (ginibreCenterOURate n α : ℝ)*(Real.sqrt (n : ℝ))⁻¹)^2 =
      2*(α : ℝ)/(n : ℝ)^2 := by
    rw [mul_pow, inv_pow, hb, hc, ginibreCenterOURate_coe]
    field_simp
  nlinarith [Real.sqrt_nonneg (2*(α : ℝ)/(n : ℝ)^2),
    mul_nonneg (Real.sqrt_nonneg (ginibreCenterOURate n α : ℝ)) (inv_nonneg.mpr (Real.sqrt_nonneg (n
        : ℝ)))]

theorem ginibreBrownian_center_real_OU
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (coordinateSum (ginibreBrownianMaximalProcess n α z B t ω)).re =
        ginibreBrownianOU (ginibreNormalizedCenterBrownian n 0 B)
          (ginibreCenterOURate n α) (Real.sqrt (ginibreCenterOURate n α : ℝ))
          (coordinateSum z).re t ω := by
  filter_upwards [ginibreBrownian_center_OU_factorization hn α z hz B P hB hind,
    ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hcenter hnoise
  let N := ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω)
  have he : (fun s : ℝ => Complex.reCLM (N s)) =
      ginibreBrownianNoise (ginibreNormalizedCenterBrownian n 0 B)
        (Real.sqrt (ginibreCenterOURate n α : ℝ)) ω := by
    funext s
    change (coordinateSumCLM n ((ginibreBrownianFullContinuousNoise n B α ω).val s)).re = _
    rw [coordinateSumCLM_apply, hnoise s]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hns : Real.sqrt (n : ℝ)/(n : ℝ) = (Real.sqrt (n : ℝ))⁻¹ := by
      have hs := (Real.sqrt_pos.mpr hnR).ne'
      field_simp
      nlinarith [Real.sq_sqrt hnR.le]
    simp [hns, coordinateSum, ginibreConfigurationBrownianNoise, ginibreBrownianNoise,
      ginibreNormalizedCenterBrownian,← Finset.mul_sum, ginibre_center_noise_scaling hn α,
      mul_assoc]
  intro t
  rw [hcenter t]
  have hh := drivenOUPath_continuousLinearMap Complex.reCLM (2*(α : ℝ)/(n : ℝ))
    (coordinateSum z) N N.continuous (t : ℝ)
  rw [he] at hh
  simpa [ginibreCenterOUValue, N, ginibreBrownianOU, ginibreCenterOURate_coe, Complex.reCLM] using
      hh

theorem ginibreBrownian_center_imag_OU
    {Ω : Type*} [MeasurableSpace Ω] {n : ℕ} (hn : 0 < n) (α : ℝ≥0)
    (z : Configuration n) (hz : CollisionFree z)
    (B : (Fin n × Fin 2) → ℝ≥0 → Ω → ℝ) (P : Measure Ω)
    [IsProbabilityMeasure P] [P.IsComplete] (hB : ∀ i, IsBrownianReal (B i) P)
    (hind : iIndepFun (fun i ω t => B i t ω) P) :
    ∀ᵐ ω ∂P, ∀ t : ℝ≥0,
      (coordinateSum (ginibreBrownianMaximalProcess n α z B t ω)).im =
        ginibreBrownianOU (ginibreNormalizedCenterBrownian n 1 B)
          (ginibreCenterOURate n α) (Real.sqrt (ginibreCenterOURate n α : ℝ))
          (coordinateSum z).im t ω := by
  filter_upwards [ginibreBrownian_center_OU_factorization hn α z hz B P hB hind,
    ginibreBrownianFullContinuousNoise_ae n B P hB α] with ω hcenter hnoise
  let N := ginibreContinuousNoiseCenter n (ginibreBrownianFullContinuousNoise n B α ω)
  have he : (fun s : ℝ => Complex.imCLM (N s)) =
      ginibreBrownianNoise (ginibreNormalizedCenterBrownian n 1 B)
        (Real.sqrt (ginibreCenterOURate n α : ℝ)) ω := by
    funext s
    change (coordinateSumCLM n ((ginibreBrownianFullContinuousNoise n B α ω).val s)).im = _
    rw [coordinateSumCLM_apply, hnoise s]
    have hnR : 0 < (n : ℝ) := by exact_mod_cast hn
    have hns : Real.sqrt (n : ℝ)/(n : ℝ) = (Real.sqrt (n : ℝ))⁻¹ := by
      have hs := (Real.sqrt_pos.mpr hnR).ne'
      field_simp
      nlinarith [Real.sq_sqrt hnR.le]
    simp [hns, coordinateSum, ginibreConfigurationBrownianNoise, ginibreBrownianNoise,
      ginibreNormalizedCenterBrownian,← Finset.mul_sum, ginibre_center_noise_scaling hn α,
      mul_assoc]
  intro t
  rw [hcenter t]
  have hh := drivenOUPath_continuousLinearMap Complex.imCLM (2*(α : ℝ)/(n : ℝ))
    (coordinateSum z) N N.continuous (t : ℝ)
  rw [he] at hh
  simpa [ginibreCenterOUValue, N, ginibreBrownianOU, ginibreCenterOURate_coe, Complex.imCLM] using
      hh

end
end GinibrePoincare
