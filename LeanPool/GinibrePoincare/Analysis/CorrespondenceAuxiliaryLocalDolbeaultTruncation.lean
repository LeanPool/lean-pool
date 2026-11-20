/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/CorrespondenceAuxiliaryLocalDolbeaultTruncation.lean.
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
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceAuxiliaryLocalDolbeaultLpIteration
public import LeanPool.GinibrePoincare.Analysis.CorrespondenceDolbeaultYoungSmooth

/-!
# Correspondence auxiliary local Dolbeault truncation

Part of the complex Gaussian and Hermite analysis development of the
Ginibre Poincaré formalization.

Main results: `dolbeaultTruncatedCutoff_eq`, `dolbeaultTruncatedCutoff_smooth_compact`,
`dolbeaultCutoffLpOperator_smooth_representative`.
-/

@[expose] public section
open MeasureTheory Set Filter Metric
open scoped ContDiff Convolution Topology
namespace GinibrePoincare
noncomputable section

theorem dolbeaultReplaceCoordinate_shift {n : ℕ} (j : Fin n)
    (p : Configuration n) (y : ℂ) :
    dolbeaultReplaceCoordinate j (p, p j-y) = p-Pi.single j y := by
  ext k
  by_cases hk : k = j
  · subst k; simp [dolbeaultReplaceCoordinate_apply]
  · simp [dolbeaultReplaceCoordinate_apply, hk]

/-- Convolution in the `j`-th coordinate of `p ↦ χ (p j) * a p` with the Cauchy–Green kernel
truncated to the closed ball of radius `R`. -/
def dolbeaultTruncatedCutoff {n : ℕ} (j : Fin n) (R : ℝ) (χ : ℂ → ℂ)
    (a : Configuration n → ℂ) : Configuration n → ℂ :=
  dolbeaultCoordinateConvolutionPointwise j (dolbeaultTruncatedCauchyGreen R)
    (fun p => χ (p j)*a p)

theorem dolbeaultTruncatedCutoff_eq {n : ℕ} (j : Fin n) (R : ℝ) (χ : ℂ → ℂ)
    (a : Configuration n → ℂ) (p : Configuration n)
    (hR : ∀ z ∈ tsupport χ, ‖p j - z‖ ≤ R) :
    dolbeaultTruncatedCutoff j R χ a p = configurationCauchyGreenPotential j χ a p := by
  change (∫ y : ℂ, dolbeaultTruncatedCauchyGreen R y *
      (χ ((p-Pi.single j y : Configuration n) j)*a (p-Pi.single j y))) =
    ∫ y : ℂ, cauchyGreenKernel y * (χ (p j-y)*a (dolbeaultReplaceCoordinate j (p, p j-y)))
  apply integral_congr_ae
  exact ae_of_all _ (fun y => by
    change dolbeaultTruncatedCauchyGreen R y *
      (χ ((p-Pi.single j y : Configuration n) j)*a (p-Pi.single j y)) =
        cauchyGreenKernel y * (χ (p j-y)*a (dolbeaultReplaceCoordinate j (p, p j-y)))
    rw [dolbeaultReplaceCoordinate_shift]
    simp only [Pi.sub_apply, Pi.single_eq_same]
    by_cases hy : p j-y ∈ tsupport χ
    · have hb : y ∈ closedBall (0 : ℂ) R := by
        have hh := hR (p j-y) hy
        simpa only [sub_sub_cancel, mem_closedBall, dist_zero_right] using hh
      rw [dolbeaultTruncatedCauchyGreen, indicator_of_mem hb]
    · rw [image_eq_zero_of_notMem_tsupport hy, zero_mul, mul_zero, mul_zero])

theorem dolbeaultTruncatedCutoff_smooth_compact {n : ℕ} (j : Fin n) (R : ℝ)
    (χ : ℂ → ℂ) (a : Configuration n → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    ContDiff ℝ ∞ (dolbeaultTruncatedCutoff j R χ a) ∧
      HasCompactSupport (dolbeaultTruncatedCutoff j R χ a) := by
  have hf : ContDiff ℝ ∞ (fun p : Configuration n => χ (p j)*a p) :=
    (hχ.comp (contDiff_apply ℝ (fun _ => ℂ) j)).mul ha
  have hcf : HasCompactSupport (fun p : Configuration n => χ (p j)*a p) := hc.mul_left
  exact ⟨(dolbeaultCauchyGreenL2_smooth_compact_representative j R _ hf hcf).1,
    (dolbeaultCauchyGreenL2_smooth_compact_representative j R _ hf hcf).2.1⟩

theorem dolbeaultCutoffLpOperator_smooth_representative {n : ℕ} (j : Fin n) (R : ℝ)
    (χ : ℂ → ℂ) (a : Configuration n → ℂ)
    (hχ : ContDiff ℝ ∞ χ) (hcχ : HasCompactSupport χ)
    (ha : ContDiff ℝ ∞ a) (hc : HasCompactSupport a) :
    (dolbeaultCutoffLpOperator j R χ hχ.continuous hcχ
      ((ha.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hc).toLp a)
        : Configuration n → ℂ) =ᵐ[volume] dolbeaultTruncatedCutoff j R χ a := by
  let hm := ha.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hc
  let f : Configuration n → ℂ := fun p => χ (p j)*a p
  have hf : ContDiff ℝ ∞ f := (hχ.comp (contDiff_apply ℝ (fun _ => ℂ) j)).mul ha
  have hcf : HasCompactSupport f := hc.mul_left
  let hmf := hf.continuous.memLp_of_hasCompactSupport (p := 2) (μ := volume) hcf
  have he : dolbeaultCutoffLpMultiplier j χ hχ.continuous hcχ (hm.toLp a) = hmf.toLp f := by
    apply Lp.ext
    have hb := dolbeaultBoundedMultiplier_ae (fun p : Configuration n => χ (p j))
      ((hχ.continuous.comp (continuous_apply j)).aestronglyMeasurable)
      (dolbeaultCompactBound χ hχ.continuous hcχ)
      (ae_of_all _ (fun p => dolbeaultCompactBound_spec χ hχ.continuous hcχ (p j))) (hm.toLp a)
    filter_upwards [hb, hm.coeFn_toLp, hmf.coeFn_toLp] with p h1 h2 h3
    change (dolbeaultBoundedMultiplierValue (fun p : Configuration n => χ (p j))
      ((hχ.continuous.comp (continuous_apply j)).aestronglyMeasurable)
      (dolbeaultCompactBound χ hχ.continuous hcχ)
      (ae_of_all _ (fun p => dolbeaultCompactBound_spec χ hχ.continuous hcχ (p j)))
        (hm.toLp a)) p = (hmf.toLp f) p
    rw [h1, h3, h2]
  change (dolbeaultCauchyGreenL2 j R
    (dolbeaultCutoffLpMultiplier j χ hχ.continuous hcχ (hm.toLp a)) : Configuration n → ℂ)
        =ᵐ[volume] _
  rw [he]
  exact (dolbeaultCauchyGreenL2_smooth_compact_representative j R f hf hcf).2.2

end
end GinibrePoincare
