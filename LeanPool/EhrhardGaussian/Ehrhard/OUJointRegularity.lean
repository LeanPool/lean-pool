/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianLinearAverage
public import LeanPool.EhrhardGaussian.Ehrhard.OrnsteinUhlenbeck
import Mathlib.Analysis.Normed.Operator.Mul

/-! # Joint space-time regularity of the OU operator -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure)

namespace EhrhardGaussian.Ehrhard

/-- The affine Gaussian argument, regarded as linear in its center and scale. -/
def affineKernelLinear {n : ℕ} (z : Fin n → ℝ) :
    ((Fin n → ℝ) × ℝ) →L[ℝ] (Fin n → ℝ) :=
  ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ +
    (ContinuousLinearMap.toSpanSingleton ℝ z).comp (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ)

/-- The affine Gaussian kernel sends a center and scale to the center plus the scaled Gaussian
vector. -/
theorem affineKernelLinear_apply {n : ℕ} (z : Fin n → ℝ) (p : (Fin n → ℝ) × ℝ) :
    affineKernelLinear z p = p.1 + p.2 • z := by
  simp only [affineKernelLinear, add_apply, ContinuousLinearMap.comp_apply,
    ContinuousLinearMap.toSpanSingleton_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd']

/-- The linear map defining the affine Gaussian kernel depends continuously on the Gaussian vector.
-/
theorem continuous_affineKernelLinear {n : ℕ} : Continuous (affineKernelLinear (n := n)) := by
  change Continuous (fun z : Fin n → ℝ => ContinuousLinearMap.fst ℝ (Fin n → ℝ) ℝ +
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ (Fin n → ℝ)) z).comp
      (ContinuousLinearMap.snd ℝ (Fin n → ℝ) ℝ))
  exact continuous_const.add
    ((ContinuousLinearMap.toSpanSingletonLIE ℝ (Fin n → ℝ)).continuous.clm_comp continuous_const)

/-- The norm of the affine Gaussian kernel map is at most one plus the Gaussian vector norm. -/
theorem norm_affineKernelLinear_le {n : ℕ} (z : Fin n → ℝ) :
    ‖affineKernelLinear z‖ ≤ 1 + ‖z‖ := by
  apply ContinuousLinearMap.opNorm_le_bound _ (by positivity)
  intro p
  rw [affineKernelLinear_apply]
  calc
    ‖p.1 + p.2 • z‖ ≤ ‖p.1‖ + ‖p.2 • z‖ := norm_add_le _ _
    _ ≤ ‖p‖ + ‖p‖ * ‖z‖ := by
      rw [norm_smul]
      exact add_le_add (norm_fst_le p) (mul_le_mul_of_nonneg_right (norm_snd_le p) (norm_nonneg _))
    _ = (1 + ‖z‖) * ‖p‖ := by ring

/-- The Gaussian average is jointly `C¹` in its center and scale. -/
theorem contDiff_one_gaussianAffineAverage {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) :
    ContDiff ℝ 1 (fun p : (Fin n → ℝ) × ℝ =>
      ∫ z, F (p.1 + p.2 • z) ∂standardGaussianMeasure n) := by
  obtain ⟨C, N, hC, hbound⟩ := polynomiallySmooth_opNorm_bound hF
  have h := contDiff_one_gaussianLinearAverage hF.1 continuous_affineKernelLinear
    (L := 1) zero_le_one hC
    (fun z => by simpa only [one_mul] using norm_affineKernelLinear_le z) hbound
  simpa only [affineKernelLinear_apply] using h

/-- The literal OU integral has joint `C¹` regularity at all positive times. -/
theorem contDiffOn_ouAverage_spaceTime {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) :
    ContDiffOn ℝ 1 (fun p : ℝ × (Fin n → ℝ) => ouAverage F p.2 p.1)
      (Ioi (0 : ℝ) ×ˢ univ) := by
  let K : ℝ × (Fin n → ℝ) → (Fin n → ℝ) × ℝ := fun p =>
    (Real.exp (-p.1) • p.2, Real.sqrt (1 - Real.exp (-2 * p.1)))
  have hK : ContDiffOn ℝ 1 K (Ioi (0 : ℝ) ×ˢ univ) := by
    apply ContDiffOn.prodMk (by fun_prop)
    apply ContDiffOn.sqrt (by fun_prop : ContDiffOn ℝ 1
      (fun p : ℝ × (Fin n → ℝ) => 1 - Real.exp (-2 * p.1)) (Ioi (0 : ℝ) ×ˢ univ))
    intro p hp
    apply ne_of_gt
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    have hp0 : 0 < p.1 := hp.1
    linarith only [hp0]
  have h := (contDiff_one_gaussianAffineAverage hF).contDiffOn.comp hK (mapsTo_univ _ _)
  exact h

end EhrhardGaussian.Ehrhard

end
