/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OULimits
public import LeanPool.EhrhardGaussian.Ehrhard.OUEndpointContinuity
import Mathlib.Analysis.Calculus.Deriv.MeanValue

/-! # Uniform preservation of an initial gap under small OU smoothing -/

@[expose] public noncomputable section

open Set

namespace EhrhardGaussian.Ehrhard

/-- A uniform generator bound controls the change of an Ornstein–Uhlenbeck average by elapsed time.
-/
theorem abs_ouAverage_sub_le_generator_bound {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedSecondCoordinateDerivatives F) {B M : ℝ}
    (hbound : ∀ z, |F z| ≤ B) (hgen : ∀ z, |ouGenerator F z| ≤ M)
    (x : Fin n → ℝ) {t : ℝ} (ht : 0 ≤ t) : |ouAverage F x t - F x| ≤ M * t := by
  have hcont := (continuous_ouAverage_time hF.1.continuous hbound x).continuousOn (s := Icc 0 t)
  have hder (s) (hs : s ∈ interior (Icc (0 : ℝ) t)) :
      HasDerivAt (ouAverage F x) (ouAverage (ouGenerator F) x s) s := by
    rw [interior_Icc] at hs
    exact hasDerivAt_ouAverage_generator hF x hs.1
  have hdiff : DifferentiableOn ℝ (ouAverage F x) (interior (Icc (0 : ℝ) t)) :=
    fun s hs => (hder s hs).differentiableAt.differentiableWithinAt
  have hderbound (s) (hs : s ∈ interior (Icc (0 : ℝ) t)) : |deriv (ouAverage F x) s| ≤ M := by
    rw [(hder s hs).deriv]
    exact abs_ouAverage_le hgen x s
  have hhi := (convex_Icc (0 : ℝ) t).image_sub_le_mul_sub_of_deriv_le hcont hdiff
    (fun s hs => (abs_le.mp (hderbound s hs)).2) 0 ⟨le_rfl, ht⟩ t ⟨ht, le_rfl⟩ ht
  have hlo := (convex_Icc (0 : ℝ) t).mul_sub_le_image_sub_of_le_deriv hcont hdiff
    (fun s hs => (abs_le.mp (hderbound s hs)).1) 0 ⟨le_rfl, ht⟩ t ⟨ht, le_rfl⟩ ht
  rw [ouAverage_zero, sub_zero] at hlo hhi
  exact abs_le.mpr ⟨by linarith only [hlo], hhi⟩

end EhrhardGaussian.Ehrhard

end
