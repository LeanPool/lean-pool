/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OUJointBounds

/-! # Concrete finite families of smoothed inputs for nonlinear interpolation -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)

namespace EhrhardGaussian.Ehrhard

/-- The vector of OU-smoothed test functions, with time as the first variable. -/
def ouFamily {n k : ℕ} (f : Fin k → (Fin n → ℝ) → ℝ) (p : ℝ × (Fin n → ℝ)) : Fin k → ℝ :=
  fun i => ouAverage (f i) p.2 p.1

/-- An Ornstein–Uhlenbeck family is continuously differentiable in space and positive time. -/
theorem contDiffOn_ouFamily {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedCoordinateDerivatives (f i)) :
    ContDiffOn ℝ 1 (ouFamily f) (Ioi (0 : ℝ) ×ˢ univ) :=
  contDiffOn_pi.mpr fun i => contDiffOn_ouAverage_spaceTime (hf i)

/-- Third derivative bounds give twice continuously differentiable spatial Ornstein–Uhlenbeck
families. -/
theorem contDiff_ouFamily_space {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedThirdCoordinateDerivatives (f i)) (t : ℝ) :
    ContDiff ℝ 2 (fun x => ouFamily f (t, x)) := by
  apply contDiff_pi.mpr
  intro i
  have h := (contDiff_two_heatAverage_of_third (hf i) (1 - Real.exp (-2 * t))).comp
    (by fun_prop : ContDiff ℝ 2 (fun x : Fin n → ℝ => Real.exp (-t) • x))
  exact h

/-- Each component solves the OU evolution equation. -/
theorem hasDerivAt_ouFamily {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedSecondCoordinateDerivatives (f i))
    (x : Fin n → ℝ) {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s => ouFamily f (s, x))
      (fun i => ouGenerator (fun y => ouAverage (f i) y t) x) t := by
  apply hasDerivAt_pi.mpr
  intro i
  rw [ouGenerator_ouAverage (hf i) x ht]
  exact hasDerivAt_ouAverage_generator (hf i) x ht

/-- Ornstein–Uhlenbeck averaging preserves a closed interval bound. -/
theorem ouAverage_mem_Icc {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : HasPolynomiallyBoundedCoordinateDerivatives F) {a b : ℝ}
    (hbound : ∀ y, F y ∈ Icc a b) (x : Fin n → ℝ) (t : ℝ) :
    ouAverage F x t ∈ Icc a b := by
  obtain ⟨C, hC, d, hvalue, _⟩ := hF.2
  have hfint := integrable_shift_of_polynomial_bound hF.1.continuous.measurable hC hvalue
    (Real.exp (-t) • x) (Real.sqrt (1 - Real.exp (-2 * t)))
  have hlo := integral_mono (integrable_const a) hfint (fun z => (hbound _).1)
  have hhi := integral_mono hfint (integrable_const b) (fun z => (hbound _).2)
  simp only [integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul] at hlo hhi
  exact ⟨hlo, hhi⟩

/-- Every coordinate of an Ornstein–Uhlenbeck family remains in the original closed interval. -/
theorem ouFamily_mem_Icc {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedCoordinateDerivatives (f i)) {a b : ℝ}
    (hbound : ∀ i y, f i y ∈ Icc a b) (x : Fin n → ℝ) (t : ℝ) :
    ∀ i, ouFamily f (t, x) i ∈ Icc a b :=
  fun i => ouAverage_mem_Icc (hf i) (hbound i) x t

/-- Joint derivative bound for the vector family, obtained from the
component bounds and the finite-product norm. -/
theorem norm_fderiv_ouFamily_le {n k : ℕ} {f : Fin k → (Fin n → ℝ) → ℝ}
    (hf : ∀ i, HasPolynomiallyBoundedSecondCoordinateDerivatives (f i)) {B G H : ℝ}
    (hB : 0 ≤ B) (hG : 0 ≤ G) (hH : 0 ≤ H)
    (hvalue : ∀ i y, |f i y| ≤ B) (hgrad : ∀ i y, ‖fderiv ℝ (f i) y‖ ≤ G)
    (hsecond : ∀ i j y, |coordinateDerivative (coordinateDerivative (f i) j) j y| ≤ H)
    {t : ℝ} (ht : 0 < t) (x : Fin n → ℝ) :
    ‖fderiv ℝ (ouFamily f) (t, x)‖ ≤ (B + (n : ℝ) * H + G) * (1 + ‖x‖) := by
  let C := (B + (n : ℝ) * H + G) * (1 + ‖x‖)
  have hC : 0 ≤ C := by dsimp only [C]; positivity
  have hpoint : (t, x) ∈ Ioi (0 : ℝ) ×ˢ (univ : Set (Fin n → ℝ)) := ⟨ht, mem_univ _⟩
  have hd := ((contDiffOn_ouFamily (fun i =>
    hasPolynomiallyBoundedCoordinateDerivatives_of_second (hf i))).contDiffAt
    ((isOpen_Ioi.prod isOpen_univ).mem_nhds hpoint)).differentiableAt_one
  apply ContinuousLinearMap.opNorm_le_bound _ hC
  intro v
  apply (pi_norm_le_iff_of_nonneg (mul_nonneg hC (norm_nonneg v))).mpr
  intro i
  have hi : ‖fderiv ℝ (fun p : ℝ × (Fin n → ℝ) => ouAverage (f i) p.2 p.1) (t, x)‖ ≤ C :=
    (le_add_of_nonneg_left (abs_nonneg _)).trans
      (ouAverage_spaceTime_linear_bound (hf i) hB hG hH (hvalue i) (hgrad i) (hsecond i) ht x)
  have heq := congrArg (fun L : (ℝ × (Fin n → ℝ)) →L[ℝ] ℝ => L v) (fderiv_apply hd i)
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.proj_apply] at heq
  rw [← heq]
  exact ((fderiv ℝ (fun p : ℝ × (Fin n → ℝ) => ouAverage (f i) p.2 p.1) (t, x)).le_opNorm v).trans
    (mul_le_mul_of_nonneg_right hi (norm_nonneg v))

end EhrhardGaussian.Ehrhard

end
