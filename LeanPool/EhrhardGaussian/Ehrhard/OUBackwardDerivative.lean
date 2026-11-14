/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.GaussianPathDerivative
public import LeanPool.EhrhardGaussian.Ehrhard.OUCommutation

/-! # Differentiation with backward OU time and a time-dependent integrand -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Filter Set
open EhrhardGaussian.Gaussian (coordinateDerivative standardGaussianMeasure)
open scoped Topology

namespace EhrhardGaussian.Ehrhard

/-- Average a space-time observable while the outer OU time decreases from `T`. -/
def ouSpaceTimeAverage {n : ℕ} (F : ℝ × (Fin n → ℝ) → ℝ)
    (T : ℝ) (x : Fin n → ℝ) (s : ℝ) : ℝ :=
  ∫ z, F (s, Real.exp (s - T) • x + Real.sqrt (1 - Real.exp (2 * (s - T))) • z)
    ∂standardGaussianMeasure n

/-- The backward space–time average is the Ornstein–Uhlenbeck average at the remaining time. -/
theorem ouSpaceTimeAverage_eq_ouAverage {n : ℕ} (F : ℝ × (Fin n → ℝ) → ℝ)
    (T : ℝ) (x : Fin n → ℝ) (s : ℝ) :
    ouSpaceTimeAverage F T x s = ouAverage (fun y => F (s, y)) x (T - s) := by
  rw [ouSpaceTimeAverage, ouAverage,
    show -(T - s) = s - T by ring,
    show -2 * (T - s) = 2 * (s - T) by ring]

/-- The backward-time Gaussian derivative before generator cancellation. -/
theorem hasDerivAt_ouSpaceTimeAverage {n : ℕ} {U : Set ℝ} (hU : IsOpen U)
    {t T : ℝ} (ht : t ∈ U) (hT : ∀ s ∈ U, s < T)
    {F : ℝ × (Fin n → ℝ) → ℝ} (hF : ContDiffOn ℝ 1 F (U ×ˢ univ))
    {C : ℝ} (hC : 0 ≤ C) {N : ℕ}
    (hbound : ∀ s ∈ U, ∀ y : Fin n → ℝ,
      |F (s, y)| + ‖fderiv ℝ F (s, y)‖ ≤ C * (1 + ‖y‖) ^ N)
    (x : Fin n → ℝ) :
    HasDerivAt (ouSpaceTimeAverage F T x)
      (∫ z, fderiv ℝ F (t, Real.exp (t - T) • x +
          Real.sqrt (1 - Real.exp (2 * (t - T))) • z)
        (1, Real.exp (t - T) • x +
          (-Real.exp (2 * (t - T)) / Real.sqrt (1 - Real.exp (2 * (t - T)))) • z)
        ∂standardGaussianMeasure n) t := by
  let p : ℝ → (Fin n → ℝ) := fun s => Real.exp (s - T) • x
  let a : ℝ → ℝ := fun s => Real.sqrt (1 - Real.exp (2 * (s - T)))
  have hpos (s : ℝ) (hs : s ∈ U) : 0 < 1 - Real.exp (2 * (s - T)) := by
    apply sub_pos.mpr
    apply Real.exp_lt_one_iff.mpr
    linarith only [hT s hs]
  have hp : ContDiffOn ℝ 1 p U := by dsimp only [p]; fun_prop
  have ha : ContDiffOn ℝ 1 a U := by
    apply ContDiffOn.sqrt (by fun_prop : ContDiffOn ℝ 1
      (fun s : ℝ => 1 - Real.exp (2 * (s - T))) U)
    exact fun s hs => (hpos s hs).ne'
  have hpd : HasDerivAt p (Real.exp (t - T) • x) t := by
    simpa only [mul_one] using (((hasDerivAt_id' t).sub_const T).exp.smul_const x)
  have harg := ((((hasDerivAt_id' t).sub_const T).const_mul 2).exp).const_sub 1
  have had : HasDerivAt a
      (-Real.exp (2 * (t - T)) / Real.sqrt (1 - Real.exp (2 * (t - T)))) t := by
    have h := (Real.hasDerivAt_sqrt (hpos t ht).ne').comp
      (h := fun s : ℝ => 1 - Real.exp (2 * (s - T))) t harg
    dsimp only [Function.comp_def] at h
    convert h using 1
    ring
  have h := hasDerivAt_gaussian_path_integral_of_contDiff hU ht hF hp ha hC hbound
  rw [hpd.deriv, had.deriv] at h
  exact h

end EhrhardGaussian.Ehrhard

end
