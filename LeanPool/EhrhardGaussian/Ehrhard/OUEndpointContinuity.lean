/-
Copyright (c) 2026 Scott Armstrong. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong
-/
module

public import LeanPool.EhrhardGaussian.Ehrhard.OUTimeDependent

/-! # Continuity at the zero outer-time endpoint of interpolation -/

@[expose] public noncomputable section

open MeasureTheory ProbabilityTheory Set
open EhrhardGaussian.Gaussian (standardGaussianMeasure)

namespace EhrhardGaussian.Ehrhard

/-- The Ornstein–Uhlenbeck average at time zero equals the original function. -/
theorem ouAverage_zero {n : ℕ} (F : (Fin n → ℝ) → ℝ) (x : Fin n → ℝ) :
    ouAverage F x 0 = F x := by
  simp [ouAverage]

/-- The backward space–time average at its terminal time equals the original function. -/
theorem ouSpaceTimeAverage_self {n : ℕ} (F : ℝ × (Fin n → ℝ) → ℝ)
    (T : ℝ) (x : Fin n → ℝ) : ouSpaceTimeAverage F T x T = F (T, x) := by
  rw [ouSpaceTimeAverage_eq_ouAverage, sub_self, ouAverage_zero]

/-- Boundedness and joint continuity imply continuity at the endpoint where the outer OU time
vanishes. -/
theorem continuousOn_ouSpaceTimeAverage {n : ℕ} {F : ℝ × (Fin n → ℝ) → ℝ}
    {l T B : ℝ} (hF : ContinuousOn F (Icc l T ×ˢ univ))
    (hbound : ∀ s ∈ Icc l T, ∀ y, |F (s, y)| ≤ B) (x : Fin n → ℝ) :
    ContinuousOn (ouSpaceTimeAverage F T x) (Icc l T) := by
  have hsection (s) (hs : s ∈ Icc l T) : Continuous (fun y => F (s, y)) :=
    hF.comp_continuous (by fun_prop : Continuous (fun y : Fin n → ℝ => (s, y)))
      (fun _ => ⟨hs, mem_univ _⟩)
  apply continuousOn_of_dominated (μ := standardGaussianMeasure n) (bound := fun _ => B)
  · intro s hs
    exact ((hsection s hs).comp (by fun_prop)).aestronglyMeasurable
  · intro s hs
    exact ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using hbound s hs _
  · exact integrable_const B
  · apply ae_of_all
    intro z
    apply hF.comp (by fun_prop : Continuous (fun s : ℝ =>
      (s, Real.exp (s - T) • x + Real.sqrt (1 - Real.exp (2 * (s - T))) • z))).continuousOn
    exact fun s hs => ⟨hs, mem_univ _⟩

/-- Ornstein–Uhlenbeck averaging preserves an upper bound for a bounded continuous function. -/
theorem ouAverage_le_of_bounded {n : ℕ} {F : (Fin n → ℝ) → ℝ}
    (hF : Continuous F) {B b : ℝ} (habs : ∀ y, |F y| ≤ B) (hle : ∀ y, F y ≤ b)
    (x : Fin n → ℝ) (t : ℝ) : ouAverage F x t ≤ b := by
  have hmeas : AEStronglyMeasurable (fun z : Fin n → ℝ =>
      F (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • z))
      (standardGaussianMeasure n) := (hF.comp (by fun_prop)).aestronglyMeasurable
  have hint : Integrable (fun z : Fin n → ℝ =>
      F (Real.exp (-t) • x + Real.sqrt (1 - Real.exp (-2 * t)) • z))
      (standardGaussianMeasure n) :=
    Integrable.of_bound hmeas B (ae_of_all _ fun z => by simpa only [Real.norm_eq_abs] using habs _)
  have h := integral_mono hint (integrable_const b) (fun z => hle _)
  simpa only [ouAverage, integral_const, Measure.real, measure_univ, ENNReal.toReal_one, one_smul]
    using h

end EhrhardGaussian.Ehrhard

end
