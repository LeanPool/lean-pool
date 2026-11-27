/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.CStarAlgebra.Classes
public import Mathlib.Tactic.ReduceModChar
import Mathlib.Tactic.Positivity
public import Mathlib.Analysis.Analytic.Basic
public import Mathlib.Analysis.Calculus.FDeriv.Basic
public import Mathlib.Analysis.InnerProductSpace.PiL2
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.Analysis.Calculus.Deriv.Basic
public import Mathlib.Analysis.Complex.CauchyIntegral
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Entire exponential transforms of compactly supported test functions

This proves the elementary Fourier–Laplace step by differentiation under the
actual Bochner integral. The coefficient in the exponential may be any
continuous complex function of the spatial variable. Compact support provides
the uniform local majorant. This is a test-function result, not a
Paley–Wiener theorem for completed compactly supported distributions.
-/

@[expose] public section

open MeasureTheory
open scoped Topology

namespace VacuumBellSeparation

/-- The exponential transform before the spatial coefficient is specialized to a Fourier slice. -/
noncomputable def compactExpTransform
    (a f : EuclideanSpace ℝ (Fin 3) → ℂ) (z : ℂ) : ℂ :=
  ∫ x, Complex.exp (z * a x) * f x

theorem hasDerivAt_compactExpTransform
    {a f : EuclideanSpace ℝ (Fin 3) → ℂ} (ha : Continuous a) (hf : Continuous f)
    (hc : HasCompactSupport f) (z₀ : ℂ) :
    HasDerivAt (compactExpTransform a f)
      (∫ x, Complex.exp (z₀ * a x) * a x * f x) z₀ := by
  obtain ⟨C, hC⟩ := hc.exists_bound_of_continuousOn ha.continuousOn
  let R : ℝ := |C| + 1
  have hR : 0 < R := by dsimp [R]; positivity
  have haR (x : EuclideanSpace ℝ (Fin 3)) (hx : x ∈ tsupport f) : ‖a x‖ ≤ R := by
    exact (hC x hx).trans (by dsimp [R]; linarith [le_abs_self C])
  have hF (z : ℂ) : Continuous (fun x => Complex.exp (z * a x) * f x) :=
    (Complex.continuous_exp.comp (continuous_const.mul ha)).mul hf
  have hD (z : ℂ) : Continuous (fun x => Complex.exp (z * a x) * a x * f x) :=
    ((Complex.continuous_exp.comp (continuous_const.mul ha)).mul ha).mul hf
  have hbound (x : EuclideanSpace ℝ (Fin 3)) (z : ℂ) (hz : z ∈ Metric.ball z₀ 1) :
      ‖Complex.exp (z * a x) * a x * f x‖ ≤
        (Real.exp ((‖z₀‖ + 1) * R) * R) * ‖f x‖ := by
    by_cases hfx : f x = 0
    · simp [hfx]
    have hx : x ∈ tsupport f := subset_tsupport f hfx
    have hzdist : ‖z - z₀‖ < 1 := by simpa [Metric.mem_ball, dist_eq_norm] using hz
    have hznorm : ‖z‖ ≤ ‖z₀‖ + 1 := by
      have ht := norm_add_le (z - z₀) z₀
      rw [sub_add_cancel] at ht
      linarith
    have hexp : ‖Complex.exp (z * a x)‖ ≤ Real.exp ((‖z₀‖ + 1) * R) := by
      refine (Complex.norm_exp_le_exp_norm _).trans (Real.exp_le_exp.mpr ?_)
      rw [norm_mul]
      exact mul_le_mul hznorm (haR x hx) (norm_nonneg _) (by positivity)
    rw [norm_mul, norm_mul]
    exact mul_le_mul_of_nonneg_right
      (mul_le_mul hexp (haR x hx) (norm_nonneg _) (Real.exp_pos _).le) (norm_nonneg _)
  have hd (x : EuclideanSpace ℝ (Fin 3)) (z : ℂ) :
      HasDerivAt (fun w => Complex.exp (w * a x) * f x)
        (Complex.exp (z * a x) * a x * f x) z := by
    simpa using (((hasDerivAt_id' (x := z)).mul_const (a x)).cexp).mul_const (f x)
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun z x => Complex.exp (z * a x) * f x)
    (F' := fun z x => Complex.exp (z * a x) * a x * f x)
    (bound := fun x => (Real.exp ((‖z₀‖ + 1) * R) * R) * ‖f x‖)
    (Metric.ball_mem_nhds z₀ (by norm_num))
    (Filter.Eventually.of_forall fun z => (hF z).aestronglyMeasurable)
    ((hF z₀).integrable_of_hasCompactSupport hc.mul_left)
    (hD z₀).aestronglyMeasurable
    (Filter.Eventually.of_forall hbound)
    ((hf.integrable_of_hasCompactSupport hc).norm.const_mul _)
    (Filter.Eventually.of_forall fun x z _ => hd x z)).2

/-- The compact test-function transform is entire in the actual complex parameter. -/
theorem analyticOnNhd_compactExpTransform
    {a f : EuclideanSpace ℝ (Fin 3) → ℂ} (ha : Continuous a) (hf : Continuous f)
    (hc : HasCompactSupport f) : AnalyticOnNhd ℂ (compactExpTransform a f) Set.univ := by
  have hdiff : Differentiable ℂ (compactExpTransform a f) :=
    fun z => (hasDerivAt_compactExpTransform ha hf hc z).differentiableAt
  exact fun z _ => hdiff.analyticAt z

end VacuumBellSeparation
