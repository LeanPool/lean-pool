/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.AffineGradient
public import Mathlib.MeasureTheory.Function.L2Space
public import Mathlib.MeasureTheory.Integral.Bochner.ContinuousLinearMap
public import Mathlib.MeasureTheory.Measure.Haar.InnerProductSpace

/-! # Smooth Euclidean Poincaré inequalities and second moments -/

public section

namespace CutoffRigidity

open MeasureTheory

/-- The actual smooth Poincaré functional inequality, with its analytic domain
visible. It is not a scalar moment-bound premise. -/
@[expose] def HasSmoothPoincare {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) (rate : ℝ) : Prop :=
  ∀ f : EuclideanSpace ℝ (Fin d) → ℝ, ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞) f → MemLp f 2 μ →
    Integrable (fun x => ‖gradient f x‖ ^ 2) μ → (∫ x, f x ∂μ) = 0 →
    (∫ x, f x ^ 2 ∂μ) ≤ (∫ x, ‖gradient f x‖ ^ 2 ∂μ) / rate

/-- Applying the genuine Poincaré inequality to actual Euclidean coordinates
proves the second-moment bound used in the source corollary. -/
theorem second_moment_le_of_smoothPoincare {d : ℕ}
    (μ : Measure (EuclideanSpace ℝ (Fin d))) [IsProbabilityMeasure μ]
    (rate : ℝ) (hLp : MemLp (fun x => x) 2 μ)
    (hcenter : ∫ x, x ∂μ = 0) (hP : HasSmoothPoincare μ rate) :
    (∫ x, ‖x‖ ^ 2 ∂μ) ≤ d / rate := by
  have hcoord (i : Fin d) : MemLp (fun x : EuclideanSpace ℝ (Fin d) => x i) 2 μ :=
    (EuclideanSpace.proj (𝕜 := ℝ) i).comp_memLp' hLp
  have hmean (i : Fin d) : (∫ x : EuclideanSpace ℝ (Fin d), x i ∂μ) = 0 := by
    have h := (EuclideanSpace.proj (𝕜 := ℝ) i).integral_comp_comm
      (hLp.integrable (by norm_num))
    simpa [hcenter] using h
  have hbound (i : Fin d) : (∫ x : EuclideanSpace ℝ (Fin d), (x i) ^ 2 ∂μ) ≤ 1 / rate := by
    have hgrad (x : EuclideanSpace ℝ (Fin d)) :
        gradient (fun y : EuclideanSpace ℝ (Fin d) => y i) x = EuclideanSpace.single i 1 := by
      simpa only [EuclideanSpace.inner_single_left, map_one, one_mul, add_zero] using
        gradient_inner_add_const (EuclideanSpace.single i 1) 0 x
    have hi : Integrable (fun x : EuclideanSpace ℝ (Fin d) =>
        ‖gradient (fun y : EuclideanSpace ℝ (Fin d) => y i) x‖ ^ 2) μ := by
      simp only [hgrad, PiLp.norm_single, norm_one, one_pow]
      exact integrable_const 1
    have hsm : ContDiff ℝ (↑(⊤ : ℕ∞) : WithTop ℕ∞)
        (fun x : EuclideanSpace ℝ (Fin d) => x i) := by
      exact (EuclideanSpace.proj (𝕜 := ℝ) i).contDiff
    have h := hP (fun x => x i) hsm (hcoord i) hi (hmean i)
    simpa only [hgrad, PiLp.norm_single, norm_one, one_pow, integral_const, measureReal_def,
      measure_univ, ENNReal.toReal_one,
      smul_eq_mul, one_mul] using h
  simp_rw [EuclideanSpace.real_norm_sq_eq]
  rw [integral_finsetSum _ (fun i _ => (hcoord i).integrable_sq)]
  calc
    _ ≤ ∑ _ : Fin d, 1 / rate := Finset.sum_le_sum (fun i _ => hbound i)
    _ = d / rate := by simp [div_eq_mul_inv]

end CutoffRigidity
