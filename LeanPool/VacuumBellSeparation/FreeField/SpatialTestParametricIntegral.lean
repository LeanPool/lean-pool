/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroDefs
public import Mathlib.Analysis.Calculus.ParametricIntegral

/-!
# Differentiation of actual compact spatial-test integrals

Joint continuity and a scalar derivative of the kernel give a local
integrable derivative majorant on the literal compact support. The
integral and its derivative are ordinary three-dimensional integrals.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter

theorem hasDerivAt_spatialTest_integral
    (f : SpatialTestFunction)
    (K D : ℂ → EuclideanSpace ℝ (Fin 3) → ℂ)
    (hK : Continuous (fun q : ℂ × EuclideanSpace ℝ (Fin 3) => K q.1 q.2))
    (hD : Continuous (fun q : ℂ × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (hd : ∀ ζ x, HasDerivAt (fun z => K z x) (D ζ x) ζ) (ζ₀ : ℂ) :
    HasDerivAt (fun ζ => ∫ x, K ζ x * (f.1 x : ℂ))
      (∫ x, D ζ₀ x * (f.1 x : ℂ)) ζ₀ := by
  have hint (ζ : ℂ) : Integrable (fun x => K ζ x * (f.1 x : ℂ)) :=
    ((hK.comp (continuous_const.prodMk continuous_id)).mul
      (Complex.continuous_ofReal.comp f.2.1.continuous)).integrable_of_hasCompactSupport
        ((f.2.2.comp_left Complex.ofReal_zero).mul_left)
  have hdf : Continuous (fun x => D ζ₀ x * (f.1 x : ℂ)) :=
    (hD.comp (continuous_const.prodMk continuous_id)).mul
      (Complex.continuous_ofReal.comp f.2.1.continuous)
  obtain ⟨C, hC⟩ := ((isCompact_closedBall ζ₀ 1).prod f.2.2).exists_bound_of_continuousOn
    hD.continuousOn
  have hb (x : EuclideanSpace ℝ (Fin 3)) (ζ : ℂ) (hζ : ζ ∈ Metric.ball ζ₀ 1) :
      ‖D ζ x * (f.1 x : ℂ)‖ ≤ C * |f.1 x| := by
    by_cases hx : x ∈ tsupport f.1
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (hC (ζ, x) ⟨Metric.ball_subset_closedBall hζ, hx⟩) (abs_nonneg _)
    · simp only [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero,
        mul_zero, norm_zero, abs_zero, le_refl]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun ζ x => K ζ x * (f.1 x : ℂ))
    (F' := fun ζ x => D ζ x * (f.1 x : ℂ)) (bound := fun x => C * |f.1 x|)
    (Metric.ball_mem_nhds ζ₀ (by norm_num))
    (Eventually.of_forall fun ζ => (hint ζ).aestronglyMeasurable)
    (hint ζ₀) hdf.aestronglyMeasurable (Eventually.of_forall hb)
    ((f.2.1.continuous.integrable_of_hasCompactSupport f.2.2).abs.const_mul C)
    (Eventually.of_forall fun x ζ _ => (hd ζ x).mul_const (f.1 x : ℂ))).2

end VacuumBellSeparation
