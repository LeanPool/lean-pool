/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeWave
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Entire dependence of the original wedge wave on complex rapidity

For each actual momentum, compact support supplies a local integrable
majorant for the exact rapidity derivative. The statement is scalar
entireness; L2-valued strip analyticity is a separate subsequent step.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Topology

/-- Wedge wave phase derivative defined as `Complex.exp (Complex.I * boostPhase m (-ζ) p x) *
(-(Complex.I * boostPhaseDeriv m (-ζ) p x))`. -/
noncomputable def wedgeWavePhaseDerivative (m : ℝ) (p : EuclideanSpace ℝ (Fin 3))
    (ζ : ℂ) (x : Spacetime) : ℂ :=
  Complex.exp (Complex.I * boostPhase m (-ζ) p x) *
    (-(Complex.I * boostPhaseDeriv m (-ζ) p x))

theorem continuous_wedgeWavePhaseDerivative (m : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    Continuous (fun q : ℂ × Spacetime => wedgeWavePhaseDerivative m p q.1 q.2) := by
  unfold wedgeWavePhaseDerivative boostPhase boostPhaseDeriv
  fun_prop

theorem hasDerivAt_wedgeWave_integrand (m : ℝ) (F : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) (x : Spacetime) (ζ : ℂ) :
    HasDerivAt (fun z => Complex.exp (Complex.I * boostPhase m (-z) p x) * (F.1 x : ℂ))
      (wedgeWavePhaseDerivative m p ζ x * (F.1 x : ℂ)) ζ := by
  have hd := ((hasDerivAt_boostPhase m p x (-ζ)).comp ζ (hasDerivAt_neg ζ)).const_mul Complex.I
  convert! hd.cexp.mul_const (F.1 x : ℂ) using 1
  simp only [wedgeWavePhaseDerivative, Function.comp_apply]; ring

theorem hasDerivAt_wedgeWave (m : ℝ) (F : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) (ζ₀ : ℂ) :
    HasDerivAt (fun ζ => wedgeWave m F ζ p)
      (∫ x : Spacetime, wedgeWavePhaseDerivative m p ζ₀ x * (F.1 x : ℂ)) ζ₀ := by
  have hc := continuous_wedgeWavePhaseDerivative m p
  have hK : IsCompact (Metric.closedBall ζ₀ 1 ×ˢ tsupport F.1) :=
    (isCompact_closedBall ζ₀ 1).prod F.2.2
  obtain ⟨C, hC⟩ := hK.exists_bound_of_continuousOn hc.continuousOn
  have hD : Continuous (fun x : Spacetime =>
      wedgeWavePhaseDerivative m p ζ₀ x * (F.1 x : ℂ)) :=
    (hc.comp (continuous_const.prodMk continuous_id)).mul
      (Complex.continuous_ofReal.comp (continuous_testFunction F))
  have hbound : ∀ x : Spacetime, ∀ ζ ∈ Metric.ball ζ₀ 1,
      ‖wedgeWavePhaseDerivative m p ζ x * (F.1 x : ℂ)‖ ≤ C * |F.1 x| := by
    intro x ζ hζ
    by_cases hx : x ∈ tsupport F.1
    · rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right
        (hC (ζ, x) ⟨Metric.ball_subset_closedBall hζ, hx⟩) (abs_nonneg _)
    · simp only [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero,
        mul_zero, norm_zero, abs_zero, le_refl]
  exact (hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (F := fun ζ x => Complex.exp (Complex.I * boostPhase m (-ζ) p x) * (F.1 x : ℂ))
    (F' := fun ζ x => wedgeWavePhaseDerivative m p ζ x * (F.1 x : ℂ))
    (bound := fun x => C * |F.1 x|)
    (Metric.ball_mem_nhds ζ₀ (by norm_num))
    (Filter.Eventually.of_forall fun ζ => (integrable_wedgeWave_integrand m F ζ
      p).aestronglyMeasurable)
    (integrable_wedgeWave_integrand m F ζ₀ p) hD.aestronglyMeasurable
    (Filter.Eventually.of_forall hbound) ((integrable_abs_testFunction F).const_mul C)
    (Filter.Eventually.of_forall fun x ζ _ => hasDerivAt_wedgeWave_integrand m F p x ζ)).2

theorem analyticOnNhd_wedgeWave (m : ℝ) (F : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    AnalyticOnNhd ℂ (fun ζ => wedgeWave m F ζ p) Set.univ := by
  have hd : Differentiable ℂ (fun ζ => wedgeWave m F ζ p) :=
    fun ζ => (hasDerivAt_wedgeWave m F p ζ).differentiableAt
  exact fun ζ _ => hd.analyticAt ζ

end VacuumBellSeparation
