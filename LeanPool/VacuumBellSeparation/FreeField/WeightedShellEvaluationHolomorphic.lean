/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceCurve
public import LeanPool.VacuumBellSeparation.Shell.InducedShellVolumeCoordinates

/-!
# Actual multivariable holomorphy of compact-source evaluation

The compact-support differentiation argument is the Fréchet version
of SpatialTestParametricIntegral. It constructs the derivative of the
literal Fourier integral and then restricts the resulting holomorphic
wave to each actual shell chart.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter

theorem hasFDerivAt_spatialTest_integral
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℂ E] [ProperSpace E]
    (f : SpatialTestFunction)
    (K : E → EuclideanSpace ℝ (Fin 3) → ℂ)
    (D : E → EuclideanSpace ℝ (Fin 3) → E →L[ℂ] ℂ)
    (hK : Continuous (fun q : E × EuclideanSpace ℝ (Fin 3) => K q.1 q.2))
    (hD : Continuous (fun q : E × EuclideanSpace ℝ (Fin 3) => D q.1 q.2))
    (hd : ∀ z x, HasFDerivAt (fun w => K w x) (D z x) z) (z₀ : E) :
    HasFDerivAt (fun z => ∫ x, K z x * (f.1 x : ℂ))
      (∫ x, (f.1 x : ℂ) • D z₀ x) z₀ := by
  have hint (z : E) : Integrable (fun x => K z x * (f.1 x : ℂ)) :=
    ((hK.comp (continuous_const.prodMk continuous_id)).mul
      (Complex.continuous_ofReal.comp f.2.1.continuous)).integrable_of_hasCompactSupport
        ((f.2.2.comp_left Complex.ofReal_zero).mul_left)
  have hdf : Continuous (fun x => (f.1 x : ℂ) • D z₀ x) :=
    (Complex.continuous_ofReal.comp f.2.1.continuous).smul
      (hD.comp (continuous_const.prodMk continuous_id))
  obtain ⟨C, hC⟩ := ((isCompact_closedBall z₀ 1).prod f.2.2).exists_bound_of_continuousOn
    hD.continuousOn
  have hb (x : EuclideanSpace ℝ (Fin 3)) (z : E) (hz : z ∈ Metric.ball z₀ 1) :
      ‖(f.1 x : ℂ) • D z x‖ ≤ C * |f.1 x| := by
    by_cases hx : x ∈ tsupport f.1
    · rw [norm_smul, Complex.norm_real, Real.norm_eq_abs, mul_comm]
      exact mul_le_mul_of_nonneg_right
        (hC (z, x) ⟨Metric.ball_subset_closedBall hz, hx⟩) (abs_nonneg _)
    · rw [norm_smul]
      simp only [image_eq_zero_of_notMem_tsupport hx, Complex.ofReal_zero,
        norm_zero, zero_mul, abs_zero, mul_zero, le_refl]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le
    (F := fun z x => K z x * (f.1 x : ℂ))
    (F' := fun z x => (f.1 x : ℂ) • D z x) (bound := fun x => C * |f.1 x|)
    (Metric.ball_mem_nhds z₀ (by norm_num))
    (Eventually.of_forall fun z => (hint z).aestronglyMeasurable)
    (hint z₀) hdf.aestronglyMeasurable (Eventually.of_forall hb)
    ((f.2.1.continuous.integrable_of_hasCompactSupport f.2.2).abs.const_mul C)
    (Eventually.of_forall fun x z _ => (hd z x).mul_const (f.1 x : ℂ))

theorem continuous_complexSpatialPhase_map :
    Continuous (complexSpatialPhase : EuclideanSpace ℝ (Fin 3) →
      ComplexSpacetime →L[ℂ] ℂ) := by
  unfold complexSpatialPhase
  fun_prop

theorem hasFDerivAt_complexSpatialFourier (f : SpatialTestFunction) (z : ComplexSpacetime) :
    HasFDerivAt (fun w : ComplexSpacetime => complexSpatialFourier f w.2)
      (∫ x : EuclideanSpace ℝ (Fin 3), (f.1 x : ℂ) •
        ((Complex.exp ((-Complex.I) * complexSpatialPhase x z) * (-Complex.I)) •
          complexSpatialPhase x)) z := by
  have h := hasFDerivAt_spatialTest_integral f
    (fun w x => Complex.exp ((-Complex.I) * complexSpatialPhase x w))
    (fun w x => (Complex.exp ((-Complex.I) * complexSpatialPhase x w) * (-Complex.I)) •
      complexSpatialPhase x)
    (by simp only [complexSpatialPhase_apply, spatialDot]; fun_prop)
    (by
      have hp := continuous_complexSpatialPhase_map.comp
        (continuous_snd : Continuous
          (Prod.snd : ComplexSpacetime × EuclideanSpace ℝ (Fin 3) → _))
      have hc : Continuous (fun q : ComplexSpacetime × EuclideanSpace ℝ (Fin 3) =>
          Complex.exp (-Complex.I * complexSpatialPhase q.2 q.1) * (-Complex.I)) := by
        simp only [complexSpatialPhase_apply, spatialDot]
        fun_prop
      simpa only [Function.comp_def, Pi.smul_def] using! hc.smul hp)
    (fun w x => by
      convert ((complexSpatialPhase x).hasFDerivAt.const_mul (-Complex.I)).cexp using 1
      simp only [smul_smul]) z
  simpa only [complexSpatialFourier, complexSpatialPhase_apply, neg_mul] using h

theorem differentiable_complexSourceWave (u : TimeZeroSource) :
    Differentiable ℂ (complexSourceWave u) := by
  have hf : Differentiable ℂ (fun z : ComplexSpacetime => complexSpatialFourier u.1 z.2) :=
    fun z => (hasFDerivAt_complexSpatialFourier u.1 z).differentiableAt
  have hg : Differentiable ℂ (fun z : ComplexSpacetime => complexSpatialFourier u.2 z.2) :=
    fun z => (hasFDerivAt_complexSpatialFourier u.2 z).differentiableAt
  exact hf.add (((ContinuousLinearMap.fst ℂ ℂ (Fin 3 → ℂ)).differentiable.const_mul
    Complex.I).mul hg)

theorem differentiableAt_complexSourceWave_shellChart {m : ℝ}
    (u : TimeZeroSource) (Λ : Spacetime ≃L[ℝ] Spacetime) {w : ShellEuclideanDomain}
    (hw : w ∈ euclideanShellChartDomain m) :
    DifferentiableAt ℂ (fun v => complexSourceWave u
      (lorentzComplexShellChart m Λ (shellEuclideanCoordinates v))) w :=
  (differentiable_complexSourceWave u _).comp w
    ((differentiableAt_lorentzComplexShellChart Λ hw).comp w
      shellEuclideanCoordinates.differentiableAt)

end VacuumBellSeparation
