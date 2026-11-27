/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.DampedSpatialKernel
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.Complex.CauchyIntegral

/-!
# Holomorphy of actual damped spatial Fourier integrals on affine strips

The integral differentiates by the proved half-damping majorant and actual
integrability of every required physical energy moment.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory Filter Set
open scoped Topology ComplexConjugate
open scoped InnerProductSpace

/-- Damped spatial slice given by `∫ p, dampedSpatialKernel m a x v z p * conj (ψ p)
∂oneParticleMeasure m`. -/
noncomputable def dampedSpatialSlice {m : ℝ} (a : ℝ)
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) (x v : EuclideanSpace ℝ (Fin 3)) (z : ℂ) : ℂ :=
  ∫ p, dampedSpatialKernel m a x v z p * conj (ψ p) ∂oneParticleMeasure m

theorem integrable_dampedSpatialSlice_integrand {m a b : ℝ}
    (hm : 0 < m) (ha : 0 < a) (x v : EuclideanSpace ℝ (Fin 3))
    (hbv : b * ‖v‖ ≤ a / 2) (ψ : Lp ℂ 2 (oneParticleMeasure m))
    {z : ℂ} (hz : |z.im| ≤ b) :
    Integrable (fun p => dampedSpatialKernel m a x v z p * conj (ψ p))
      (oneParticleMeasure m) := by
  apply (integrable_dampedShellAmplitude hm (half_pos ha) ψ).norm.mono'
  · exact (continuous_dampedSpatialKernel m a x v z).aestronglyMeasurable.mul
      (Lp.memLp ψ).aestronglyMeasurable.star
  · exact Eventually.of_forall (norm_dampedSpatialKernel_mul_le hm x v hbv ψ hz)

theorem hasDerivAt_dampedSpatialSlice {m a b : ℝ}
    (hm : 0 < m) (ha : 0 < a) (x v : EuclideanSpace ℝ (Fin 3))
    (hbv : b * ‖v‖ ≤ a / 2) (ψ : Lp ℂ 2 (oneParticleMeasure m))
    {z : ℂ} (hz : |z.im| < b) :
    HasDerivAt (dampedSpatialSlice a ψ x v)
      (∫ p, dampedSpatialKernel m a x v z p * (-Complex.I * (⟪p, v⟫_ℝ : ℂ)) *
        conj (ψ p) ∂oneParticleMeasure m) z := by
  have hb : Integrable
      (fun p => ‖v‖ * (dispersion m p * ‖dampedShellAmplitude (a / 2) ψ p‖))
      (oneParticleMeasure m) := by
    simpa only [pow_one] using
      (integrable_dampedShellAmplitude_moment hm (half_pos ha) ψ 1).const_mul ‖v‖
  obtain ⟨_, hd⟩ := hasDerivAt_integral_of_dominated_loc_of_deriv_le
    (μ := oneParticleMeasure m)
    (F := fun w p => dampedSpatialKernel m a x v w p * conj (ψ p))
    (F' := fun w p => dampedSpatialKernel m a x v w p *
      (-Complex.I * (⟪p, v⟫_ℝ : ℂ)) * conj (ψ p))
    (bound := fun p => ‖v‖ * (dispersion m p * ‖dampedShellAmplitude (a / 2) ψ p‖))
    ((isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const).mem_nhds hz)
    (Eventually.of_forall fun w =>
      (continuous_dampedSpatialKernel m a x v w).aestronglyMeasurable.mul
        (Lp.memLp ψ).aestronglyMeasurable.star)
    (integrable_dampedSpatialSlice_integrand hm ha x v hbv ψ hz.le)
    (show AEStronglyMeasurable
      (fun p => dampedSpatialKernel m a x v z p * (-Complex.I * (⟪p, v⟫_ℝ : ℂ)) * conj (ψ p))
      (oneParticleMeasure m) from
      (show Continuous (fun p => dampedSpatialKernel m a x v z p *
        (-Complex.I * (⟪p, v⟫_ℝ : ℂ))) by
        exact (continuous_dampedSpatialKernel m a x v z).mul (by fun_prop)).aestronglyMeasurable.mul
          (Lp.memLp ψ).aestronglyMeasurable.star)
    (Eventually.of_forall fun p w hw =>
      norm_dampedSpatialKernel_derivative_mul_le hm x v hbv ψ hw.le p)
    hb
    (Eventually.of_forall fun p w _ => (hasDerivAt_dampedSpatialKernel m a x v w p).mul_const _)
  exact hd

theorem analyticOnNhd_dampedSpatialSlice {m a b : ℝ}
    (hm : 0 < m) (ha : 0 < a) (x v : EuclideanSpace ℝ (Fin 3))
    (hbv : b * ‖v‖ ≤ a / 2) (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    AnalyticOnNhd ℂ (dampedSpatialSlice a ψ x v) {z : ℂ | |z.im| < b} := by
  apply DifferentiableOn.analyticOnNhd _
    (isOpen_lt (continuous_abs.comp Complex.continuous_im) continuous_const)
  intro z hz
  exact (hasDerivAt_dampedSpatialSlice hm ha x v hbv ψ hz).differentiableAt.differentiableWithinAt

theorem analyticOnNhd_real_dampedSpatialSlice {m a : ℝ}
    (hm : 0 < m) (ha : 0 < a) (x v : EuclideanSpace ℝ (Fin 3))
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    AnalyticOnNhd ℝ (fun t : ℝ => dampedSpatialSlice a ψ x v (t : ℂ)) univ := by
  let b : ℝ := a / (2 * (‖v‖ + 1))
  have hb : 0 < b := by dsimp [b]; positivity
  have heq : b * (2 * (‖v‖ + 1)) = a := by
    dsimp [b]
    exact div_mul_cancel₀ _ (by positivity)
  have hbv : b * ‖v‖ ≤ a / 2 := by nlinarith
  intro t _
  have h := analyticOnNhd_dampedSpatialSlice hm ha x v hbv ψ (t : ℂ) (by simpa using hb)
  exact (h.restrictScalars (𝕜 := ℝ)).comp (Complex.ofRealCLM.analyticAt t)

end VacuumBellSeparation
