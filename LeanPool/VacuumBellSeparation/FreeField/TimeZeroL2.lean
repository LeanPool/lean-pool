/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroCovarianceDilation
public import LeanPool.VacuumBellSeparation.FreeField.Existence

/-!
# Literal time-zero sources in the physical one-particle Hilbert space

The same mass-shell measure used by the spacetime model is used here. This
bundles the proved integrability and Gram identity into genuine `L²` vectors.
No source completion, density, complex injectivity or time-slice result is assumed.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate
open MeasureTheory

namespace VacuumBellSeparation

theorem spatialFourier_add (f g : SpatialTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    spatialFourier (f + g) p = spatialFourier f p + spatialFourier g p := by
  unfold spatialFourier
  rw [← integral_add (integrable_spatialFourier f p) (integrable_spatialFourier g p)]
  apply integral_congr_ae
  refine Filter.Eventually.of_forall fun x => ?_
  change _ * ((f.1 x + g.1 x : ℝ) : ℂ) = _
  push_cast
  ring

theorem timeZeroOneParticle_add (m : ℝ) (u v : TimeZeroSource)
    (p : EuclideanSpace ℝ (Fin 3)) :
    timeZeroOneParticle m (u + v) p = timeZeroOneParticle m u p + timeZeroOneParticle m v p := by
  change spatialFourier (u.1 + v.1) p + Complex.I * (dispersion m p : ℂ) *
      spatialFourier (u.2 + v.2) p = _
  rw [spatialFourier_add, spatialFourier_add]
  unfold timeZeroOneParticle
  ring

theorem continuous_timeZeroOneParticle (m : ℝ) (u : TimeZeroSource) :
    Continuous (timeZeroOneParticle m u) :=
  (continuous_spatialFourier u.1).add
    ((continuous_const.mul (Complex.continuous_ofReal.comp (continuous_dispersion m))).mul
      (continuous_spatialFourier u.2))

/-- The literal time-zero source map belongs to the physical one-particle `L²` space. -/
theorem memLp_timeZeroOneParticle {m : ℝ} (hm : 0 < m) (u : TimeZeroSource) :
    MemLp (timeZeroOneParticle m u) 2 (oneParticleMeasure m) := by
  have hmeas : AEStronglyMeasurable (timeZeroOneParticle m u) (oneParticleMeasure m) :=
    (continuous_timeZeroOneParticle m u).aestronglyMeasurable
  rw [memLp_two_iff_integrable_sq_norm hmeas, oneParticleMeasure,
    integrable_withDensity_iff_integrable_smul (measurable_oneParticleWeight hm)]
  refine (integrable_timeZeroOneParticleInner_integrand hm u u).norm.congr
    (Filter.Eventually.of_forall fun p => ?_)
  change ‖conj (timeZeroOneParticle m u p) * timeZeroOneParticle m u p *
      ((1 / (2 * (2 * Real.pi) ^ 3 * dispersion m p) : ℝ) : ℂ)‖ =
    oneParticleWeight m p • ‖timeZeroOneParticle m u p‖ ^ 2
  rw [norm_mul, norm_mul, Complex.norm_conj, Complex.norm_real, Real.norm_eq_abs,
    abs_of_pos (oneParticleWeightReal_pos hm p), NNReal.smul_def, smul_eq_mul,
    oneParticleWeight_coe hm p]
  ring

/-- The time-zero source vector in the existing physical mass-shell Hilbert space. -/
noncomputable def timeZeroL2 {m : ℝ} (hm : 0 < m) (u : TimeZeroSource) :
    Lp ℂ 2 (oneParticleMeasure m) :=
  (memLp_timeZeroOneParticle hm u).toLp (timeZeroOneParticle m u)

theorem coeFn_timeZeroL2 {m : ℝ} (hm : 0 < m) (u : TimeZeroSource) :
    (timeZeroL2 hm u : EuclideanSpace ℝ (Fin 3) → ℂ) =ᵐ[oneParticleMeasure m]
      timeZeroOneParticle m u :=
  (memLp_timeZeroOneParticle hm u).coeFn_toLp

theorem timeZeroL2_add {m : ℝ} (hm : 0 < m) (u v : TimeZeroSource) :
    timeZeroL2 hm (u + v) = timeZeroL2 hm u + timeZeroL2 hm v :=
  (MemLp.toLp_congr (memLp_timeZeroOneParticle hm (u + v))
    ((memLp_timeZeroOneParticle hm u).add (memLp_timeZeroOneParticle hm v))
    (Filter.Eventually.of_forall fun p => timeZeroOneParticle_add m u v p)).trans
    (MemLp.toLp_add (memLp_timeZeroOneParticle hm u) (memLp_timeZeroOneParticle hm v))

theorem inner_timeZeroL2 {m : ℝ} (hm : 0 < m) (u v : TimeZeroSource) :
    ⟪timeZeroL2 hm u, timeZeroL2 hm v⟫_ℂ = timeZeroOneParticleInner m u v := by
  refine (L2.inner_def (𝕜 := ℂ) _ _).trans ?_
  refine (integral_congr_ae
    (g := fun p => conj (timeZeroOneParticle m u p) * timeZeroOneParticle m v p) ?_).trans ?_
  · filter_upwards [coeFn_timeZeroL2 hm u, coeFn_timeZeroL2 hm v] with p hpu hpv
    rw [hpu, hpv, RCLike.inner_apply']
  · rw [oneParticleMeasure, integral_withDensity_eq_integral_smul (measurable_oneParticleWeight hm)]
    unfold timeZeroOneParticleInner
    refine integral_congr_ae (Filter.Eventually.of_forall fun p => ?_)
    change oneParticleWeight m p • (conj (timeZeroOneParticle m u p) * timeZeroOneParticle m v
      p) = _
    rw [NNReal.smul_def, Complex.real_smul, oneParticleWeight_coe hm p]
    ring

/-- The Gram formula now describes actual inner products of Hilbert-space vectors. -/
theorem inner_timeZeroL2_gram {m : ℝ} (hm : 0 < m) (u v : TimeZeroSource) :
    ⟪timeZeroL2 hm u, timeZeroL2 hm v⟫_ℂ = (timeZeroFourierCovariance m u v : ℂ) +
      (Complex.I / 2) * (timeZeroSymplectic u v : ℂ) := by
  rw [inner_timeZeroL2 hm, timeZeroGram_identity hm]

theorem norm_timeZeroL2_sq {m : ℝ} (hm : 0 < m) (u : TimeZeroSource) :
    ‖timeZeroL2 hm u‖ ^ 2 = timeZeroFourierCovariance m u u := by
  rw [← timeZeroOneParticleInner_re hm, ← inner_timeZeroL2 hm]
  exact (inner_self_eq_norm_sq (𝕜 := ℂ) (timeZeroL2 hm u)).symm

theorem timeZeroFourierCovariance_self_nonneg {m : ℝ} (hm : 0 < m) (u : TimeZeroSource) :
    0 ≤ timeZeroFourierCovariance m u u := by
  rw [← norm_timeZeroL2_sq hm]
  positivity

end VacuumBellSeparation
