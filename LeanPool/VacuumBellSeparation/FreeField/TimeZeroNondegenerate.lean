/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroL2

/-!
# Nondegeneracy of the real time-zero covariance

Reality of both source components recovers each Fourier transform from κ(p)
and the conjugate of κ(-p). This proves injectivity on real test pairs. It is
not the complexified completed-source injectivity/standardness theorem.
-/

@[expose] public section

open scoped InnerProductSpace ComplexConjugate FourierTransform
open MeasureTheory

namespace VacuumBellSeparation

theorem spatialTestFunction_eq_zero_of_fourier_eq_zero (f : SpatialTestFunction)
    (hf : ∀ p, spatialFourier f p = 0) : f = 0 := by
  have hFT : 𝓕 (spatialSchwartz f) = (0 : SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ) := by
    ext p
    change (𝓕 (spatialSchwartz f)) p = 0
    simpa only [← spatialFourier_two_pi] using hf ((2 * Real.pi) • p)
  have hS : spatialSchwartz f = 0 := by
    apply (FourierTransform.fourierCLE ℂ
      (SchwartzMap (EuclideanSpace ℝ (Fin 3)) ℂ)).injective
    simpa using hFT
  apply Subtype.ext
  funext x
  have hx := DFunLike.congr_fun hS x
  change f.1 x = 0
  change (f.1 x : ℂ) = 0 at hx
  exact Complex.ofReal_injective hx

theorem timeZeroSource_eq_zero_of_oneParticle_eq_zero {m : ℝ} (hm : 0 < m)
    (u : TimeZeroSource) (hu : ∀ p, timeZeroOneParticle m u p = 0) : u = 0 := by
  have hcomponents (p : EuclideanSpace ℝ (Fin 3)) :
      spatialFourier u.1 p = 0 ∧ spatialFourier u.2 p = 0 := by
    have hp := hu p
    have hn := congrArg conj (hu (-p))
    have hw : dispersion m (-p) = dispersion m p := by simp only [dispersion, norm_neg]
    simp only [timeZeroOneParticle, hw, spatialFourier_neg, map_add, map_mul,
      Complex.conj_conj, Complex.conj_I, Complex.conj_ofReal, map_zero] at hp hn
    have hf : spatialFourier u.1 p = 0 := by
      linear_combination (1 / 2 : ℂ) * hp + (1 / 2 : ℂ) * hn
    have hg : Complex.I * (dispersion m p : ℂ) * spatialFourier u.2 p = 0 := by
      linear_combination (1 / 2 : ℂ) * hp - (1 / 2 : ℂ) * hn
    refine ⟨hf, (mul_eq_zero.mp hg).resolve_left ?_⟩
    exact mul_ne_zero Complex.I_ne_zero
      (Complex.ofReal_ne_zero.mpr (hm.trans_le (le_dispersion hm.le p)).ne')
  apply Prod.ext
  · exact spatialTestFunction_eq_zero_of_fourier_eq_zero u.1 (fun p => (hcomponents p).1)
  · exact spatialTestFunction_eq_zero_of_fourier_eq_zero u.2 (fun p => (hcomponents p).2)

/-- The positive massive shell density has the same null sets as spatial volume. -/
theorem ae_oneParticleMeasure_iff {m : ℝ} (hm : 0 < m)
    {P : EuclideanSpace ℝ (Fin 3) → Prop} :
    (∀ᵐ p ∂oneParticleMeasure m, P p) ↔ ∀ᵐ p, P p := by
  rw [oneParticleMeasure, ae_withDensity_iff (measurable_oneParticleWeight hm).coe_nnreal_ennreal]
  have hw (p : EuclideanSpace ℝ (Fin 3)) : (oneParticleWeight m p : ENNReal) ≠ 0 := by
    have hp : 0 < oneParticleWeight m p := Real.toNNReal_pos.mpr (oneParticleWeightReal_pos hm p)
    exact_mod_cast hp.ne'
  constructor
  · intro h
    filter_upwards [h] with p hp
    exact hp (hw p)
  · intro h
    filter_upwards [h] with p hp
    exact fun _ => hp

/-- Real test pairs cannot vanish as physical one-particle vectors unless both sources vanish. -/
theorem timeZeroSource_eq_zero_of_L2_eq_zero {m : ℝ} (hm : 0 < m)
    (u : TimeZeroSource) (hu : timeZeroL2 hm u = 0) : u = 0 := by
  have hae : timeZeroOneParticle m u =ᵐ[oneParticleMeasure m] 0 := by
    have hcoe := coeFn_timeZeroL2 hm u
    rw [hu] at hcoe
    exact hcoe.symm.trans (Lp.coeFn_zero ℂ 2 (oneParticleMeasure m))
  have hvol : timeZeroOneParticle m u =ᵐ[volume] 0 := (ae_oneParticleMeasure_iff hm).mp hae
  have hfun := Measure.eq_of_ae_eq hvol (continuous_timeZeroOneParticle m u) continuous_const
  exact timeZeroSource_eq_zero_of_oneParticle_eq_zero hm u (fun p => congrFun hfun p)

/-- The explicitly defined real covariance is positive definite on the test-source space. -/
theorem timeZeroFourierCovariance_self_pos {m : ℝ} (hm : 0 < m)
    (u : TimeZeroSource) (hu : u ≠ 0) : 0 < timeZeroFourierCovariance m u u := by
  rw [← norm_timeZeroL2_sq hm]
  exact sq_pos_of_pos (norm_pos_iff.mpr (fun h => hu (timeZeroSource_eq_zero_of_L2_eq_zero hm u h)))

end VacuumBellSeparation
