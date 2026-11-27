/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceWave
public import LeanPool.VacuumBellSeparation.FreeField.SpatialTestParametricIntegral
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroNondegenerate
public import LeanPool.VacuumBellSeparation.FreeField.AnalyticOddOrder

/-!
# Entire Cauchy-data waves on the literal complex boost orbit

Original spatial test integrals supply genuine entire functions of
rapidity. Equality of the original physical L2 vectors implies equality
of these entire waves with the spacetime test waves. The identity theorem
is applied to actual integrals, with no analytic-continuation premise.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory

/-- Spatial rapidity wave given by `∫ x : EuclideanSpace ℝ (Fin 3), Complex.exp (Complex.I *
boostPhase m (-ζ) p (0, x)) * (f.1 x : ℂ)`. -/
noncomputable def spatialRapidityWave (m : ℝ) (f : SpatialTestFunction) (ζ : ℂ)
    (p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  ∫ x : EuclideanSpace ℝ (Fin 3),
    Complex.exp (Complex.I * boostPhase m (-ζ) p (0, x)) * (f.1 x : ℂ)

theorem spatialRapidityWave_eq_complexSpatialFourier (m : ℝ) (f : SpatialTestFunction)
    (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    spatialRapidityWave m f ζ p = complexSpatialFourier f (complexShellBoost m ζ p).2 := by
  unfold spatialRapidityWave complexSpatialFourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [← complexShellBoost_phase m ζ p (0, x)]
    simp only [Complex.ofReal_zero, mul_zero, zero_sub, mul_neg]

theorem spatialRapidityWave_ofReal (m η : ℝ) (f : SpatialTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    spatialRapidityWave m f (η : ℂ) p = spatialFourier f (shellBoost m η p) := by
  unfold spatialRapidityWave spatialFourier
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [← Complex.ofReal_neg, boostPhase_ofReal_eq_zero_shellBoost, neg_neg, boostPhase_zero]
    simp only [mul_zero, zero_sub, Complex.ofReal_neg, mul_neg]

theorem complexShellBoost_energy_ofReal (m η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    (complexShellBoost m (η : ℂ) p).1 = (dispersion m (shellBoost m η p) : ℂ) := by
  have h := complexShellBoost_phase m (η : ℂ) p (1, 0)
  rw [← Complex.ofReal_neg, boostPhase_ofReal_eq_zero_shellBoost, neg_neg, boostPhase_zero] at h
  simpa only [Complex.ofReal_one, mul_one, spatialDot, PiLp.zero_apply,
    Complex.ofReal_zero, mul_zero, Finset.sum_const_zero, sub_zero,
    inner_zero_right] using h

theorem hasDerivAt_spatialRapidityWave (m : ℝ) (f : SpatialTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) (ζ : ℂ) :
    HasDerivAt (fun z => spatialRapidityWave m f z p)
      (∫ x : EuclideanSpace ℝ (Fin 3), wedgeWavePhaseDerivative m p ζ (0, x) * (f.1 x : ℂ)) ζ := by
  apply hasDerivAt_spatialTest_integral f
    (fun z x => Complex.exp (Complex.I * boostPhase m (-z) p (0, x)))
    (fun z x => wedgeWavePhaseDerivative m p z (0, x))
  · unfold boostPhase
    fun_prop
  · have hinc : Continuous (fun q : ℂ × EuclideanSpace ℝ (Fin 3) =>
        (q.1, ((0 : ℝ), q.2))) :=
      (continuous_fst : Continuous (Prod.fst : ℂ × EuclideanSpace ℝ (Fin 3) → ℂ)).prodMk
        ((continuous_const : Continuous (fun _ : ℂ × EuclideanSpace ℝ (Fin 3) => (0 : ℝ))).prodMk
          continuous_snd)
    change Continuous (fun q : ℂ × EuclideanSpace ℝ (Fin 3) =>
      wedgeWavePhaseDerivative m p q.1 (0, q.2))
    exact Continuous.comp'
      (f := fun q : ℂ × EuclideanSpace ℝ (Fin 3) => (q.1, ((0 : ℝ), q.2)))
      (g := fun q : ℂ × Spacetime => wedgeWavePhaseDerivative m p q.1 q.2)
      (continuous_wedgeWavePhaseDerivative m p) hinc
  · intro z x
    have hd := ((hasDerivAt_boostPhase m p (0, x) (-z)).comp z
      (hasDerivAt_neg z)).const_mul Complex.I
    simpa only [wedgeWavePhaseDerivative, Function.comp_apply, mul_neg_one, mul_neg, mul_one]
      using hd.cexp

theorem analyticOnNhd_complexSourceWave_boost (m : ℝ) (u : TimeZeroSource)
    (p : EuclideanSpace ℝ (Fin 3)) :
    AnalyticOnNhd ℂ (fun ζ => complexSourceWave u (complexShellBoost m ζ p)) Set.univ := by
  have hf : Differentiable ℂ (fun ζ => spatialRapidityWave m u.1 ζ p) :=
    fun ζ => (hasDerivAt_spatialRapidityWave m u.1 p ζ).differentiableAt
  have hg : Differentiable ℂ (fun ζ => spatialRapidityWave m u.2 ζ p) :=
    fun ζ => (hasDerivAt_spatialRapidityWave m u.2 p ζ).differentiableAt
  have he : Differentiable ℂ (fun ζ => (complexShellBoost m ζ p).1) := by
    unfold complexShellBoost
    fun_prop
  have hi : Differentiable ℂ (fun _ : ℂ => Complex.I) := differentiable_const _
  have hd := hf.add ((hi.mul he).mul hg)
  intro ζ hζ
  simpa only [complexSourceWave, spatialRapidityWave_eq_complexSpatialFourier,
    Pi.add_def, Pi.mul_def] using hd.analyticAt ζ

theorem complexSourceWave_boost_ofReal (m η : ℝ) (u : TimeZeroSource)
    (p : EuclideanSpace ℝ (Fin 3)) :
    complexSourceWave u (complexShellBoost m (η : ℂ) p) =
      timeZeroOneParticle m u (shellBoost m η p) := by
  rw [complexSourceWave, ← spatialRapidityWave_eq_complexSpatialFourier,
    ← spatialRapidityWave_eq_complexSpatialFourier, spatialRapidityWave_ofReal,
    spatialRapidityWave_ofReal, complexShellBoost_energy_ofReal]
  rfl

theorem wedgeWave_eq_complexSourceWave_of_L2_eq {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (u : TimeZeroSource) (heq : oneParticleL2 hm F = timeZeroL2 hm u)
    (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    wedgeWave m F ζ p = complexSourceWave u (complexShellBoost m ζ p) := by
  have hae : oneParticle m F =ᵐ[oneParticleMeasure m] timeZeroOneParticle m u := by
    have hF := coeFn_oneParticleL2 hm F
    rw [heq] at hF
    exact hF.symm.trans (coeFn_timeZeroL2 hm u)
  have hreal : oneParticle m F = timeZeroOneParticle m u :=
    Measure.eq_of_ae_eq ((ae_oneParticleMeasure_iff hm).mp hae)
      (continuous_oneParticle m F) (continuous_timeZeroOneParticle m u)
  have hall := entire_eq_of_real_eq (analyticOnNhd_wedgeWave m F p)
    (analyticOnNhd_complexSourceWave_boost m u p) (fun η => by
      rw [wedgeWave_ofReal, complexSourceWave_boost_ofReal, hreal])
  exact congrFun hall ζ

end VacuumBellSeparation
