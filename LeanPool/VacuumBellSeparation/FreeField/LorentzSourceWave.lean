/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceCurve
public import LeanPool.VacuumBellSeparation.FreeField.TimeZeroRapidityWave
public import LeanPool.VacuumBellSeparation.FreeField.OneParticleLorentz

/-!
# Actual Cauchy-data waves on Lorentz-transformed boost contours

Physical L2 equality first gives pointwise equality of the continuous real
mass-shell waves. Real Lorentz covariance then identifies the real-rapidity
values, and the genuine entire-function identity theorem proves the full
complex contour identity. No pointwise evaluation of an L2 class is used.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace

theorem complexShellBoost_ofReal (m η : ℝ) (p : EuclideanSpace ℝ (Fin 3)) :
    complexShellBoost m (η : ℂ) p = complexSpacetimeOfReal (onShell m (shellBoost m η p)) := by
  apply Prod.ext
  · exact complexShellBoost_energy_ofReal m η p
  · ext i
    fin_cases i <;>
      simp only [complexShellBoost, ← Complex.ofReal_cosh, Fin.isValue, ← Complex.ofReal_sinh,
        Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val_zero, Matrix.cons_val_one,
        Matrix.cons_val, complexSpacetimeOfReal, onShell, shellBoost, e₁,
        EuclideanSpace.inner_single_left, conj_trivial, one_mul, LinearMap.coe_mk, AddHom.coe_mk,
        PiLp.add_apply, PiLp.smul_apply, PiLp.single_apply, smul_eq_mul, mul_ite, mul_one,
        mul_zero, Complex.ofReal_add, one_ne_zero, Fin.reduceEq, ↓reduceIte, Complex.ofReal_mul,
        Complex.ofReal_sub, Complex.ofReal_one, Complex.ofReal_zero, add_zero]; push_cast; ring

theorem complexified_lorentzBoost_ofReal (m η : ℝ)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    (hfuture : IsOrthochronousMap Λ) (p : EuclideanSpace ℝ (Fin 3)) :
    complexifiedSpacetimeMap Λ (complexShellBoost m (η : ℂ) p) =
      complexSpacetimeOfReal (onShell m (lorentzShellMap m Λ (shellBoost m η p))) := by
  rw [complexShellBoost_ofReal, complexifiedSpacetimeMap_ofReal,
    lorentzMap_onShell m Λ hΛ hfuture]

theorem oneParticle_eq_timeZero_of_L2_eq {m : ℝ} (hm : 0 < m)
    (F : RealTestFunction) (u : TimeZeroSource) (heq : oneParticleL2 hm F = timeZeroL2 hm u) :
    oneParticle m F = timeZeroOneParticle m u := by
  have hae : oneParticle m F =ᵐ[oneParticleMeasure m] timeZeroOneParticle m u := by
    have hF := coeFn_oneParticleL2 hm F
    rw [heq] at hF
    exact hF.symm.trans (coeFn_timeZeroL2 hm u)
  exact Measure.eq_of_ae_eq ((ae_oneParticleMeasure_iff hm).mp hae)
    (continuous_oneParticle m F) (continuous_timeZeroOneParticle m u)

/-- The Lorentz-transformed source-wave identity holds at every complex
rapidity, for the original literal Cauchy-data integral. -/
theorem wedgeWave_compLorentz_eq_complexSourceWave {m : ℝ} (hm : 0 < m)
    (Λ : Spacetime ≃L[ℝ] Spacetime) (hΛ : IsLorentzMap Λ)
    (hfuture : IsOrthochronousMap Λ)
    (F : RealTestFunction) (u : TimeZeroSource) (heq : oneParticleL2 hm F = timeZeroL2 hm u)
    (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    wedgeWave m (F.compCLE Λ) ζ p =
      complexSourceWave u (complexifiedSpacetimeMap Λ (complexShellBoost m ζ p)) := by
  have hreal := oneParticle_eq_timeZero_of_L2_eq hm F u heq
  have hall := entire_eq_of_real_eq (analyticOnNhd_wedgeWave m (F.compCLE Λ) p)
    (analyticOnNhd_complexSourceWave_lorentzBoost m Λ u p) (fun η => by
      rw [wedgeWave_ofReal, oneParticle_lorentzMap m Λ hΛ hfuture,
        complexified_lorentzBoost_ofReal m η Λ hΛ hfuture, hreal]
      exact (complexSourceWave_onShell m u _).symm)
  exact congrFun hall ζ

end VacuumBellSeparation
