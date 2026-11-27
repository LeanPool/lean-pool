/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.Defs
public import Mathlib.MeasureTheory.Function.LocallyIntegrable

/-!
# Basic properties of the one-particle wave functions

First steps towards integrability in the one-particle definitions:

* `integrable_oneParticleIntegrand`: the integrand defining `oneParticle m F 𝐩` is
  integrable (it is continuous with compact support), so `oneParticle` is a genuine
  integral;
* `oneParticle_add`: `κ_m(F + G) = κ_m F + κ_m G`;
* `norm_oneParticle_le`: `|κ_m F(𝐩)| ≤ ∫ |F|`.

The decay of `κ_m F` in `𝐩` and the integrability of the integrand of `oneParticleInner`
are proved in `FreeField/Decay.lean`.
-/

@[expose] public section

open scoped InnerProductSpace

namespace VacuumBellSeparation

/-- The integrand of `oneParticle m F 𝐩`. -/
noncomputable def oneParticleIntegrand (m : ℝ) (F : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) (x : Spacetime) : ℂ :=
  Complex.exp (Complex.I * ((dispersion m p * x.1 - ⟪p, x.2⟫_ℝ : ℝ) : ℂ)) * (F.1 x : ℂ)

theorem oneParticle_eq_integral (m : ℝ) (F : RealTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m F p = ∫ x, oneParticleIntegrand m F p x := rfl

theorem continuous_testFunction (F : RealTestFunction) : Continuous F.1 :=
  F.2.1.continuous

theorem integrable_oneParticleIntegrand (m : ℝ) (F : RealTestFunction)
    (p : EuclideanSpace ℝ (Fin 3)) :
    MeasureTheory.Integrable (oneParticleIntegrand m F p) := by
  apply Continuous.integrable_of_hasCompactSupport
  · exact (Complex.continuous_exp.comp (continuous_const.mul (Complex.continuous_ofReal.comp
      ((continuous_const.mul continuous_fst).sub (continuous_const.inner continuous_snd))))).mul
      (Complex.continuous_ofReal.comp (continuous_testFunction F))
  · exact (F.2.2.comp_left Complex.ofReal_zero).mul_left

/-- `κ_m(F + G) = κ_m F + κ_m G`. -/
theorem oneParticle_add (m : ℝ) (F G : RealTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m (F + G) p = oneParticle m F p + oneParticle m G p := by
  simp only [oneParticle_eq_integral]
  rw [← MeasureTheory.integral_add (integrable_oneParticleIntegrand m F p)
    (integrable_oneParticleIntegrand m G p)]
  congr 1
  funext x
  simp only [oneParticleIntegrand]
  change _ * ((F.1 x + G.1 x : ℝ) : ℂ) = _
  push_cast
  ring

/-- `|κ_m F(𝐩)| ≤ ∫ |F|`. -/
theorem norm_oneParticle_le (m : ℝ) (F : RealTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    ‖oneParticle m F p‖ ≤ ∫ x, |F.1 x| := by
  rw [oneParticle_eq_integral]
  refine (MeasureTheory.norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  congr 1
  funext x
  simp only [oneParticleIntegrand, norm_mul, Complex.norm_exp_I_mul_ofReal, one_mul,
    Complex.norm_real, Real.norm_eq_abs]

end VacuumBellSeparation
