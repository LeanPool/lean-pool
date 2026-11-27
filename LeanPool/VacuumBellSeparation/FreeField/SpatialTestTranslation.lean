/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ComplexSourceWave
public import LeanPool.VacuumBellSeparation.FreeField.LpUnitModulus
public import Mathlib.MeasureTheory.Group.Integral

/-!
# Literal spatial translation of compact Cauchy data and physical vectors

Translation by a sends f(x) to f(x-a). The original unnormalized Fourier
transform therefore acquires exp(-i p.a), including at complex momenta.
The corresponding map on the entire physical L2 space is unitary.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace

/-- Spatial test translate. -/
noncomputable def spatialTestTranslate (a : EuclideanSpace ℝ (Fin 3))
    (f : SpatialTestFunction) : SpatialTestFunction :=
  ⟨fun x => f.1 (x - a), f.2.1.comp (contDiff_id.sub contDiff_const),
    f.2.2.comp_homeomorph (Homeomorph.subRight a)⟩

theorem tsupport_spatialTestTranslate (a : EuclideanSpace ℝ (Fin 3))
    (f : SpatialTestFunction) :
    tsupport (spatialTestTranslate a f).1 = (fun x => x - a) ⁻¹' tsupport f.1 :=
  tsupport_comp_eq_preimage f.1 (Homeomorph.subRight a)

theorem spatialTestTranslate_neg_cancel (a : EuclideanSpace ℝ (Fin 3))
    (f : SpatialTestFunction) : spatialTestTranslate (-a) (spatialTestTranslate a f) = f := by
  apply Subtype.ext
  funext x
  simp only [spatialTestTranslate, sub_neg_eq_add, add_sub_cancel_right]

theorem spatialDot_ofReal_add (z : Fin 3 → ℂ) (x a : EuclideanSpace ℝ (Fin 3)) :
    spatialDot z (fun i => ((x + a) i : ℂ)) =
      spatialDot z (fun i => (x i : ℂ)) + spatialDot z (fun i => (a i : ℂ)) := by
  simp only [spatialDot, PiLp.add_apply, Complex.ofReal_add, mul_add, Finset.sum_add_distrib]

theorem complexSpatialFourier_translate (a : EuclideanSpace ℝ (Fin 3))
    (f : SpatialTestFunction) (z : Fin 3 → ℂ) :
    complexSpatialFourier (spatialTestTranslate a f) z =
      Complex.exp (-(Complex.I * spatialDot z (fun i => (a i : ℂ)))) *
        complexSpatialFourier f z := by
  unfold complexSpatialFourier
  rw [← integral_add_right_eq_self
    (fun x : EuclideanSpace ℝ (Fin 3) =>
      Complex.exp (-(Complex.I * spatialDot z (fun i => (x i : ℂ)))) *
        ((spatialTestTranslate a f).1 x : ℂ)) a]
  simp only [spatialTestTranslate, add_sub_cancel_right, spatialDot_ofReal_add]
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [mul_add, neg_add, Complex.exp_add]
    ring

/-- Time zero translate. -/
noncomputable def timeZeroTranslate (a : EuclideanSpace ℝ (Fin 3))
    (u : TimeZeroSource) : TimeZeroSource :=
  (spatialTestTranslate a u.1, spatialTestTranslate a u.2)

theorem complexSourceWave_translate (a : EuclideanSpace ℝ (Fin 3))
    (u : TimeZeroSource) (z : ℂ × (Fin 3 → ℂ)) :
    complexSourceWave (timeZeroTranslate a u) z =
      Complex.exp (-(Complex.I * spatialDot z.2 (fun i => (a i : ℂ)))) *
        complexSourceWave u z := by
  simp only [complexSourceWave, timeZeroTranslate, complexSpatialFourier_translate]
  ring

/-- Spatial translation phase given by `Complex.exp (-(Complex.I * (⟪p, a⟫_ℝ : ℂ)))`. -/
noncomputable def spatialTranslationPhase (a p : EuclideanSpace ℝ (Fin 3)) : ℂ :=
  Complex.exp (-(Complex.I * (⟪p, a⟫_ℝ : ℂ)))

theorem measurable_spatialTranslationPhase (a : EuclideanSpace ℝ (Fin 3)) :
    Measurable (spatialTranslationPhase a) := by
  unfold spatialTranslationPhase
  fun_prop

theorem norm_spatialTranslationPhase (a p : EuclideanSpace ℝ (Fin 3)) :
    ‖spatialTranslationPhase a p‖ = 1 := by
  rw [spatialTranslationPhase, Complex.norm_exp]
  simp

/-- Linear isometry equivalence for the one particle spatial translation, of type `Lp ℂ 2
(oneParticleMeasure m) ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m)`. -/
noncomputable def oneParticleSpatialTranslation (m : ℝ)
    (a : EuclideanSpace ℝ (Fin 3)) :
    Lp ℂ 2 (oneParticleMeasure m) ≃ₗᵢ[ℂ] Lp ℂ 2 (oneParticleMeasure m) :=
  lpUnitModulus (oneParticleMeasure m) (spatialTranslationPhase a)
    (measurable_spatialTranslationPhase a) (norm_spatialTranslationPhase a)

theorem oneParticleSpatialTranslation_ae (m : ℝ) (a : EuclideanSpace ℝ (Fin 3))
    (ψ : Lp ℂ 2 (oneParticleMeasure m)) :
    oneParticleSpatialTranslation m a ψ =ᵐ[oneParticleMeasure m]
      fun p => spatialTranslationPhase a p * ψ p :=
  lpUnitModulus_ae _ _ _ _ ψ

theorem timeZeroOneParticle_translate (m : ℝ) (a : EuclideanSpace ℝ (Fin 3))
    (u : TimeZeroSource) (p : EuclideanSpace ℝ (Fin 3)) :
    timeZeroOneParticle m (timeZeroTranslate a u) p =
      spatialTranslationPhase a p * timeZeroOneParticle m u p := by
  rw [← complexSourceWave_onShell, complexSourceWave_translate,
    real_spatialDot, complexSourceWave_onShell]
  rfl

theorem timeZeroL2_translate {m : ℝ} (hm : 0 < m)
    (a : EuclideanSpace ℝ (Fin 3)) (u : TimeZeroSource) :
    timeZeroL2 hm (timeZeroTranslate a u) = oneParticleSpatialTranslation m a
      (timeZeroL2 hm u) := by
  apply Lp.ext
  filter_upwards [coeFn_timeZeroL2 hm (timeZeroTranslate a u),
    oneParticleSpatialTranslation_ae m a (timeZeroL2 hm u), coeFn_timeZeroL2 hm u]
    with p hT hU hu
  rw [hT, hU, hu, timeZeroOneParticle_translate]

end VacuumBellSeparation
