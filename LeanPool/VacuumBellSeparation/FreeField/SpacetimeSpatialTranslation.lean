/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SpatialTestTranslation
public import LeanPool.VacuumBellSeparation.FreeField.SourceTranslation

/-!
# Literal spatial translation of spacetime tests and entire wedge waves

The same physical translation unitary acts on original spacetime test
vectors. Its full complex-rapidity wave acquires the actual complex
Fourier phase, proved by a volume-preserving translation of the integral.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory
open scoped InnerProductSpace

/-- Spacetime spatial translate. -/
noncomputable def spacetimeSpatialTranslate (a : EuclideanSpace ℝ (Fin 3))
    (F : RealTestFunction) : RealTestFunction :=
  ⟨fun x => F.1 (x - (0, a)), F.2.1.comp (contDiff_id.sub contDiff_const),
    F.2.2.comp_homeomorph (Homeomorph.subRight (0, a))⟩

theorem tsupport_spacetimeSpatialTranslate (a : EuclideanSpace ℝ (Fin 3))
    (F : RealTestFunction) :
    tsupport (spacetimeSpatialTranslate a F).1 =
      (fun x => x - (0, a)) ⁻¹' tsupport F.1 :=
  tsupport_comp_eq_preimage F.1 (Homeomorph.subRight (0, a))

theorem boostPhase_add (m : ℝ) (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3))
    (x y : Spacetime) : boostPhase m ζ p (x + y) = boostPhase m ζ p x + boostPhase m ζ p y := by
  rw [← boostPhaseCLM_apply, map_add, boostPhaseCLM_apply, boostPhaseCLM_apply]

theorem wedgeWave_spatialTranslate (m : ℝ) (a : EuclideanSpace ℝ (Fin 3))
    (F : RealTestFunction) (ζ : ℂ) (p : EuclideanSpace ℝ (Fin 3)) :
    wedgeWave m (spacetimeSpatialTranslate a F) ζ p =
      Complex.exp (-(Complex.I * spatialDot (complexShellBoost m ζ p).2
        (fun i => (a i : ℂ)))) * wedgeWave m F ζ p := by
  have : (volume : Measure Spacetime).IsAddHaarMeasure :=
    Measure.prod.instIsAddHaarMeasure _ _
  unfold wedgeWave
  rw [← integral_add_right_eq_self
    (fun x : Spacetime => Complex.exp (Complex.I * boostPhase m (-ζ) p x) *
      ((spacetimeSpatialTranslate a F).1 x : ℂ)) (0, a)]
  simp only [spacetimeSpatialTranslate, add_sub_cancel_right, boostPhase_add]
  have ha : boostPhase m (-ζ) p (0, a) =
      -spatialDot (complexShellBoost m ζ p).2 (fun i => (a i : ℂ)) := by
    rw [← complexShellBoost_phase]
    simp
  rw [← integral_const_mul]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun x => by
    dsimp only
    rw [ha, mul_add, Complex.exp_add, mul_neg]
    ring

theorem oneParticle_spatialTranslate (m : ℝ) (a : EuclideanSpace ℝ (Fin 3))
    (F : RealTestFunction) (p : EuclideanSpace ℝ (Fin 3)) :
    oneParticle m (spacetimeSpatialTranslate a F) p =
      spatialTranslationPhase a p * oneParticle m F p := by
  rw [← wedgeWave_zero, wedgeWave_spatialTranslate, wedgeWave_zero]
  congr 1
  simp only [complexShellBoost, Complex.cosh_zero, Complex.sinh_zero,
    mul_one, mul_zero, add_zero]
  have hp : ![(p 0 : ℂ), (p 1 : ℂ), (p 2 : ℂ)] = (fun i => (p i : ℂ)) := by
    ext i
    fin_cases i <;> rfl
  rw [hp, real_spatialDot]
  rfl

theorem oneParticleL2_spatialTranslate {m : ℝ} (hm : 0 < m)
    (a : EuclideanSpace ℝ (Fin 3)) (F : RealTestFunction) :
    oneParticleL2 hm (spacetimeSpatialTranslate a F) =
      oneParticleSpatialTranslation m a (oneParticleL2 hm F) := by
  apply Lp.ext
  filter_upwards [coeFn_oneParticleL2 hm (spacetimeSpatialTranslate a F),
    oneParticleSpatialTranslation_ae m a (oneParticleL2 hm F), coeFn_oneParticleL2 hm F]
    with p hT hU hF
  rw [hT, hU, hF, oneParticle_spatialTranslate]

theorem spacetimeSpatialTranslate_support_wedge_zero (ℓ : ℝ)
    (F : RealTestFunction) (hF : tsupport F.1 ⊆ leftWedge ℓ) :
    tsupport (spacetimeSpatialTranslate (-(ℓ • e₁)) F).1 ⊆ leftWedge 0 := by
  rw [tsupport_spacetimeSpatialTranslate]
  intro x hx
  have h := hF hx
  change ⟪e₁, x.2 - -(ℓ • e₁)⟫_ℝ + |x.1 - 0| < ℓ at h
  rw [sub_neg_eq_add, inner_e₁_add_smul, sub_zero] at h
  change ⟪e₁, x.2⟫_ℝ + |x.1| < 0
  linarith

end VacuumBellSeparation
