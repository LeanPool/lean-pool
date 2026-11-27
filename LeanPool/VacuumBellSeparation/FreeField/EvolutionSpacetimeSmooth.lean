/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.EvolutionMassShellMeasure
public import LeanPool.VacuumBellSeparation.FreeField.CauchyEvolutionL2

/-!
# Joint spacetime smoothness of the actual massive Cauchy solution

The smooth graph Fourier integral is identified, with all 2π factors and
signs explicit, with the existing literal spatial Fourier-multiplier
evolution. The positive/negative frequency decomposition then proves joint
smoothness of the actual cosine/sine Cauchy solution.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

open MeasureTheory Filter FourierTransform
open scoped FourierTransform

theorem evolutionFrequencyGraph_character (m : ℝ)
    (ξ : EuclideanSpace ℝ (Fin 3)) (x : Spacetime) :
    (𝐞 (-spacetimeEuclideanPairing (evolutionFrequencyGraph m ξ) x) : ℂ) =
      (𝐞 ⟪ξ, x.2⟫_ℝ : ℂ) * massiveEvolutionPhase m x.1 ξ := by
  have hphase :
      2 * Real.pi * (-spacetimeEuclideanPairing (evolutionFrequencyGraph m ξ) x) =
        2 * Real.pi * ⟪ξ, x.2⟫_ℝ + x.1 * massiveSchwartzSymbol m 1 ξ := by
    simp only [spacetimeEuclideanPairing_apply, evolutionFrequencyGraph, evolutionGraphTime,
      inner_neg_left]
    field_simp [Real.pi_ne_zero]; ring
  simp only [Real.fourierChar_apply, massiveEvolutionPhase]
  rw [hphase, Complex.ofReal_add, add_mul, Complex.exp_add]

theorem spacetimePhaseEvolution_fourier_eq (m : ℝ) (f : SpatialSchwartz) (x : Spacetime) :
    spacetimePhaseEvolution m (𝓕 f) x = massiveSchwartzEvolution m x.1 f x.2 := by
  rw [spacetimePhaseEvolution_eq_integral, massiveSchwartzEvolution,
    SchwartzMap.fourierMultiplierCLM_apply]
  rw [SchwartzMap.fourierInv_coe, Real.fourierInv_eq]
  apply integral_congr_ae
  exact Eventually.of_forall fun ξ => by
    change (𝐞 (-spacetimeEuclideanPairing (evolutionFrequencyGraph m ξ) x) : ℂ) * (𝓕 f) ξ =
      (𝐞 ⟪ξ, x.2⟫_ℝ : ℂ) *
        (SchwartzMap.smulLeftCLM ℂ (massiveEvolutionPhase m x.1) (𝓕 f)) ξ
    rw [evolutionFrequencyGraph_character m ξ x,
      SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_massiveEvolutionPhase m x.1)]
    simp only [smul_eq_mul, mul_assoc]

/-- Genuine smoothness in all four real spacetime coordinates of the actual
positive-frequency evolution of arbitrary spatial Schwartz data. -/
theorem contDiff_massiveSchwartzEvolution_spacetime (m : ℝ) (f : SpatialSchwartz) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Spacetime => massiveSchwartzEvolution m x.1 f x.2) := by
  have heq : spacetimePhaseEvolution m (𝓕 f) =
      (fun x : Spacetime => massiveSchwartzEvolution m x.1 f x.2) :=
    funext (spacetimePhaseEvolution_fourier_eq m f)
  rw [← heq]
  exact contDiff_spacetimePhaseEvolution m (𝓕 f)

theorem contDiff_massiveSchwartzEvolution_neg_spacetime (m : ℝ) (f : SpatialSchwartz) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Spacetime => massiveSchwartzEvolution m (-x.1) f x.2) := by
  have hneg : ContDiff ℝ (⊤ : ℕ∞) (fun x : Spacetime => (-x.1, x.2)) :=
    (contDiff_fst.neg).prodMk contDiff_snd
  exact ContDiff.fun_comp
    (f := fun x : Spacetime => (-x.1, x.2))
    (g := fun x : Spacetime => massiveSchwartzEvolution m x.1 f x.2)
    (contDiff_massiveSchwartzEvolution_spacetime m f) hneg

/-- The actual cosine/sine Cauchy solution is jointly smooth, with no
Schwartz-valued time-differentiability premise. -/
theorem contDiff_massiveSchwartzCauchy_spacetime (m : ℝ) (f g : SpatialSchwartz) :
    ContDiff ℝ (⊤ : ℕ∞) (fun x : Spacetime => massiveSchwartzCauchy m x.1 f g x.2) := by
  have h := (contDiff_massiveSchwartzEvolution_spacetime m (cauchyPositiveData m f g)).add
    (contDiff_massiveSchwartzEvolution_neg_spacetime m (cauchyNegativeData m f g))
  simpa only [massiveSchwartzCauchy_eq_phases, add_apply] using h

theorem contDiff_massiveSchwartzCauchyVelocity_spacetime (m : ℝ) (f g : SpatialSchwartz) :
    ContDiff ℝ (⊤ : ℕ∞)
      (fun x : Spacetime => massiveSchwartzCauchyVelocity m x.1 f g x.2) := by
  exact ((contDiff_massiveSchwartzEvolution_spacetime m
    (massiveSchwartzPower m 1 (cauchyPositiveData m f g))).const_smul Complex.I).sub
      ((contDiff_massiveSchwartzEvolution_neg_spacetime m
        (massiveSchwartzPower m 1 (cauchyNegativeData m f g))).const_smul Complex.I)

end VacuumBellSeparation
