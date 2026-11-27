/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.SchwartzEvolutionDefs
public import LeanPool.VacuumBellSeparation.FreeField.SchwartzKleinGordon

/-!
# Actual real-time massive evolution on the Schwartz core

These are literal Fourier multipliers in the normalized frequency convention.
Temperate growth is proved for every real time, so the multipliers do not use
the default zero branch. This file establishes the group law, the actual
frequency formula, its scalar time derivative and Plancherel norm conservation.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped SchwartzMap FourierTransform
open FourierTransform MeasureTheory





theorem hasTemperateGrowth_massiveEvolutionPhase (m t : ℝ) :
    Function.HasTemperateGrowth (massiveEvolutionPhase m t) := by
  exact Complex.hasTemperateGrowth_exp_mul_I.comp
    ((Function.HasTemperateGrowth.const t).mul (hasTemperateGrowth_massiveSchwartzSymbol m 1))

@[simp] theorem norm_massiveEvolutionPhase (m t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    ‖massiveEvolutionPhase m t ξ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

@[simp] theorem massiveEvolutionPhase_zero (m : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    massiveEvolutionPhase m 0 ξ = 1 := by simp [massiveEvolutionPhase]

theorem massiveEvolutionPhase_add (m s t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    massiveEvolutionPhase m (s + t) ξ =
      massiveEvolutionPhase m s ξ * massiveEvolutionPhase m t ξ := by
  simp only [massiveEvolutionPhase, add_mul, Complex.ofReal_add, Complex.exp_add]

theorem hasDerivAt_massiveEvolutionPhase (m t : ℝ) (ξ : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun s => massiveEvolutionPhase m s ξ)
      (massiveEvolutionPhase m t ξ * ((massiveSchwartzSymbol m 1 ξ : ℂ) * Complex.I)) t := by
  have h := (((hasDerivAt_id t).mul_const (massiveSchwartzSymbol m 1 ξ)).ofReal_comp.mul_const
    Complex.I).cexp
  simpa only [one_mul, id_eq, massiveEvolutionPhase] using! h



theorem fourier_massiveSchwartzEvolution (m t : ℝ) (f : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    (𝓕 (massiveSchwartzEvolution m t f)) ξ = massiveEvolutionPhase m t ξ * (𝓕 f) ξ := by
  rw [massiveSchwartzEvolution, SchwartzMap.fourierMultiplierCLM_apply,
    fourier_fourierInv_eq, SchwartzMap.smulLeftCLM_apply_apply
      (hasTemperateGrowth_massiveEvolutionPhase m t)]
  rfl

@[simp] theorem massiveSchwartzEvolution_zero (m : ℝ) (f : SpatialSchwartz) :
    massiveSchwartzEvolution m 0 f = f := by
  have hphase : massiveEvolutionPhase m 0 = fun _ => 1 :=
    funext (massiveEvolutionPhase_zero m)
  simp [massiveSchwartzEvolution, hphase]

theorem massiveSchwartzEvolution_add (m s t : ℝ) (f : SpatialSchwartz) :
    massiveSchwartzEvolution m s (massiveSchwartzEvolution m t f) =
      massiveSchwartzEvolution m (s + t) f := by
  unfold massiveSchwartzEvolution
  rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (hasTemperateGrowth_massiveEvolutionPhase m s)
    (hasTemperateGrowth_massiveEvolutionPhase m t)]
  congr 2
  funext ξ
  exact (massiveEvolutionPhase_add m s t ξ).symm

theorem massiveSchwartzEvolution_neg (m t : ℝ) (f : SpatialSchwartz) :
    massiveSchwartzEvolution m (-t) (massiveSchwartzEvolution m t f) = f := by
  rw [massiveSchwartzEvolution_add, neg_add_cancel, massiveSchwartzEvolution_zero]

/-- The genuine scalar derivative of each Fourier coefficient. -/
theorem hasDerivAt_fourier_massiveSchwartzEvolution (m t : ℝ) (f : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    HasDerivAt (fun s => (𝓕 (massiveSchwartzEvolution m s f)) ξ)
      ((massiveEvolutionPhase m t ξ *
        ((massiveSchwartzSymbol m 1 ξ : ℂ) * Complex.I)) * (𝓕 f) ξ) t := by
  simpa only [fourier_massiveSchwartzEvolution] using
    (hasDerivAt_massiveEvolutionPhase m t ξ).mul_const ((𝓕 f) ξ)

/-- Plancherel norm conservation for the actual real-time evolution. -/
theorem integral_norm_sq_massiveSchwartzEvolution (m t : ℝ) (f : SpatialSchwartz) :
    ∫ x, ‖massiveSchwartzEvolution m t f x‖ ^ 2 = ∫ x, ‖f x‖ ^ 2 := by
  rw [← SchwartzMap.integral_norm_sq_fourier (massiveSchwartzEvolution m t f),
    ← SchwartzMap.integral_norm_sq_fourier f]
  apply integral_congr_ae
  exact Filter.Eventually.of_forall fun ξ => by
    change ‖(𝓕 (massiveSchwartzEvolution m t f)) ξ‖ ^ 2 = ‖(𝓕 f) ξ‖ ^ 2
    rw [fourier_massiveSchwartzEvolution, norm_mul, norm_massiveEvolutionPhase, one_mul]



theorem hasTemperateGrowth_massiveCosine (m t : ℝ) :
    Function.HasTemperateGrowth
      (fun ξ => (Real.cos (t * massiveSchwartzSymbol m 1 ξ) : ℂ)) :=
  Complex.hasTemperateGrowth_ofReal.comp (Real.hasTemperateGrowth_cos.comp
    ((Function.HasTemperateGrowth.const t).mul (hasTemperateGrowth_massiveSchwartzSymbol m 1)))



theorem hasTemperateGrowth_massiveSine (m t : ℝ) :
    Function.HasTemperateGrowth (fun ξ =>
      ((massiveSchwartzSymbol m (-1) ξ * Real.sin (t * massiveSchwartzSymbol m 1 ξ) : ℝ) : ℂ)) :=
  Complex.hasTemperateGrowth_ofReal.comp ((hasTemperateGrowth_massiveSchwartzSymbol m (-1)).mul
    (Real.hasTemperateGrowth_sin.comp ((Function.HasTemperateGrowth.const t).mul
      (hasTemperateGrowth_massiveSchwartzSymbol m 1))))

theorem fourier_massiveSchwartzCosine (m t : ℝ) (f : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    (𝓕 (massiveSchwartzCosine m t f)) ξ =
      (Real.cos (t * massiveSchwartzSymbol m 1 ξ) : ℂ) * (𝓕 f) ξ := by
  rw [massiveSchwartzCosine, SchwartzMap.fourierMultiplierCLM_apply,
    fourier_fourierInv_eq, SchwartzMap.smulLeftCLM_apply_apply
      (hasTemperateGrowth_massiveCosine m t)]
  rfl

theorem fourier_massiveSchwartzSine (m t : ℝ) (f : SpatialSchwartz)
    (ξ : EuclideanSpace ℝ (Fin 3)) :
    (𝓕 (massiveSchwartzSine m t f)) ξ =
      ((massiveSchwartzSymbol m (-1) ξ * Real.sin (t * massiveSchwartzSymbol m 1 ξ) : ℝ) : ℂ)
        * (𝓕 f) ξ := by
  rw [massiveSchwartzSine, SchwartzMap.fourierMultiplierCLM_apply,
    fourier_fourierInv_eq, SchwartzMap.smulLeftCLM_apply_apply
      (hasTemperateGrowth_massiveSine m t)]
  rfl



@[simp] theorem massiveSchwartzCauchy_zero (m : ℝ) (f g : SpatialSchwartz) :
    massiveSchwartzCauchy m 0 f g = f := by
  simp [massiveSchwartzCauchy, massiveSchwartzCosine, massiveSchwartzSine]

/-- At positive mass this is exactly the manuscript's physical dispersion,
with the frequency change `p = 2πξ` made explicit. -/
theorem fourier_massiveSchwartzCauchy {m : ℝ} (hm : 0 < m) (t : ℝ)
    (f g : SpatialSchwartz) (ξ : EuclideanSpace ℝ (Fin 3)) :
    (𝓕 (massiveSchwartzCauchy m t f g)) ξ =
      (Real.cos (t * dispersion m ((2 * Real.pi) • ξ)) : ℂ) * (𝓕 f) ξ +
      (((dispersion m ((2 * Real.pi) • ξ))⁻¹ *
        Real.sin (t * dispersion m ((2 * Real.pi) • ξ)) : ℝ) : ℂ) * (𝓕 g) ξ := by
  change ((SchwartzMap.fourierTransformCLM ℂ)
    (massiveSchwartzCosine m t f + massiveSchwartzSine m t g)) ξ = _
  rw [map_add]
  change (𝓕 (massiveSchwartzCosine m t f)) ξ +
    (𝓕 (massiveSchwartzSine m t g)) ξ = _
  simp only [
    fourier_massiveSchwartzCosine, fourier_massiveSchwartzSine,
    massiveSchwartzSymbol_one hm, massiveSchwartzSymbol_neg_one hm]

end VacuumBellSeparation
