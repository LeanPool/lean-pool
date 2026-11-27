/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.EvolutionL2Derivative

/-!
# The genuine massive generator and second derivative on the Schwartz core

The first L² derivative is `i U(t) h f`. Differentiating the actual evolution of
the Schwartz datum `h f` gives the second derivative `-h² U(t)f`. At positive
mass the previously proved identity `h²=m²-Δ` gives the Klein–Gordon equation
in L². No unbounded-operator domain theorem is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform

@[simp] theorem spatialSchwartz_toL2_smul (c : ℂ) (f : SpatialSchwartz) :
    (c • f).toLp 2 volume = c • f.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_smul c f

@[simp] theorem spatialSchwartz_toL2_add (f g : SpatialSchwartz) :
    (f + g).toLp 2 volume = f.toLp 2 volume + g.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_add f g

@[simp] theorem spatialSchwartz_toL2_sub (f g : SpatialSchwartz) :
    (f - g).toLp 2 volume = f.toLp 2 volume - g.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_sub f g

@[simp] theorem spatialSchwartz_toL2_neg (f : SpatialSchwartz) :
    (-f).toLp 2 volume = -f.toLp 2 volume :=
  (SchwartzMap.toLpCLM ℂ ℂ 2 volume).map_neg f

theorem massiveSchwartzEvolution_commute_power (m t r : ℝ) (f : SpatialSchwartz) :
    massiveSchwartzEvolution m t (massiveSchwartzPower m r f) =
      massiveSchwartzPower m r (massiveSchwartzEvolution m t f) := by
  unfold massiveSchwartzEvolution massiveSchwartzPower
  rw [SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply
    (hasTemperateGrowth_massiveEvolutionPhase m t)
    (hasTemperateGrowth_complex_massiveSchwartzSymbol m r),
    SchwartzMap.fourierMultiplierCLM_fourierMultiplierCLM_apply
      (hasTemperateGrowth_complex_massiveSchwartzSymbol m r)
      (hasTemperateGrowth_massiveEvolutionPhase m t), mul_comm]

theorem inverseFourier_massiveFrequencyDerivative (m t : ℝ) (f : SpatialSchwartz) :
    𝓕⁻ (massiveFrequencyDerivative m t (𝓕 f)) =
      Complex.I • massiveSchwartzEvolution m t (massiveSchwartzPower m 1 f) := by
  apply (fourierCLE ℂ SpatialSchwartz).injective
  change 𝓕 (𝓕⁻ (massiveFrequencyDerivative m t (𝓕 f))) =
    𝓕 (Complex.I • massiveSchwartzEvolution m t (massiveSchwartzPower m 1 f))
  rw [fourier_fourierInv_eq, fourier_smul]
  ext ξ
  simp only [massiveFrequencyDerivative, smul_apply,
    massiveFrequencyEvolution_apply, massiveFrequencyEnergy_apply,
    fourier_massiveSchwartzEvolution, massiveSchwartzPower,
    SchwartzMap.fourierMultiplierCLM_apply, fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply (hasTemperateGrowth_complex_massiveSchwartzSymbol m 1),
    smul_eq_mul]

/-- First derivative in the actual physical position L² space. -/
theorem hasDerivAt_massiveSchwartzEvolution_generator (m t : ℝ) (f : SpatialSchwartz) :
    HasDerivAt (fun s => (massiveSchwartzEvolution m s f).toLp 2 volume)
      (Complex.I • (massiveSchwartzEvolution m t (massiveSchwartzPower m 1 f)).toLp 2 volume) t
        := by
  simpa only [inverseFourier_massiveFrequencyDerivative, spatialSchwartz_toL2_smul] using
    hasDerivAt_massiveSchwartzEvolution_toL2 m t f

/-- The derivative field itself has the expected actual second derivative. -/
theorem hasDerivAt_massiveSchwartzEvolution_generator_twice {m : ℝ} (hm : 0 < m)
    (t : ℝ) (f : SpatialSchwartz) :
    HasDerivAt
      (fun s => Complex.I •
        (massiveSchwartzEvolution m s (massiveSchwartzPower m 1 f)).toLp 2 volume)
      (-(massiveSchwartzPower m 2 (massiveSchwartzEvolution m t f)).toLp 2 volume) t := by
  have ht := (hasDerivAt_massiveSchwartzEvolution_generator m t
    (massiveSchwartzPower m 1 f)).const_smul Complex.I
  simpa only [Pi.smul_def, smul_smul, Complex.I_mul_I, neg_one_smul, massiveSchwartzPower_add hm,
    show (1 : ℝ) + 1 = 2 by norm_num, massiveSchwartzEvolution_commute_power] using ht

open Laplacian in
/-- The actual L² second derivative satisfies the massive Klein–Gordon equation. -/
theorem hasDerivAt_massiveSchwartzEvolution_kleinGordon {m : ℝ} (hm : 0 < m)
    (t : ℝ) (f : SpatialSchwartz) :
    HasDerivAt
      (fun s => Complex.I •
        (massiveSchwartzEvolution m s (massiveSchwartzPower m 1 f)).toLp 2 volume)
      ((Δ (massiveSchwartzEvolution m t f)).toLp 2 volume -
        ((m ^ 2 : ℝ) : ℂ) • (massiveSchwartzEvolution m t f).toLp 2 volume) t := by
  simpa only [massiveSchwartzPower_two hm, spatialSchwartz_toL2_sub,
    spatialSchwartz_toL2_smul, neg_sub] using
    hasDerivAt_massiveSchwartzEvolution_generator_twice hm t f

end VacuumBellSeparation
