/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CauchyEvolutionDefs
public import LeanPool.VacuumBellSeparation.FreeField.EvolutionGenerator

/-!
# The actual Klein–Gordon Cauchy solution in L²

The literal cosine/sine solution is identified with its two frequency parts.
The genuine first and second L² derivatives then follow from the phase
evolution theorem. The initial position and velocity are the given Schwartz
data.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory FourierTransform
open scoped SchwartzMap FourierTransform





/-- Exact identification with the original literal cosine/sine multipliers. -/
theorem massiveSchwartzCauchy_eq_phases (m t : ℝ) (f g : SpatialSchwartz) :
    massiveSchwartzCauchy m t f g =
      massiveSchwartzEvolution m t (cauchyPositiveData m f g) +
        massiveSchwartzEvolution m (-t) (cauchyNegativeData m f g) := by
  apply (fourierCLE ℂ SpatialSchwartz).injective
  change 𝓕 (massiveSchwartzCauchy m t f g) =
    𝓕 (massiveSchwartzEvolution m t (cauchyPositiveData m f g) +
      massiveSchwartzEvolution m (-t) (cauchyNegativeData m f g))
  rw [massiveSchwartzCauchy, FourierTransform.fourier_add, FourierTransform.fourier_add]
  ext ξ
  simp only [add_apply, fourier_massiveSchwartzCosine,
    fourier_massiveSchwartzSine, fourier_massiveSchwartzEvolution,
    cauchyPositiveData, cauchyNegativeData, FourierTransform.fourier_smul,
      FourierTransform.fourier_add,
    sub_eq_add_neg, FourierTransform.fourier_neg, massiveSchwartzPower,
    SchwartzMap.fourierMultiplierCLM_apply, fourier_fourierInv_eq,
    SchwartzMap.smulLeftCLM_apply_apply
      (hasTemperateGrowth_complex_massiveSchwartzSymbol m (-1)),
    add_apply, neg_apply, smul_apply, smul_eq_mul,
    massiveEvolutionPhase, Complex.ofReal_cos, Complex.ofReal_sin,
    Complex.cos, Complex.sin, neg_mul,
    Complex.ofReal_neg, Complex.ofReal_mul]
  ring_nf

theorem hasDerivAt_massiveSchwartzEvolution_neg_generator (m t : ℝ) (f : SpatialSchwartz) :
    HasDerivAt (fun s => (massiveSchwartzEvolution m (-s) f).toLp 2)
      (-(Complex.I • (massiveSchwartzEvolution m (-t) (massiveSchwartzPower m 1 f)).toLp 2)) t := by
  simpa only [Function.comp_def, neg_one_smul] using
    (hasDerivAt_massiveSchwartzEvolution_generator m (-t) f).scomp t (hasDerivAt_neg t)



theorem hasDerivAt_massiveSchwartzCauchy_toL2 (m t : ℝ) (f g : SpatialSchwartz) :
    HasDerivAt (fun s => (massiveSchwartzCauchy m s f g).toLp 2)
      ((massiveSchwartzCauchyVelocity m t f g).toLp 2) t := by
  have ht := (hasDerivAt_massiveSchwartzEvolution_generator m t (cauchyPositiveData m f g)).add
    (hasDerivAt_massiveSchwartzEvolution_neg_generator m t (cauchyNegativeData m f g))
  simpa only [massiveSchwartzCauchy_eq_phases, spatialSchwartz_toL2_add,
    massiveSchwartzCauchyVelocity, spatialSchwartz_toL2_sub, spatialSchwartz_toL2_smul,
    sub_eq_add_neg, spatialSchwartz_toL2_neg, spatialSchwartz_toL2_smul,
    Pi.add_def, Pi.smul_def, Pi.neg_def, Pi.add_apply, Pi.smul_apply, Pi.neg_apply] using ht

@[simp] theorem massiveSchwartzCauchyVelocity_zero {m : ℝ} (hm : 0 < m)
    (f g : SpatialSchwartz) : massiveSchwartzCauchyVelocity m 0 f g = g := by
  simp only [massiveSchwartzCauchyVelocity, neg_zero, massiveSchwartzEvolution_zero,
    cauchyPositiveData, cauchyNegativeData, map_smul, map_sub, map_add,
    massiveSchwartzPower_add hm, show (1 : ℝ) + -1 = 0 by norm_num,
    massiveSchwartzPower_zero, ContinuousLinearMap.id_apply]
  ext ξ
  simp only [smul_apply, sub_apply, add_apply, smul_eq_mul]
  ring_nf
  simp [Complex.I_sq]

/-- Second L² derivative of the actual Cauchy solution. -/
theorem hasDerivAt_massiveSchwartzCauchyVelocity_toL2 {m : ℝ} (hm : 0 < m)
    (t : ℝ) (f g : SpatialSchwartz) :
    HasDerivAt (fun s => (massiveSchwartzCauchyVelocity m s f g).toLp 2)
      (-(massiveSchwartzPower m 2 (massiveSchwartzCauchy m t f g)).toLp 2) t := by
  have hp := hasDerivAt_massiveSchwartzEvolution_generator_twice hm t
    (cauchyPositiveData m f g)
  have hn := (hasDerivAt_massiveSchwartzEvolution_generator_twice hm (-t)
    (cauchyNegativeData m f g)).scomp t (hasDerivAt_neg t)
  have hn' : HasDerivAt
      (fun s => Complex.I •
        (massiveSchwartzEvolution m (-s) (massiveSchwartzPower m 1
          (cauchyNegativeData m f g))).toLp 2)
      ((massiveSchwartzPower m 2
        (massiveSchwartzEvolution m (-t) (cauchyNegativeData m f g))).toLp 2) t := by
    simpa only [Function.comp_def, neg_one_smul, neg_neg] using hn
  refine ((hp.sub hn').congr_of_eventuallyEq
    (Filter.Eventually.of_forall fun s => ?_)).congr_deriv ?_
  · simp only [massiveSchwartzCauchyVelocity, spatialSchwartz_toL2_sub,
      spatialSchwartz_toL2_smul, Pi.sub_apply]
  · rw [massiveSchwartzCauchy_eq_phases, map_add, spatialSchwartz_toL2_add]
    simp only [neg_add_rev, sub_eq_add_neg, add_comm]

open Laplacian in
/-- The literal cosine/sine Cauchy solution solves the massive equation in L². -/
theorem hasDerivAt_massiveSchwartzCauchy_kleinGordon {m : ℝ} (hm : 0 < m)
    (t : ℝ) (f g : SpatialSchwartz) :
    HasDerivAt (fun s => (massiveSchwartzCauchyVelocity m s f g).toLp 2)
      ((Δ (massiveSchwartzCauchy m t f g)).toLp 2 -
        ((m ^ 2 : ℝ) : ℂ) • (massiveSchwartzCauchy m t f g).toLp 2) t := by
  simpa only [massiveSchwartzPower_two hm, spatialSchwartz_toL2_sub,
    spatialSchwartz_toL2_smul, neg_sub] using
    hasDerivAt_massiveSchwartzCauchyVelocity_toL2 hm t f g

end VacuumBellSeparation
