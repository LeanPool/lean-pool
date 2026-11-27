/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.CauchyEvolutionL2

/-!
# Actual spatial derivatives of the Cauchy evolution

Directional differentiation commutes with the literal Fourier multipliers.
Applying the established L² derivative theorem to differentiated initial data
therefore differentiates the actual spatial gradient in L². No bounded spatial
derivative on L², or exchange of unproved derivatives, is assumed.
-/

@[expose] public section

namespace VacuumBellSeparation

open MeasureTheory FourierTransform LineDeriv
open scoped SchwartzMap FourierTransform LineDeriv

theorem lineDeriv_fourierMultiplier (w : EuclideanSpace ℝ (Fin 3) → ℂ)
    (hw : Function.HasTemperateGrowth w) (v : EuclideanSpace ℝ (Fin 3))
    (f : SpatialSchwartz) :
    ∂_{v} (SchwartzMap.fourierMultiplierCLM ℂ w f) =
      SchwartzMap.fourierMultiplierCLM ℂ w (∂_{v} f) := by
  have hv : Function.HasTemperateGrowth (inner ℝ · v) :=
    ((innerSL ℝ).flip v).hasTemperateGrowth
  apply (fourierCLE ℂ SpatialSchwartz).injective
  change 𝓕 (∂_{v} (SchwartzMap.fourierMultiplierCLM ℂ w f)) =
    𝓕 (SchwartzMap.fourierMultiplierCLM ℂ w (∂_{v} f))
  simp only [SchwartzMap.fourier_lineDerivOp_eq,
    SchwartzMap.fourierMultiplierCLM_apply, fourier_fourierInv_eq]
  ext ξ
  simp only [smul_apply, SchwartzMap.smulLeftCLM_apply_apply hw,
    SchwartzMap.smulLeftCLM_apply_apply hv, smul_eq_mul, Complex.real_smul]
  ring

theorem lineDeriv_massiveSchwartzPower (m r : ℝ) (v : EuclideanSpace ℝ (Fin 3))
    (f : SpatialSchwartz) :
    ∂_{v} (massiveSchwartzPower m r f) = massiveSchwartzPower m r (∂_{v} f) :=
  lineDeriv_fourierMultiplier _ (hasTemperateGrowth_complex_massiveSchwartzSymbol m r) v f

theorem lineDeriv_massiveSchwartzEvolution (m t : ℝ) (v : EuclideanSpace ℝ (Fin 3))
    (f : SpatialSchwartz) :
    ∂_{v} (massiveSchwartzEvolution m t f) = massiveSchwartzEvolution m t (∂_{v} f) :=
  lineDeriv_fourierMultiplier _ (hasTemperateGrowth_massiveEvolutionPhase m t) v f

theorem lineDeriv_cauchyPositiveData (m : ℝ) (v : EuclideanSpace ℝ (Fin 3))
    (f g : SpatialSchwartz) :
    ∂_{v} (cauchyPositiveData m f g) = cauchyPositiveData m (∂_{v} f) (∂_{v} g) := by
  simp only [cauchyPositiveData, sub_eq_add_neg, lineDerivOp_add,
    lineDerivOp_neg, lineDerivOp_smul, lineDeriv_massiveSchwartzPower]

theorem lineDeriv_cauchyNegativeData (m : ℝ) (v : EuclideanSpace ℝ (Fin 3))
    (f g : SpatialSchwartz) :
    ∂_{v} (cauchyNegativeData m f g) = cauchyNegativeData m (∂_{v} f) (∂_{v} g) := by
  simp only [cauchyNegativeData, lineDerivOp_add, lineDerivOp_smul,
    lineDeriv_massiveSchwartzPower]

theorem lineDeriv_massiveSchwartzCauchy (m t : ℝ) (v : EuclideanSpace ℝ (Fin 3))
    (f g : SpatialSchwartz) :
    ∂_{v} (massiveSchwartzCauchy m t f g) =
      massiveSchwartzCauchy m t (∂_{v} f) (∂_{v} g) := by
  simp only [massiveSchwartzCauchy_eq_phases, lineDerivOp_add,
    lineDeriv_massiveSchwartzEvolution, lineDeriv_cauchyPositiveData,
    lineDeriv_cauchyNegativeData]

theorem lineDeriv_massiveSchwartzCauchyVelocity (m t : ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) (f g : SpatialSchwartz) :
    ∂_{v} (massiveSchwartzCauchyVelocity m t f g) =
      massiveSchwartzCauchyVelocity m t (∂_{v} f) (∂_{v} g) := by
  simp only [massiveSchwartzCauchyVelocity, sub_eq_add_neg, lineDerivOp_add,
    lineDerivOp_neg, lineDerivOp_smul, lineDeriv_massiveSchwartzEvolution,
    lineDeriv_massiveSchwartzPower, lineDeriv_cauchyPositiveData,
    lineDeriv_cauchyNegativeData]

/-- Actual time derivative of each actual spatial directional derivative. -/
theorem hasDerivAt_lineDeriv_massiveSchwartzCauchy_toL2 (m t : ℝ)
    (v : EuclideanSpace ℝ (Fin 3)) (f g : SpatialSchwartz) :
    HasDerivAt (fun s => (∂_{v} (massiveSchwartzCauchy m s f g)).toLp 2)
      ((∂_{v} (massiveSchwartzCauchyVelocity m t f g)).toLp 2) t := by
  simpa only [lineDeriv_massiveSchwartzCauchy, lineDeriv_massiveSchwartzCauchyVelocity] using
    hasDerivAt_massiveSchwartzCauchy_toL2 m t (∂_{v} f) (∂_{v} g)

end VacuumBellSeparation
