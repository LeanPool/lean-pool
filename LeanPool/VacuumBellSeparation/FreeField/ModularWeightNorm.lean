/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.ModularWeightCompression
public import LeanPool.VacuumBellSeparation.FreeField.SourceModularPowers

/-!
# The actual squared modular source weight

The product G^(1/2-c) Gbar^c is identified with continuous scalar calculus
of the normalized commutation operator. Its adjoint square has the literal
function used by the compression inequality, including both spectral endpoints.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap Gaussian
open scoped InnerProductSpace

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Modular weight operator given by `(1 + T) ^ (1 / 2 - c) * (1 - T) ^ c`. -/
noncomputable def modularWeightOperator (T : E →L[ℂ] E) (c : ℝ) : E →L[ℂ] E :=
  (1 + T) ^ (1 / 2 - c) * (1 - T) ^ c

theorem modularWeightOperator_eq_cfc {T : E →L[ℂ] E}
    (hT : IsSelfAdjoint T) (hnorm : ‖T‖ ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    modularWeightOperator T c =
      cfc (fun x : ℝ => (1 + x) ^ (1 / 2 - c) * (1 - x) ^ c) T := by
  have hp : Continuous (fun x : ℝ => x ^ (1 / 2 - c)) :=
    Real.continuous_rpow_const (sub_nonneg.mpr hc2)
  have hq : Continuous (fun x : ℝ => x ^ c) := Real.continuous_rpow_const hc
  have hplus : (1 + T) ^ (1 / 2 - c) =
      cfc (fun x : ℝ => (1 + x) ^ (1 / 2 - c)) T := by
    rw [CFC.rpow_eq_cfc_real (show 0 ≤ (1 + T) from gramPlus_nonneg hT hnorm),
      ← cfc_one_add_id T hT]
    simpa only [Function.comp_def] using
      (cfc_comp' (fun x : ℝ => x ^ (1 / 2 - c)) (fun x : ℝ => 1 + x) T
        hp.continuousOn (continuous_const.add continuous_id).continuousOn hT).symm
  have hminus : (1 - T) ^ c = cfc (fun x : ℝ => (1 - x) ^ c) T := by
    rw [CFC.rpow_eq_cfc_real (show 0 ≤ (1 - T) from gramMinus_nonneg hT hnorm),
      ← cfc_one_sub_id T hT]
    simpa only [Function.comp_def] using
      (cfc_comp' (fun x : ℝ => x ^ c) (fun x : ℝ => 1 - x) T
        hq.continuousOn (continuous_const.sub continuous_id).continuousOn hT).symm
  rw [modularWeightOperator, hplus, hminus,
    ← cfc_mul (fun x : ℝ => (1 + x) ^ (1 / 2 - c))
      (fun x : ℝ => (1 - x) ^ c) T
      (hp.comp (continuous_const.add continuous_id)).continuousOn
      (hq.comp (continuous_const.sub continuous_id)).continuousOn]

theorem modularWeightOperator_adjoint_mul {T : E →L[ℂ] E}
    (hT : IsSelfAdjoint T) (hnorm : ‖T‖ ≤ 1)
    {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    (modularWeightOperator T c).adjoint * modularWeightOperator T c =
      cfc (modularWeightSquareFunction (2 * c)) T := by
  let f : ℝ → ℝ := fun x => (1 + x) ^ (1 / 2 - c) * (1 - x) ^ c
  have hf : Continuous f :=
    ((Real.continuous_rpow_const (sub_nonneg.mpr hc2)).comp
      (continuous_const.add continuous_id)).mul
        ((Real.continuous_rpow_const hc).comp (continuous_const.sub continuous_id))
  have hs (x : ℝ) (hx : x ∈ spectrum ℝ T) : 0 ≤ 1 + x ∧ 0 ≤ 1 - x := by
    have hh := spectrum_mem_Icc_of_norm_le_one hnorm hx
    constructor <;> linarith [hh.1, hh.2]
  have hfpos : 0 ≤ cfc f T := cfc_nonneg fun x hx =>
    mul_nonneg (Real.rpow_nonneg (hs x hx).1 _) (Real.rpow_nonneg (hs x hx).2 _)
  rw [modularWeightOperator_eq_cfc hT hnorm hc hc2, hfpos.isSelfAdjoint.adjoint_eq,
    ← cfc_mul f f T hf.continuousOn hf.continuousOn]
  apply cfc_congr
  intro x hx
  change ((1 + x) ^ (1 / 2 - c) * (1 - x) ^ c) *
    ((1 + x) ^ (1 / 2 - c) * (1 - x) ^ c) = _
  calc
    _ = ((1 + x) ^ (1 / 2 - c) * (1 + x) ^ (1 / 2 - c)) *
        ((1 - x) ^ c * (1 - x) ^ c) := by ring
    _ = (1 + x) ^ ((1 / 2 - c) + (1 / 2 - c)) * (1 - x) ^ (c + c) := by
      rw [← Real.rpow_add_of_nonneg (hs x hx).1 (sub_nonneg.mpr hc2) (sub_nonneg.mpr hc2),
        ← Real.rpow_add_of_nonneg (hs x hx).2 hc hc]
    _ = _ := by unfold modularWeightSquareFunction; congr 2 <;> ring

variable {m : ℝ} (hm : 0 < m) (U : Set (EuclideanSpace ℝ (Fin 3)))

theorem sourceModularWeight_eq_modularWeightOperator (c : ℝ) :
    sourceModularWeight hm U c =
      modularWeightOperator (normalizedCommutation (complexSourceCommutation hm U)) c := by
  rw [sourceModularWeight, sourceGram_eq_normalized_commutation, conjugateSourceGram_eq]
  rfl

theorem sourceModularWeight_adjoint_mul {c : ℝ} (hc : 0 ≤ c) (hc2 : c ≤ 1 / 2) :
    (sourceModularWeight hm U c).adjoint * sourceModularWeight hm U c =
      cfc (modularWeightSquareFunction (2 * c))
        (normalizedCommutation (complexSourceCommutation hm U)) := by
  rw [sourceModularWeight_eq_modularWeightOperator]
  exact modularWeightOperator_adjoint_mul
    (normalizedCommutation_isSelfAdjoint (complexSourceCommutation_mem_skewAdjoint hm U))
    (norm_normalizedCommutation_le_one (norm_complexSourceCommutation_le_two hm U)) hc hc2

end VacuumBellSeparation
