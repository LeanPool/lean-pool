/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.PositiveContractionPowers
public import LeanPool.VacuumBellSeparation.FreeField.BoundedRatioTotal

/-!
# Agreement of the resolvent power construction with bounded CFC

When the intrinsic positive resolvent has a bounded inverse, its associated
operator T=(1-R)R⁻¹ is bounded and positive. The constructed full-domain
partial power agrees exactly with the ordinary bounded continuous functional
calculus T^c. The proof uses scalar identities on the actual spectrum and
retains c=0 and possible kernel of T.
-/

@[expose] public section

namespace VacuumBellSeparation

open ContinuousLinearMap

variable {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

/-- Bounded functional calculus compatibility, including equality of domains. -/
theorem resolventPowerRatio_eq_bounded_power (R : E →L[ℂ] E)
    (hR : IsStrictlyPositive R) (hR1 : R ≤ 1) (hi : Function.Injective R)
    (c : ℝ) (hc : 0 ≤ c) (hc1 : c ≤ 1) :
    resolventPowerRatio R hR.nonneg hi c hc hc1 =
      (((1 - R) * Ring.inverse R) ^ c).toPMap ⊤ := by
  let f : ℝ → ℝ := fun x => (1 - x) / x
  have hs (x : ℝ) (hx : x ∈ spectrum ℝ R) : 0 < x ∧ x ≤ 1 := by
    refine ⟨hR.spectrum_pos hx, ?_⟩
    exact (Real.le_norm_self x).trans
      ((IsometricContinuousFunctionalCalculus.norm_spectrum_le R hx hR.nonneg.isSelfAdjoint).trans
        ((CStarAlgebra.norm_le_one_iff_of_nonneg R hR.nonneg).mpr hR1))
  have hf : ContinuousOn f (spectrum ℝ R) :=
    (continuous_const.sub continuous_id).continuousOn.div continuous_id.continuousOn
      (fun x hx => (hs x hx).1.ne')
  have hsub : cfc (fun x : ℝ => 1 - x) R = 1 - R := by
    rw [cfc_sub (fun _ : ℝ => 1) (fun x : ℝ => x) R
      continuous_const.continuousOn continuous_id.continuousOn,
      cfc_const_one ℝ R hR.nonneg.isSelfAdjoint, cfc_id' ℝ R hR.nonneg.isSelfAdjoint]
  have hT : cfc f R = (1 - R) * Ring.inverse R := by
    rw [show f = fun x : ℝ => (1 - x) / x from rfl,
      cfc_map_div (fun x : ℝ => 1 - x) (fun x : ℝ => x) R
        (fun x hx => (hs x hx).1.ne')
        (continuous_const.sub continuous_id).continuousOn continuous_id.continuousOn
        hR.nonneg.isSelfAdjoint, hsub, cfc_id' ℝ R hR.nonneg.isSelfAdjoint]
  have hT0 : 0 ≤ cfc f R := by
    apply (cfc_nonneg_iff f R hf hR.nonneg.isSelfAdjoint).mpr
    intro x hx
    exact div_nonneg (sub_nonneg.mpr (hs x hx).2) (hs x hx).1.le
  have hp : Continuous (fun x : ℝ => x ^ c) := Real.continuous_rpow_const hc
  have hTc : ((1 - R) * Ring.inverse R) ^ c = cfc (fun x : ℝ => f x ^ c) R := by
    rw [← hT, CFC.rpow_eq_cfc_real hT0,
      ← cfc_comp' (fun x : ℝ => x ^ c) f R hp.continuousOn hf hR.nonneg.isSelfAdjoint]
  have hBc : (1 - R) ^ c = cfc (fun x : ℝ => (1 - x) ^ c) R := by
    rw [CFC.rpow_eq_cfc_real (sub_nonneg.mpr hR1), ← hsub,
      ← cfc_comp' (fun x : ℝ => x ^ c) (fun x : ℝ => 1 - x) R hp.continuousOn
        (continuous_const.sub continuous_id).continuousOn hR.nonneg.isSelfAdjoint]
  apply boundedRatio_eq_toPMap_of_factorization (R ^ c) ((1 - R) ^ c)
    (((1 - R) * Ring.inverse R) ^ c) _ (IsStrictlyPositive.rpow R c hR).isUnit
  rw [hTc, CFC.rpow_eq_cfc_real hR.nonneg, hBc,
    ← cfc_mul (fun x : ℝ => f x ^ c) (fun x : ℝ => x ^ c) R
      (hp.comp_continuousOn' hf) hp.continuousOn]
  apply cfc_congr
  intro x hx
  dsimp [f]
  rw [Real.div_rpow (sub_nonneg.mpr (hs x hx).2) (hs x hx).1.le c,
    div_mul_cancel₀ _ (Real.rpow_pos_of_pos (hs x hx).1 c).ne']

end VacuumBellSeparation
