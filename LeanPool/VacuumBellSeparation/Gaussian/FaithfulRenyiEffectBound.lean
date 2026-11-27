/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.RenyiEffectBound

/-!
# The extended arbitrary-effect Rényi bound, including infinity

Faithfulness forces every positive effect with zero reference expectation
to vanish. This handles the zero-times-infinity endpoint and removes the
finite-quantity premise from the genuine effect inequality.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap
open scoped ENNReal ContinuousFunctionalCalculus

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

@[simp] theorem positiveEffectExpectation_zero (ρ : E →L[ℂ] E) :
    positiveEffectExpectation ρ 0 = 0 := by
  simp [positiveEffectExpectation, positiveTrace_zero]

theorem positiveEffectExpectation_eq_zero_iff {σ M : E →L[ℂ] E}
    (hσ : 0 ≤ σ) (hinj : Function.Injective σ) (hM : 0 ≤ M) :
    positiveEffectExpectation σ M = 0 ↔ M = 0 := by
  constructor
  · intro hz
    have hGram : CFC.sqrt M * σ * CFC.sqrt M = 0 :=
      (positiveTrace_eq_zero_iff (conjugate_nonneg_of_nonneg hσ (CFC.sqrt_nonneg M))).mp hz
    let T := CFC.sqrt σ * CFC.sqrt M
    have hTGram : T.adjoint.comp T = 0 := by
      change star (CFC.sqrt σ * CFC.sqrt M) * (CFC.sqrt σ * CFC.sqrt M) = 0
      rw [star_mul, (CFC.sqrt_nonneg σ).isSelfAdjoint.star_eq,
        (CFC.sqrt_nonneg M).isSelfAdjoint.star_eq]
      calc
        _ = CFC.sqrt M * (CFC.sqrt σ * CFC.sqrt σ) * CFC.sqrt M := by noncomm_ring
        _ = 0 := by rw [← pow_two, CFC.sq_sqrt σ hσ, hGram]
    have hT : T = 0 := adjoint_comp_self_eq_zero_iff.mp hTGram
    have hi : Function.Injective (CFC.sqrt σ : E →L[ℂ] E) := by
      rw [CFC.sqrt_eq_rpow]
      exact positive_rpow_injective hσ hinj (by norm_num)
    have hs : CFC.sqrt M = 0 := by
      ext x
      apply hi
      have hx := DFunLike.congr_fun hT x
      simpa only [T, mul_apply_eq_comp, zero_apply, map_zero] using hx
    calc
      M = CFC.sqrt M * CFC.sqrt M := by rw [← pow_two, CFC.sq_sqrt M hM]
      _ = 0 := by rw [hs, zero_mul]
  · rintro rfl
    exact positiveEffectExpectation_zero σ

theorem faithful_sandwichedRenyi_effect_bound {ρ σ M : E →L[ℂ] E}
    (hσ : IsFaithfulDensity σ) {r : ℝ} (hr : 1 < r) (hM₀ : 0 ≤ M) (hM₁ : M ≤ 1) :
    positiveEffectExpectation ρ M ^ r ≤
      sandwichedRenyiQuantity ρ σ r * positiveEffectExpectation σ M ^ (r - 1) := by
  by_cases hM : M = 0
  · subst M
    simp only [positiveEffectExpectation_zero,
      ENNReal.zero_rpow_of_pos (lt_trans zero_lt_one hr),
      ENNReal.zero_rpow_of_pos (sub_pos.mpr hr), mul_zero, le_refl]
  · have he : positiveEffectExpectation σ M ≠ 0 :=
      mt (positiveEffectExpectation_eq_zero_iff hσ.1 hσ.2.2 hM₀).mp hM
    by_cases hQ : sandwichedRenyiQuantity ρ σ r = ∞
    · rw [hQ, ENNReal.top_mul
        (ENNReal.rpow_pos_of_nonneg (pos_iff_ne_zero.mpr he) (sub_pos.mpr hr).le).ne']
      exact le_top
    · exact finite_sandwichedRenyi_effect_bound hσ hr (lt_top_iff_ne_top.mpr hQ) hM₀ hM₁

theorem faithful_sandwichedRenyi_density_effect_bound (b : HilbertBasis ι ℂ E)
    {ρ σ M : E →L[ℂ] E} (hρ : IsPositiveTraceClass ρ) (hσ : IsFaithfulDensity σ)
    {r : ℝ} (hr : 1 < r) (hM₀ : 0 ≤ M) (hM₁ : M ≤ 1) :
    ENNReal.ofReal (densityExpectation b ρ M).re ^ r ≤
      sandwichedRenyiQuantity ρ σ r * ENNReal.ofReal (densityExpectation b σ M).re ^ (r - 1) := by
  have hσtc : IsPositiveTraceClass σ :=
    ⟨hσ.1, by rw [hσ.2.1]; exact ENNReal.one_lt_top⟩
  simpa only [positiveEffectExpectation_eq_densityExpectation b hρ hM₀,
    positiveEffectExpectation_eq_densityExpectation b hσtc hM₀] using
    faithful_sandwichedRenyi_effect_bound (ρ := ρ) hσ hr hM₀ hM₁

end VacuumBellSeparation.Gaussian
