/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PositiveSandwichDifference

/-!
# Nuclear continuity of genuine selfadjoint trace-class sandwiches

The positive difference modulus extends through the actual Jordan parts.
The resulting estimate proves continuity of the real nuclear trace under
operator-norm convergence of selfadjoint sandwich factors. Neither finite
rank nor a nuclear-norm completeness theorem is assumed.
-/

@[expose] public section

noncomputable section

namespace VacuumBellSeparation.Gaussian

open ContinuousLinearMap Filter
open scoped ENNReal Topology

variable {ι E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℂ E] [CompleteSpace E]

theorem operatorTraceNorm_sandwich_difference_modulus {B S T : E →L[ℂ] E}
    (hB : IsSelfAdjoint B) (htB : operatorTraceNorm B < ∞)
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) :
    operatorTraceNorm (S * B * S - T * B * T) ≤
      ENNReal.ofReal (‖S - T‖ * (‖S - T‖ + 1 + ‖T‖ ^ 2)) * operatorTraceNorm B := by
  obtain ⟨hp, hn⟩ := selfAdjoint_parts_traceClass hB htB
  let Dp : E →L[ℂ] E := S * B⁺ * S - T * B⁺ * T
  let Dn : E →L[ℂ] E := S * B⁻ * S - T * B⁻ * T
  have hcp := positiveTraceClass_isCompactOperator hp
  have hcn := positiveTraceClass_isCompactOperator hn
  have hcDp : IsCompactOperator Dp :=
    ((hcp.clm_comp S).comp_clm S).sub ((hcp.clm_comp T).comp_clm T)
  have hcDn : IsCompactOperator Dn :=
    ((hcn.clm_comp S).comp_clm S).sub ((hcn.clm_comp T).comp_clm T)
  have hsDp : IsSelfAdjoint Dp :=
    (selfAdjoint_sandwich_isSelfAdjoint hp.1.isSelfAdjoint hS).sub
      (selfAdjoint_sandwich_isSelfAdjoint hp.1.isSelfAdjoint hT)
  have hsDn : IsSelfAdjoint Dn :=
    (selfAdjoint_sandwich_isSelfAdjoint hn.1.isSelfAdjoint hS).sub
      (selfAdjoint_sandwich_isSelfAdjoint hn.1.isSelfAdjoint hT)
  have he : S * B * S - T * B * T = Dp - Dn := by
    calc
      _ = S * (B⁺ - B⁻) * S -
          T * (B⁺ - B⁻) * T := by
        rw [CFC.posPart_sub_negPart B hB]
      _ = Dp - Dn := by dsimp only [Dp, Dn]; noncomm_ring
  rw [he]
  apply (operatorTraceNorm_sub_le hcDp hcDn hsDp hsDn).trans
  apply (add_le_add (operatorTraceNorm_positive_sandwich_difference_modulus hp hS hT)
    (operatorTraceNorm_positive_sandwich_difference_modulus hn hS hT)).trans_eq
  rw [← mul_add, ← positiveTrace_add hp.1 hn.1, CFC.posPart_add_negPart B hB]
  rfl

theorem operatorTraceNorm_reverse_triangle_toReal {A B : E →L[ℂ] E}
    (hcA : IsCompactOperator A) (hcB : IsCompactOperator B)
    (hA : IsSelfAdjoint A) (hB : IsSelfAdjoint B)
    (htA : operatorTraceNorm A < ∞) (htB : operatorTraceNorm B < ∞) :
    |(operatorTraceNorm A).toReal - (operatorTraceNorm B).toReal| ≤
      (operatorTraceNorm (A - B)).toReal := by
  have htD : operatorTraceNorm (A - B) < ∞ :=
    (operatorTraceNorm_sub_le hcA hcB hA hB).trans_lt (ENNReal.add_lt_top.mpr ⟨htA, htB⟩)
  have hleft : operatorTraceNorm A ≤ operatorTraceNorm (A - B) + operatorTraceNorm B := by
    simpa only [sub_add_cancel] using operatorTraceNorm_add_le (hcA.sub hcB) hcB (hA.sub hB) hB
  have hright : operatorTraceNorm B ≤ operatorTraceNorm (A - B) + operatorTraceNorm A := by
    have h := operatorTraceNorm_add_le (hcB.sub hcA) hcA (hB.sub hA) hA
    rw [sub_add_cancel, show B - A = -(A - B) by abel, operatorTraceNorm_neg] at h
    exact h
  have hl := ENNReal.toReal_mono (ENNReal.add_lt_top.mpr ⟨htD, htB⟩).ne hleft
  have hr := ENNReal.toReal_mono (ENNReal.add_lt_top.mpr ⟨htD, htA⟩).ne hright
  rw [ENNReal.toReal_add htD.ne htB.ne] at hl
  rw [ENNReal.toReal_add htD.ne htA.ne] at hr
  exact abs_le.mpr ⟨by linarith, by linarith⟩

theorem nuclear_sandwich_toReal_modulus {B S T : E →L[ℂ] E}
    (hcB : IsCompactOperator B) (hB : IsSelfAdjoint B) (htB : operatorTraceNorm B < ∞)
    (hS : IsSelfAdjoint S) (hT : IsSelfAdjoint T) :
    |(operatorTraceNorm (S * B * S)).toReal - (operatorTraceNorm (T * B * T)).toReal| ≤
      (‖S - T‖ * (‖S - T‖ + 1 + ‖T‖ ^ 2)) * (operatorTraceNorm B).toReal := by
  have hr := operatorTraceNorm_reverse_triangle_toReal
    ((hcB.clm_comp S).comp_clm S) ((hcB.clm_comp T).comp_clm T)
    (selfAdjoint_sandwich_isSelfAdjoint hB hS) (selfAdjoint_sandwich_isSelfAdjoint hB hT)
    (operatorTraceNorm_selfAdjoint_sandwich_lt_top hcB hB htB hS)
    (operatorTraceNorm_selfAdjoint_sandwich_lt_top hcB hB htB hT)
  have hc : 0 ≤ ‖S - T‖ * (‖S - T‖ + 1 + ‖T‖ ^ 2) := by positivity
  have he := operatorTraceNorm_sandwich_difference_modulus hB htB hS hT
  have hf : ENNReal.ofReal (‖S - T‖ * (‖S - T‖ + 1 + ‖T‖ ^ 2)) *
      operatorTraceNorm B ≠ ∞ := (ENNReal.mul_lt_top ENNReal.ofReal_lt_top htB).ne
  have hreal := ENNReal.toReal_mono hf he
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hc] at hreal
  exact hr.trans hreal

theorem tendsto_nuclear_sandwich_toReal {l : Filter ι} {S : ι → E →L[ℂ] E}
    {T B : E →L[ℂ] E} (hS : ∀ i, IsSelfAdjoint (S i)) (hT : IsSelfAdjoint T)
    (hcB : IsCompactOperator B) (hB : IsSelfAdjoint B) (htB : operatorTraceNorm B < ∞)
    (hST : Tendsto S l (𝓝 T)) :
    Tendsto (fun i => (operatorTraceNorm (S i * B * S i)).toReal) l
      (𝓝 (operatorTraceNorm (T * B * T)).toReal) := by
  have hd : Tendsto (fun i => ‖S i - T‖) l (𝓝 (0 : ℝ)) := by
    simpa only [sub_self, norm_zero] using (hST.sub (tendsto_const_nhds (x := T))).norm
  have hlim : Tendsto (fun i =>
      (‖S i - T‖ * (‖S i - T‖ + 1 + ‖T‖ ^ 2)) * (operatorTraceNorm B).toReal)
      l (𝓝 (0 : ℝ)) := by
    simpa only [zero_mul] using
      (hd.mul ((hd.add (tendsto_const_nhds (x := (1 : ℝ)))).add
        (tendsto_const_nhds (x := ‖T‖ ^ 2)))).mul
          (tendsto_const_nhds (x := (operatorTraceNorm B).toReal))
  apply tendsto_iff_norm_sub_tendsto_zero.mpr
  apply squeeze_zero (fun _ => norm_nonneg _) _ hlim
  intro i
  rw [Real.norm_eq_abs]
  exact nuclear_sandwich_toReal_modulus hcB hB htB (hS i) hT

end VacuumBellSeparation.Gaussian
