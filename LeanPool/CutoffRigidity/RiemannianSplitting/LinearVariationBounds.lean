/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.ODE.Gronwall
public import Mathlib.Analysis.Normed.Operator.CompleteCodomain
public import Mathlib.Tactic.Abel
public import Mathlib.Tactic.Ring

/-! # Genuine linear-variation norm and coefficient-dependence estimates
Both estimates are derived from the actual operator-valued ODE by Grönwall.
-/

@[expose] public section
open Set
open scoped Topology NNReal

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

/-- The norm of an actual identity-initialized linear variation grows at most
exponentially with the actual coefficient norm bound. -/
theorem norm_linearVariation_le_exp
    {A J : ℝ → E →L[ℝ] E} {T : ℝ} (hT : 0 ≤ T)
    (hJzero : J 0 = ContinuousLinearMap.id ℝ E)
    (hJD : ∀ t ∈ Icc 0 T, HasDerivAt J ((A t).comp (J t)) t)
    {M : ℝ≥0} (hM : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ M) :
    ‖J T‖ ≤ Real.exp ((M : ℝ) * T) := by
  have hJC : ContinuousOn J (Icc 0 T) :=
    fun t ht ↦ (hJD t ht).continuousAt.continuousWithinAt
  have hb (t : ℝ) (ht : t ∈ Ico 0 T) :
      ‖(A t).comp (J t)‖ ≤ (M : ℝ) * ‖J t‖ + 0 := by
    rw [add_zero]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
      (mul_le_mul_of_nonneg_right (hM t (Ico_subset_Icc_self ht)) (norm_nonneg _))
  have hinit : ‖J 0‖ ≤ 1 := by rw [hJzero]; exact ContinuousLinearMap.norm_id_le
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hJC
    (fun t ht ↦ (hJD t (Ico_subset_Icc_self ht)).hasDerivWithinAt)
    hinit hb T ⟨hT, le_rfl⟩
  simpa only [sub_zero, gronwallBound_ε0, one_mul] using h

/-- Actual variations depend quantitatively on their actual coefficient
functions. No differentiability or continuity of a solution map is assumed. -/
theorem norm_sub_linearVariation_le
    {A B J K : ℝ → E →L[ℝ] E} {T : ℝ} (hT : 0 ≤ T)
    (hJzero : J 0 = ContinuousLinearMap.id ℝ E)
    (hKzero : K 0 = ContinuousLinearMap.id ℝ E)
    (hJD : ∀ t ∈ Icc 0 T, HasDerivAt J ((A t).comp (J t)) t)
    (hKD : ∀ t ∈ Icc 0 T, HasDerivAt K ((B t).comp (K t)) t)
    {M : ℝ≥0} (hM : ∀ t ∈ Icc 0 T, ‖A t‖ ≤ M)
    {η N : ℝ} (hη : 0 ≤ η)
    (hdiff : ∀ t ∈ Icc 0 T, ‖A t - B t‖ ≤ η)
    (hK : ∀ t ∈ Icc 0 T, ‖K t‖ ≤ N) :
    ‖J T - K T‖ ≤ η * N * gronwallBound 0 (M : ℝ) 1 T := by
  let Z := fun t ↦ J t - K t
  have hZD (t : ℝ) (ht : t ∈ Icc 0 T) :
      HasDerivAt Z ((A t).comp (J t) - (B t).comp (K t)) t :=
    (hJD t ht).sub (hKD t ht)
  have hZC : ContinuousOn Z (Icc 0 T) :=
    fun t ht ↦ (hZD t ht).continuousAt.continuousWithinAt
  have hb (t : ℝ) (ht : t ∈ Ico 0 T) :
      ‖(A t).comp (J t) - (B t).comp (K t)‖ ≤ (M : ℝ) * ‖Z t‖ + η * N := by
    have heq : (A t).comp (J t) - (B t).comp (K t) =
        (A t).comp (J t - K t) + (A t - B t).comp (K t) := by
      rw [ContinuousLinearMap.comp_sub, ContinuousLinearMap.sub_comp]
      abel
    rw [heq]
    apply (norm_add_le _ _).trans
    apply add_le_add
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hM t (Ico_subset_Icc_self ht)) (norm_nonneg _))
    · exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul (hdiff t (Ico_subset_Icc_self ht)) (hK t (Ico_subset_Icc_self ht))
          (norm_nonneg _) hη)
  have hz : ‖Z 0‖ ≤ 0 := by simp [Z, hJzero, hKzero]
  have h := norm_le_gronwallBound_of_norm_deriv_right_le hZC
    (fun t ht ↦ (hZD t (Ico_subset_Icc_self ht)).hasDerivWithinAt) hz hb T ⟨hT, le_rfl⟩
  have hscale : gronwallBound 0 (M : ℝ) (η * N) T =
      η * N * gronwallBound 0 (M : ℝ) 1 T := by
    unfold gronwallBound
    split_ifs <;> ring
  simpa only [sub_zero, hscale] using h

end CutoffRigidity
