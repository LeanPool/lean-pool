/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import Mathlib.Analysis.ODE.ExistUnique
public import Mathlib.Tactic.Linarith
public import Mathlib.Tactic.Ring

/-! # Actual short-time linear variational equations
Continuous operator coefficients with a genuine norm bound yield an actual
solution of `J'=A(t)∘J`, initialized at the identity. No positivity, invertibility,
or supplied variational solution is required.
-/

@[expose] public section
open Set Metric
open scoped NNReal Topology

namespace CutoffRigidity

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]

/-- A continuous operator coefficient admits a true variational solution on a
sufficiently short two-sided interval, by actual Picard existence on a ball. -/
theorem exists_linear_variation_short_interval
    {A : ℝ → E →L[ℝ] E} {T : ℝ} (hT : 0 ≤ T)
    (hA : ContinuousOn A (Icc (-T) T)) {M : ℝ≥0}
    (hbound : ∀ t ∈ Icc (-T) T, ‖A t‖ ≤ M)
    (hshort : 2 * (M : ℝ) * T ≤ 1) :
    ∃ J : ℝ → E →L[ℝ] E, J 0 = ContinuousLinearMap.id ℝ E ∧
      ContinuousOn J (Icc (-T) T) ∧
      ∀ t ∈ Icc (-T) T,
        HasDerivWithinAt J ((A t).comp (J t)) (Icc (-T) T) t := by
  have hPicard : IsPicardLindelof (fun t J ↦ (A t).comp J)
      (tmin := -T) (tmax := T) ⟨0, ⟨by linarith, hT⟩⟩
      (ContinuousLinearMap.id ℝ E) 1 0 (2 * M) M := by
    constructor
    · intro t ht
      apply LipschitzOnWith.of_dist_le_mul
      intro J _ K _
      rw [dist_eq_norm, dist_eq_norm, ← ContinuousLinearMap.comp_sub]
      exact (ContinuousLinearMap.opNorm_comp_le _ _).trans
        (mul_le_mul_of_nonneg_right (hbound t ht) (norm_nonneg _))
    · intro J _
      exact hA.clm_comp continuousOn_const
    · intro t ht J hJ
      have hJdist : ‖J - ContinuousLinearMap.id ℝ E‖ ≤ 1 := by
        simpa only [mem_closedBall, dist_eq_norm, NNReal.coe_one] using hJ
      have hJn : ‖J‖ ≤ 2 := by
        have hh := norm_le_norm_sub_add J (ContinuousLinearMap.id ℝ E)
        have hid := ContinuousLinearMap.norm_id_le (𝕜 := ℝ) (E := E)
        linarith
      calc
        ‖(A t).comp J‖ ≤ ‖A t‖ * ‖J‖ := ContinuousLinearMap.opNorm_comp_le _ _
        _ ≤ (M : ℝ) * 2 := mul_le_mul (hbound t ht) hJn (norm_nonneg _) M.coe_nonneg
        _ = ↑(2 * M) := by simp; ring
    · simpa only [sub_zero, zero_sub, neg_neg, max_self, NNReal.coe_mul,
        NNReal.coe_ofNat, NNReal.coe_one, NNReal.coe_zero] using hshort
  obtain ⟨J, hJzero, hJ⟩ := hPicard.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨J, hJzero, fun t ht ↦ (hJ t ht).continuousWithinAt, hJ⟩

end CutoffRigidity
