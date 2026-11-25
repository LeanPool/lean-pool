/-
Copyright (c) 2026 Mingchen Xia, Jian Wang, and Siqi He. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mingchen Xia, Jian Wang, Siqi He
-/

-- Modified for Lean Pool.

module

public import LeanPool.NonpluripolarProducts.Foundations.Analysis.PshSmoothApproximation

/-!
# Buffered neighborhoods for distribution regularization

Around a point of an open subset of a finite-dimensional normed space, we
choose an inner open set whose closure has a uniform closed-ball buffer inside
one compact subset of the original domain.  This is the geometric support
bookkeeping needed by translated smoothing kernels.
-/

@[expose] public section

noncomputable section

open Set Metric TopologicalSpace

namespace SGPT.Foundations.Analysis.Pending

/-- A point in an open finite-dimensional real vector space has an inner open
neighborhood whose closure admits one positive-radius compact buffer inside
the original domain. -/
theorem exists_open_closure_closedBall_neighborhood
    {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] {Ω : Opens E} {x : E} (hx : x ∈ Ω) :
    ∃ R > 0, ∃ U : Opens E, ∃ K : Compacts E,
      x ∈ U ∧ U ≤ Ω ∧ (K : Set E) ⊆ Ω ∧
        ∀ z ∈ closure (U : Set E), closedBall z R ⊆ K := by
  let _ : ProperSpace E := FiniteDimensional.proper ℝ E
  obtain ⟨R, hR, V, K, hVo, hxV, hVK, hKc, hKΩ, hball⟩ :=
    exists_open_compact_closedBall_neighborhood
      (S := ({x} : Set E)) isCompact_singleton Ω.isOpen (by simpa using hx)
  obtain ⟨U, hUo, hxU, hUV⟩ :=
    normal_exists_closure_subset isClosed_singleton hVo hxV
  let Uo : Opens E := ⟨U, hUo⟩
  let Kc : Compacts E := ⟨K, hKc⟩
  refine ⟨R, hR, Uo, Kc, ?_, ?_, hKΩ, ?_⟩
  · exact hxU (mem_singleton x)
  · exact subset_closure.trans (hUV.trans (hVK.trans hKΩ))
  · intro z hz
    exact hball z (hUV hz)

/-- The preceding buffer may be measured through any chosen continuous linear
coordinates.  The coordinate radius is shrunk by a uniform operator-norm
bound for the inverse equivalence. -/
theorem exists_open_closure_coordinateBall_neighborhood
    {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [FiniteDimensional ℝ E] [NormedAddCommGroup F] [NormedSpace ℝ F]
    (A : E ≃L[ℝ] F) {Ω : Opens E} {x : E} (hx : x ∈ Ω) :
    ∃ R > 0, ∃ U : Opens E, ∃ K : Compacts E,
      x ∈ U ∧ U ≤ Ω ∧ (K : Set E) ⊆ Ω ∧
        ∀ z ∈ closure (U : Set E), ∀ y : E,
          ‖A (y - z)‖ ≤ R → y ∈ K := by
  obtain ⟨r, hr, U, K, hxU, hUΩ, hKΩ, hball⟩ :=
    exists_open_closure_closedBall_neighborhood hx
  let M : ℝ := max ‖A.symm.toContinuousLinearMap‖ 1
  have hM : 0 < M := lt_of_lt_of_le zero_lt_one (le_max_right _ _)
  let R : ℝ := r / M
  have hR : 0 < R := div_pos hr hM
  refine ⟨R, hR, U, K, hxU, hUΩ, hKΩ, ?_⟩
  intro z hz y hy
  apply hball z hz
  rw [mem_closedBall, dist_eq_norm]
  calc
    ‖y - z‖ = ‖A.symm (A (y - z))‖ := by rw [A.symm_apply_apply]
    _ ≤ ‖A.symm.toContinuousLinearMap‖ * ‖A (y - z)‖ :=
      A.symm.toContinuousLinearMap.le_opNorm _
    _ ≤ M * R := mul_le_mul (le_max_left _ _) hy (norm_nonneg _) hM.le
    _ = r := by
      dsimp [R]
      exact mul_div_cancel₀ r hM.ne'

end SGPT.Foundations.Analysis.Pending
