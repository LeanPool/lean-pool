/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

-- Modified for Lean Pool.

module

public import LeanPool.CutoffRigidity.RiemannianSplitting.C1CoordinateJointFlow
public import LeanPool.CutoffRigidity.RiemannianSplitting.DifferentiableCoordinateLocalFlow

/-! # Actual joint `C¹` Picard flow from the original vector field -/

@[expose] public section
open Set Filter Metric Function
open scoped Topology NNReal

namespace CutoffRigidity
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
  [CompleteSpace E] [FiniteDimensional ℝ E]

/-- Every actual `C¹` vector field has an actual jointly `C¹` local Picard flow.
Only source-field regularity is assumed: all solution, variation, coefficient,
and parameter-dependence obligations are proved. -/
theorem exists_jointContDiff_lipschitz_coordinate_localFlow
    {F : E → E} (hF : ContDiff ℝ 1 F) (x₀ : E) :
    ∃ r > (0 : ℝ), ∃ θ > (0 : ℝ), ∃ α : E → ℝ → E, ∃ L' : ℝ≥0,
      ContDiffOn ℝ 1 (uncurry α) (ball x₀ r ×ˢ Ioo (-θ) θ) ∧
      (∀ x ∈ ball x₀ r, α x 0 = x ∧
        ∀ t ∈ Ioo (-θ) θ, HasDerivAt (α x) (F (α x t)) t) ∧
      ∀ t ∈ Ioo (-θ) θ, LipschitzOnWith L' (fun y ↦ α y t) (ball x₀ r) := by
  obtain ⟨ε, hε, a, r, L, K, hr, hpl⟩ := IsPicardLindelof.of_contDiffAt_one
    (hF.contDiffAt (x := x₀))
  obtain ⟨α, hα, L', hLip⟩ :=
    (hpl 0).exists_forall_mem_closedBall_eq_hasDerivWithinAt_lipschitzOnWith
  let D := closedBall x₀ (r : ℝ) ×ˢ Icc (0 - ε) (0 + ε)
  have hcont : ContinuousOn (uncurry α) D := by
    apply continuousOn_prod_of_continuousOn_lipschitzOnWith _ L' _ hLip
    exact fun x hx ↦ HasDerivWithinAt.continuousOn (hα x hx).2
  have hDfcont : ContinuousOn (fun p : E × ℝ ↦ fderiv ℝ F (α p.1 p.2)) D :=
    (hF.continuous_fderiv one_ne_zero).comp_continuousOn hcont
  have hDcompact : IsCompact D := (isCompact_closedBall x₀ (r : ℝ)).prod isCompact_Icc
  obtain ⟨M₀, hM₀⟩ := hDcompact.exists_bound_of_continuousOn hDfcont
  let M : ℝ≥0 := ⟨max M₀ 0, le_max_right _ _⟩
  let T := min (ε / 2) (1 / (4 * ((M : ℝ) + 1)))
  have hden : 0 < 4 * ((M : ℝ) + 1) := by positivity
  have hT : 0 < T := lt_min (half_pos hε) (div_pos zero_lt_one hden)
  have hTε : T < ε := (min_le_left _ _).trans_lt (half_lt_self hε)
  have hshort : 2 * (M : ℝ) * T ≤ 1 := by
    have hb := (le_div_iff₀ hden).mp
      (min_le_right (ε / 2) (1 / (4 * ((M : ℝ) + 1))))
    nlinarith [mul_nonneg M.coe_nonneg hT.le]
  have htime {t : ℝ} (ht : t ∈ Icc (-T) T) : t ∈ Ioo (0 - ε) (0 + ε) := by
    constructor <;> linarith [ht.1, ht.2]
  have hinside {x : E} (hx : x ∈ ball x₀ ((r : ℝ) / 2)) : x ∈ closedBall x₀ (r : ℝ) := by
    apply mem_closedBall.mpr
    exact (mem_ball.mp hx).le.trans (half_le_self r.coe_nonneg)
  have hsolution {x : E} (hx : x ∈ closedBall x₀ (r : ℝ)) {t : ℝ}
      (ht : t ∈ Icc (-T) T) : HasDerivAt (α x) (F (α x t)) t :=
    ((hα x hx).2 t (Ioo_subset_Icc_self (htime ht))).hasDerivAt
      (Icc_mem_nhds (htime ht).1 (htime ht).2)
  refine ⟨(r : ℝ) / 2, half_pos hr, T / 2, half_pos hT, α, L', ?_, ?_, ?_⟩
  · have hfull : ContDiffOn ℝ 1 (uncurry α)
        (ball x₀ (r : ℝ) ×ˢ Ioo (-(T / 2)) (T / 2)) := by
      apply contDiffOn_coordinateFlow_joint_short_of_bound hF x₀ hr hT
        (fun y hy ↦ (hα y hy).1)
        (fun y hy s hs ↦ hsolution hy hs)
        (fun s hs ↦ hLip s (Ioo_subset_Icc_self (htime hs)))
        (hcont.mono (Set.prod_mono Subset.rfl (fun s hs ↦ Ioo_subset_Icc_self (htime hs))))
        (M := M) ?_ hshort
      intro y hy s hs
      exact (hM₀ (y, s) ⟨hy, Ioo_subset_Icc_self (htime hs)⟩).trans (le_max_left _ _)
    exact hfull.mono (Set.prod_mono (ball_subset_ball (half_le_self r.coe_nonneg)) Subset.rfl)
  · intro x hx
    refine ⟨(hα x (hinside hx)).1, ?_⟩
    intro t ht
    exact hsolution (hinside hx) ⟨by linarith [ht.1], by linarith [ht.2]⟩
  · intro t ht
    exact (hLip t (Ioo_subset_Icc_self (htime
      ⟨by linarith [ht.1], by linarith [ht.2]⟩))).mono (fun y hy ↦ hinside hy)

end CutoffRigidity
