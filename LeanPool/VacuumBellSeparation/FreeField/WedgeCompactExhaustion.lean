/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.FreeField.WedgeGeometry
public import Mathlib.Topology.Order.Compact
public import Mathlib.Analysis.Normed.Group.Bounded

/-!
# Compact exhaustion of the literal left wedge by double cones

A cone tangent to the wedge edge, with its center sufficiently far along
the negative first spatial axis, contains any prescribed compact subset of
the wedge. This also supplies a single contained ball for any compact
subset of the time-zero halfspace, without a transverse size restriction.
-/

@[expose] public section

namespace VacuumBellSeparation

open scoped InnerProductSpace

theorem tangent_doubleCone_subset_leftWedge (ℓ L : ℝ) :
    doubleCone (0, (ℓ - L) • e₁) L ⊆ leftWedge ℓ := by
  intro x hx
  have hi := (le_abs_self _).trans (abs_inner_e₁_le (x.2 - (ℓ - L) • e₁))
  rw [inner_sub_right, real_inner_smul_right, inner_e₁_self, mul_one] at hi
  change |x.1 - 0| + ‖x.2 - (ℓ - L) • e₁‖ < L at hx
  rw [sub_zero] at hx
  change ⟪e₁, x.2⟫_ℝ + |x.1| < ℓ
  linarith

theorem tangent_ball_subset_leftWedgeTimeZero (ℓ L : ℝ) :
    Metric.ball ((ℓ - L) • e₁) L ⊆ leftWedgeTimeZero ℓ := by
  intro x hx
  apply (mem_leftWedge_zero_time ℓ x).mp
  apply tangent_doubleCone_subset_leftWedge ℓ L
  simpa only [doubleCone, Set.mem_ofPred_eq, sub_self, abs_zero, zero_add,
    Metric.mem_ball, dist_eq_norm] using hx

theorem mem_tangent_doubleCone_of_margin {ℓ L δ M : ℝ} {x : Spacetime}
    (hL : |x.1| < L) (hlarge : M < 2 * L * δ)
    (hM : ‖x.2 - ℓ • e₁‖ ^ 2 ≤ M)
    (hδ : δ ≤ ℓ - (⟪e₁, x.2⟫_ℝ + |x.1|)) :
    x ∈ doubleCone (0, (ℓ - L) • e₁) L := by
  have hL₀ : 0 < L := (abs_nonneg _).trans_lt hL
  have heq : x.2 - (ℓ - L) • e₁ = (x.2 - ℓ • e₁) + L • e₁ := by
    rw [sub_smul]
    module
  have hsquare : ‖x.2 - (ℓ - L) • e₁‖ ^ 2 =
      ‖x.2 - ℓ • e₁‖ ^ 2 + 2 * L * (⟪e₁, x.2⟫_ℝ - ℓ) + L ^ 2 := by
    rw [heq, norm_add_sq_real, real_inner_smul_right,
      inner_sub_left, real_inner_smul_left, inner_e₁_self, mul_one,
      norm_smul, Real.norm_eq_abs, abs_of_pos hL₀, norm_e₁, mul_one]
    rw [real_inner_comm x.2 e₁]
    ring
  have hmul := mul_le_mul_of_nonneg_left hδ (show 0 ≤ 2 * L by positivity)
  have hsq : ‖x.2 - (ℓ - L) • e₁‖ ^ 2 < (L - |x.1|) ^ 2 := by
    nlinarith [sq_nonneg |x.1|]
  have hn : ‖x.2 - (ℓ - L) • e₁‖ < L - |x.1| := by
    nlinarith [norm_nonneg (x.2 - (ℓ - L) • e₁)]
  change |x.1 - 0| + ‖x.2 - (ℓ - L) • e₁‖ < L
  rw [sub_zero]
  linarith

/-- Every actual compact subset fits inside one double cone contained in the
same wedge. Empty compact sets are included. -/
theorem IsCompact.exists_tangent_doubleCone {K : Set Spacetime} (hK : IsCompact K)
    {ℓ : ℝ} (hKW : K ⊆ leftWedge ℓ) :
    ∃ L : ℝ, 0 < L ∧ K ⊆ doubleCone (0, (ℓ - L) • e₁) L := by
  have hcδ : Continuous (fun x : Spacetime => ℓ - (⟪e₁, x.2⟫_ℝ + |x.1|)) := by
    fun_prop
  obtain ⟨δ, hδ₀, hδ⟩ := hK.exists_forall_le' hcδ.continuousOn
    (a := (0 : ℝ)) (fun x hx => sub_pos.mpr (hKW hx))
  have hcM : Continuous (fun x : Spacetime => ‖x.2 - ℓ • e₁‖ ^ 2 + |x.1|) := by
    fun_prop
  obtain ⟨M, hM⟩ := hK.exists_bound_of_continuousOn hcM.continuousOn
  obtain ⟨L, hL⟩ := exists_gt (max (M / (2 * δ)) (max M 0))
  have hL₀ : 0 < L := (le_max_right M 0).trans_lt ((le_max_right _ _).trans_lt hL)
  have hML : M < L := (le_max_left M 0).trans_lt ((le_max_right _ _).trans_lt hL)
  have hlarge : M < 2 * L * δ := by
    have hdiv : M / (2 * δ) < L := (le_max_left _ _).trans_lt hL
    have h := (div_lt_iff₀ (show 0 < 2 * δ by positivity)).mp hdiv
    nlinarith
  refine ⟨L, hL₀, ?_⟩
  intro x hx
  have hb : ‖x.2 - ℓ • e₁‖ ^ 2 + |x.1| ≤ M := by
    simpa only [Real.norm_eq_abs, abs_of_nonneg (add_nonneg (sq_nonneg (‖x.2 - ℓ • e₁‖ : ℝ))
      (abs_nonneg x.1))]
      using hM x hx
  exact mem_tangent_doubleCone_of_margin (by nlinarith [sq_nonneg ‖x.2 - ℓ • e₁‖])
    hlarge (by linarith [abs_nonneg x.1]) (hδ x hx)

theorem IsCompact.exists_tangent_ball {K : Set (EuclideanSpace ℝ (Fin 3))}
    (hK : IsCompact K) {ℓ : ℝ} (hKW : K ⊆ leftWedgeTimeZero ℓ) :
    ∃ L : ℝ, 0 < L ∧ K ⊆ Metric.ball ((ℓ - L) • e₁) L := by
  have hc : Continuous (fun x : EuclideanSpace ℝ (Fin 3) => ((0 : ℝ), x)) := by fun_prop
  have hW : (fun x : EuclideanSpace ℝ (Fin 3) => ((0 : ℝ), x)) '' K ⊆ leftWedge ℓ := by
    rintro _ ⟨x, hx, rfl⟩
    exact (mem_leftWedge_zero_time ℓ x).mpr (hKW hx)
  obtain ⟨L, hL, hsub⟩ := IsCompact.exists_tangent_doubleCone (hK.image hc) hW
  refine ⟨L, hL, ?_⟩
  intro x hx
  have h := hsub ⟨x, hx, rfl⟩
  simpa only [doubleCone, Set.mem_ofPred_eq, sub_self, abs_zero, zero_add,
    Metric.mem_ball, dist_eq_norm] using h

end VacuumBellSeparation
