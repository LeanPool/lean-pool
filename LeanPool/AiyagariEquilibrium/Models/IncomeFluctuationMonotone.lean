/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuation
public import LeanPool.AiyagariEquilibrium.Analysis.DecreasingIncrements


/-!
# The optimal policy is increasing in assets

A household that starts richer saves at least as much, holding the income state fixed.

The argument is the classical monotone-comparative-statics one, but it needs neither Topkis
nor any derivative. Two observations do all the work.

First, the continuation value `β E[V(a', z')]` depends on the chosen saving `a'` and on the
*current* income state, but not on current assets. So when comparing two asset levels with
the same income state, the continuation terms cancel, and increasing differences of the
objective reduces to increasing differences of `u` composed with the budget — which is
exactly `ConcaveOn.sub_le_sub_of_shift`, concavity of `u`.

Second, the usual Topkis conclusion (the argmax is an increasing *correspondence*) is not
needed, because uniqueness of the optimal action is already proved. If the richer household
saved strictly less, the exchange argument shows the poorer household's choice is *also*
optimal for the richer one, and uniqueness collapses the two.

The feasible set grows with assets, which is what makes both exchanges legal.
-/

@[expose] public section

open Set Filter Topology

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ}
variable (P : IncomeFluctuation Z assetFloor assetCap)

/-! ### The budget grows with assets -/

theorem resources_mono {a a' : ℝ} {z : Z} (h : a ≤ a') :
    P.resources (a, z) ≤ P.resources (a', z) := by
  have hm : max assetFloor a ≤ max assetFloor a' := max_le_max le_rfl h
  have hi := P.interest_gt_neg_one
  simp only [resources]
  nlinarith

theorem maxSaving_mono {a a' : ℝ} {z : Z} (h : a ≤ a') :
    P.maxSaving (a, z) ≤ P.maxSaving (a', z) :=
  max_le_max le_rfl (min_le_min le_rfl (P.resources_mono h))

theorem feasible_mono {a a' : ℝ} {z : Z} (h : a ≤ a') :
    P.toExtended.feasible (a, z) ⊆ P.toExtended.feasible (a', z) := by
  simp only [P.feasible_eq]
  exact Icc_subset_Icc le_rfl (P.maxSaving_mono h)

/-! ### The objective in the reals -/

/-- The continuation value of saving `x` when the current income state is `z`. It does not
depend on current assets, which is what makes the comparison below work. -/
noncomputable def cont (z : Z) (x : ℝ) : ℝ :=
  ∑ z', P.transitionMatrix z z' * P.toExtended.valueFunction (x, z')

/-- The objective, as a real number. Valid wherever consumption is positive. -/
noncomputable def objR (s : ℝ × Z) (x : ℝ) : ℝ :=
  P.u (P.consumption s x) + P.discount * P.cont s.2 x

theorem objectiveE_eq_coe {s : ℝ × Z} {x : ℝ} (hs : s.1 ∈ Icc assetFloor assetCap)
    (hx : x ∈ P.toExtended.feasible s) (hc : P.consumption s x ∈ P.dom) :
    P.toExtended.objectiveE P.toExtended.valueFunction s x = ((P.objR s x : ℝ) : EReal) := by
  rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_coe_dom hs hx hc, ← EReal.coe_add]
  rfl

/-- Any feasible action with positive consumption is worth at most the optimum. -/
theorem objR_le_of_mem {s : ℝ × Z} {x : ℝ} (hs : s.1 ∈ Icc assetFloor assetCap)
    (hx : x ∈ P.toExtended.feasible s) (hc : P.consumption s x ∈ P.dom) :
    P.objR s x ≤ P.objR s (P.policy s) := by
  have hpol : ((P.objR s (P.policy s) : ℝ) : EReal)
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction s : ℝ) : EReal) := by
    rw [← P.objectiveE_eq_coe hs (P.policy_mem s) (P.consumption_policy_mem_dom hs)]
    exact P.policy_optimal s
  have h1 := P.toExtended.le_bellmanFn P.toExtended.valueFunction hx
  rw [P.objectiveE_eq_coe hs hx hc, ← hpol] at h1
  exact_mod_cast h1

/-! ### Monotonicity -/

/-- **The optimal policy is increasing in assets.** Holding the income state fixed, a
household with more assets saves at least as much. -/
theorem policy_mono {a a' : ℝ} {z : Z} (ha : a ∈ Icc assetFloor assetCap)
    (ha' : a' ∈ Icc assetFloor assetCap) (hle : a ≤ a') :
    P.policy (a, z) ≤ P.policy (a', z) := by
  by_contra hcon
  rw [not_le] at hcon
  have hR : P.resources (a, z) ≤ P.resources (a', z) := P.resources_mono hle
  -- both exchanges are feasible
  have hys : P.policy (a, z) ∈ P.toExtended.feasible (a, z) := P.policy_mem _
  have hys' : P.policy (a, z) ∈ P.toExtended.feasible (a', z) := P.feasible_mono hle hys
  have hy's' : P.policy (a', z) ∈ P.toExtended.feasible (a', z) := P.policy_mem _
  have hy's : P.policy (a', z) ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq] at hys ⊢
    rw [P.feasible_eq] at hy's'
    exact ⟨hy's'.1, le_trans hcon.le hys.2⟩
  -- all four consumptions are positive
  have hcsy : P.consumption (a, z) (P.policy (a, z)) ∈ P.dom := P.consumption_policy_mem_dom ha
  have hcs'y' : P.consumption (a', z) (P.policy (a', z)) ∈ P.dom :=
    P.consumption_policy_mem_dom ha'
  have hcsy' : P.consumption (a, z) (P.policy (a', z)) ∈ P.dom := by
    refine P.dom_upward hcsy ?_
    simp only [consumption]; linarith
  have hcs'y : P.consumption (a', z) (P.policy (a, z)) ∈ P.dom := by
    refine P.dom_upward hcsy ?_
    simp only [consumption]; linarith
  -- increasing differences, from concavity of u alone
  have hshift := P.strictConcaveOn_u_dom.concaveOn.sub_le_sub_of_shift
    (c₁ := P.resources (a, z) - P.policy (a, z))
    (c₂ := P.resources (a, z) - P.policy (a', z))
    (Δ := P.resources (a', z) - P.resources (a, z))
    (by simpa only [consumption] using hcsy)
    (by
      have : P.resources (a, z) - P.policy (a', z)
          + (P.resources (a', z) - P.resources (a, z))
          = P.consumption (a', z) (P.policy (a', z)) := by simp only [consumption]; ring
      rw [this]; exact hcs'y')
    (by linarith) (by linarith)
  -- the poorer household's choice beats its rival at its own state
  have hopt_s := P.objR_le_of_mem ha hy's hcsy'
  -- so it also beats it at the richer state
  have hge : P.objR (a', z) (P.policy (a', z)) ≤ P.objR (a', z) (P.policy (a, z)) := by
    simp only [objR, consumption] at hopt_s ⊢
    have e₁ : P.resources (a, z) - P.policy (a', z)
        + (P.resources (a', z) - P.resources (a, z))
        = P.resources (a', z) - P.policy (a', z) := by ring
    have e₂ : P.resources (a, z) - P.policy (a, z)
        + (P.resources (a', z) - P.resources (a, z))
        = P.resources (a', z) - P.policy (a, z) := by ring
    rw [e₁, e₂] at hshift
    linarith
  -- hence the poorer household's choice is optimal at the richer state too
  have hopt' : P.objR (a', z) (P.policy (a, z)) = P.objR (a', z) (P.policy (a', z)) :=
    le_antisymm (P.objR_le_of_mem ha' hys' hcs'y) hge
  have hbell : P.toExtended.objectiveE P.toExtended.valueFunction (a', z) (P.policy (a, z))
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction (a', z) : ℝ) : EReal) := by
    rw [P.objectiveE_eq_coe ha' hys' hcs'y, hopt',
      ← P.objectiveE_eq_coe ha' hy's' hcs'y']
    exact P.policy_optimal _
  -- uniqueness collapses the two, contradicting the strict inequality
  exact absurd (P.eq_policy_of_optimal ha' hys' hbell) (by linarith)

end IncomeFluctuation

end LeanEconomics
