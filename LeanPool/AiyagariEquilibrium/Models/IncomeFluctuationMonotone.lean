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

open Set Filter Topology BoundedContinuousFunction

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

/-- The continuation value of saving `x`, read against `v`. -/
noncomputable def contOf (v : (ℝ × Z) →ᵇ ℝ) (z : Z) (x : ℝ) : ℝ :=
  ∑ z' : Z, P.transitionMatrix z z' * v (x, z')

/-- The objective, as a real number, read against `v`. -/
noncomputable def objROf (v : (ℝ × Z) →ᵇ ℝ) (s : ℝ × Z) (x : ℝ) : ℝ :=
  P.u (P.consumption s x) + P.discount * P.contOf v s.2 x

/-- The objective in the reals agrees with the extended objective where consumption is
positive. -/
theorem objectiveE_eq_coe_of (v : (ℝ × Z) →ᵇ ℝ) {a : ℝ} {z : Z} {x : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) (hx : x ∈ P.toExtended.feasible (a, z))
    (hcx : P.consumption (a, z) x ∈ P.dom) :
    P.toExtended.objectiveE v (a, z) x = ((P.objROf v (a, z) x : ℝ) : EReal) := by
  rw [ExtendedStochasticProgram.objectiveE, P.reward_eq_coe_dom (s := (a, z)) ha hx hcx,
    ← EReal.coe_add]
  rfl

/-- **Any feasible action with positive consumption is worth at most the optimum**, whatever
the continuation. -/
theorem objROf_le_of_mem (v : (ℝ × Z) →ᵇ ℝ) {a : ℝ} {z : Z} {x : ℝ}
    (ha : a ∈ Icc assetFloor assetCap) (hx : x ∈ P.toExtended.feasible (a, z))
    (hcx : P.consumption (a, z) x ∈ P.dom) :
    P.objROf v (a, z) x ≤ P.objROf v (a, z) (P.policyOf v (a, z)) := by
  have hc : P.consumption (a, z) (P.policyOf v (a, z)) ∈ P.dom :=
    (P.bellmanFn_eq_of_optimal ha (P.policyOf_mem v (a, z))
      (P.policyOf_optimal v (a, z))).1
  have hle := P.toExtended.le_bellmanFn v hx
  rw [P.objectiveE_eq_coe_of v ha hx hcx, EReal.coe_le_coe_iff] at hle
  have heq := P.policyOf_optimal v (a, z)
  rw [P.objectiveE_eq_coe_of v ha (P.policyOf_mem v (a, z)) hc,
    EReal.coe_eq_coe_iff] at heq
  exact hle.trans_eq heq.symm

/-! ### Monotonicity of the saving policy -/

/-- **The optimal policy is increasing in assets, whatever the continuation.** The exchange
argument uses concavity and uniqueness against `v`. -/
theorem policyOf_mono {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ∀ z : Z, ConcaveOn ℝ (Icc assetFloor assetCap) fun a => v (a, z)) {a a' : ℝ} {z : Z}
    (ha : a ∈ Icc assetFloor assetCap) (ha' : a' ∈ Icc assetFloor assetCap) (hle : a ≤ a') :
    P.policyOf v (a, z) ≤ P.policyOf v (a', z) := by
  by_contra hcon
  rw [not_le] at hcon
  have hR : P.resources (a, z) ≤ P.resources (a', z) := P.resources_mono hle
  have hys : P.policyOf v (a, z) ∈ P.toExtended.feasible (a, z) := P.policyOf_mem v _
  have hys' : P.policyOf v (a, z) ∈ P.toExtended.feasible (a', z) := P.feasible_mono hle hys
  have hy's' : P.policyOf v (a', z) ∈ P.toExtended.feasible (a', z) := P.policyOf_mem v _
  have hy's : P.policyOf v (a', z) ∈ P.toExtended.feasible (a, z) := by
    rw [P.feasible_eq] at hys ⊢
    rw [P.feasible_eq] at hy's'
    exact ⟨hy's'.1, le_trans hcon.le hys.2⟩
  have hcsy : P.consumption (a, z) (P.policyOf v (a, z)) ∈ P.dom :=
    (P.bellmanFn_eq_of_optimal ha (P.policyOf_mem v _) (P.policyOf_optimal v _)).1
  have hcs'y' : P.consumption (a', z) (P.policyOf v (a', z)) ∈ P.dom :=
    (P.bellmanFn_eq_of_optimal ha' (P.policyOf_mem v _) (P.policyOf_optimal v _)).1
  have hcsy' : P.consumption (a, z) (P.policyOf v (a', z)) ∈ P.dom := by
    refine P.dom_upward hcsy ?_
    simp only [consumption]; linarith
  have hcs'y : P.consumption (a', z) (P.policyOf v (a, z)) ∈ P.dom := by
    refine P.dom_upward hcsy ?_
    simp only [consumption]; linarith
  -- increasing differences, from concavity of `u` alone
  have hshift := P.strictConcaveOn_u_dom.concaveOn.sub_le_sub_of_shift
    (c₁ := P.resources (a, z) - P.policyOf v (a, z))
    (c₂ := P.resources (a, z) - P.policyOf v (a', z))
    (Δ := P.resources (a', z) - P.resources (a, z))
    (by simpa only [consumption] using hcsy)
    (by
      have he : P.resources (a, z) - P.policyOf v (a', z)
          + (P.resources (a', z) - P.resources (a, z))
          = P.consumption (a', z) (P.policyOf v (a', z)) := by simp only [consumption]; ring
      rw [he]; exact hcs'y')
    (by linarith) (by linarith)
  have hopt_s := P.objROf_le_of_mem v ha hy's hcsy'
  have hge : P.objROf v (a', z) (P.policyOf v (a', z))
      ≤ P.objROf v (a', z) (P.policyOf v (a, z)) := by
    simp only [objROf, consumption] at hopt_s ⊢
    have e₁ : P.resources (a, z) - P.policyOf v (a', z)
        + (P.resources (a', z) - P.resources (a, z))
        = P.resources (a', z) - P.policyOf v (a', z) := by ring
    have e₂ : P.resources (a, z) - P.policyOf v (a, z)
        + (P.resources (a', z) - P.resources (a, z))
        = P.resources (a', z) - P.policyOf v (a, z) := by ring
    rw [e₁, e₂] at hshift
    linarith
  have hopt' : P.objROf v (a', z) (P.policyOf v (a, z))
      = P.objROf v (a', z) (P.policyOf v (a', z)) :=
    le_antisymm (P.objROf_le_of_mem v ha' hys' hcs'y) hge
  have hbell : P.toExtended.objectiveE v (a', z) (P.policyOf v (a, z))
      = ((P.toExtended.bellmanFn v (a', z) : ℝ) : EReal) := by
    rw [P.objectiveE_eq_coe_of v ha' hys' hcs'y, hopt',
      ← P.objectiveE_eq_coe_of v ha' hy's' hcs'y']
    exact P.policyOf_optimal v _
  exact absurd (P.optimal_action_unique_of_concave hv (s := (a', z)) ha' hys' hy's'
    hbell (P.policyOf_optimal v _)) (by linarith)

/-- **The optimal policy is increasing in assets.** Holding the income state fixed, a
household with more assets saves at least as much. -/
theorem policy_mono {a a' : ℝ} {z : Z} (ha : a ∈ Icc assetFloor assetCap)
    (ha' : a' ∈ Icc assetFloor assetCap) (hle : a ≤ a') :
    P.policy (a, z) ≤ P.policy (a', z) := by
  simpa only [P.policyOf_valueFunction] using
    P.policyOf_mono P.concaveOn_valueFunction ha ha' hle

end IncomeFluctuation

end LeanEconomics
