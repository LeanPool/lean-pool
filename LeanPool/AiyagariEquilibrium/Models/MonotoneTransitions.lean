/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationEuler
public import LeanPool.AiyagariEquilibrium.Models.ImpatientDecline
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationRate

/-!
# Persistent income: the decline condition from monotone transitions

Açıkgöz's decline argument (`policy_lt_self_of_impatient`) runs the Euler inequality at the state
where consumption is lowest, and needs to know which state that is. With iid income it is the
lowest-income state, because every state shares a continuation. With persistent income the
continuations differ, and the lowest-income state is still the lowest-consumption state only if
its continuation is the STEEPEST — a poor household today expects to be poor tomorrow, so wealth
is worth more to it at the margin.

That is Huggett (1993) Lemma 1, `v'(a, e_h) ≤ v'(a, e_l)`, proved there by induction on the
Bellman iterates under `π(e_h | e_h) ≥ π(e_h | e_l)`. This file is that induction, in secant form
and for a finite income process ordered by income.

## Monotone transitions

The condition is stated by its use: a state with higher income has a transition row that makes
every income-antitone function of tomorrow's state smaller in expectation
(`MonotoneTransitions`). For two states it is exactly Huggett's `π(h|h) ≥ π(h|l)`
(`monotoneTransitions_of_two_states`); for a Tauchen chain it is first-order stochastic
dominance of the rows, which the chain has by construction.

## The induction

`IncDiffAcrossStates v` says the increments of `v` in assets are antitone in income. It survives
the Bellman operator because the envelope derivative is `R · u'(c)` and consumption at a fixed
asset level is increasing in income (`consumptionFnOf_le_across_states`) — which in turn follows
from single crossing: a richer household with a flatter continuation saves less of its extra
resources than it receives. The base case is the zero continuation, and the property passes to
the value function as a pointwise limit.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-! ### The two properties -/

/-- **Monotone transitions.** A higher-income state's transition row makes every
income-antitone function of tomorrow's state smaller in expectation: first-order stochastic
dominance of the rows, in the income order. -/
def MonotoneTransitions : Prop :=
  ∀ z₁ z₂ : Z, P.income z₁ ≤ P.income z₂ → ∀ f : Z → ℝ,
    (∀ w₁ w₂ : Z, P.income w₁ ≤ P.income w₂ → f w₂ ≤ f w₁) →
    ∑ z' : Z, P.transitionMatrix z₂ z' * f z' ≤ ∑ z' : Z, P.transitionMatrix z₁ z' * f z'

/-- iid income has monotone transitions, trivially: the rows are all equal. -/
theorem monotoneTransitions_of_iid (hiid : P.IidIncome) : P.MonotoneTransitions := by
  intro z₁ z₂ _ f _
  exact le_of_eq (Finset.sum_congr rfl fun z' _ => by rw [hiid z₂ z₁ z'])

/-- Changing the rate leaves the income process, hence monotonicity, untouched. -/
theorem monotoneTransitions_withRate {assetCap : ℝ} {P : IncomeFluctuation Z 0 assetCap}
    (hmono : P.MonotoneTransitions) {r : ℝ} (hrr : P.RateOK r) :
    (P.withRate r hrr).MonotoneTransitions := hmono

/-- **Increments of `v` in assets are antitone in income**: the secant form of Huggett's
`v'(a, e_h) ≤ v'(a, e_l)`. -/
def IncDiffAcrossStates (v : (ℝ × Z) →ᵇ ℝ) : Prop :=
  ∀ z₁ z₂ : Z, P.income z₁ ≤ P.income z₂ → ∀ x y : ℝ,
    x ∈ Icc assetFloor assetCap → y ∈ Icc assetFloor assetCap → x ≤ y →
    v (y, z₂) - v (x, z₂) ≤ v (y, z₁) - v (x, z₁)

theorem incDiffAcrossStates_zero : P.IncDiffAcrossStates 0 := by
  intro _ _ _ _ _ _ _ _
  simp

/-- The continuation inherits the property, by monotone transitions: the increment
`v (y, ·) - v (x, ·)` is income-antitone, and the poorer state's row weights it more. -/
theorem contOf_sub_le_across_states (hmono : P.MonotoneTransitions) {v : (ℝ × Z) →ᵇ ℝ}
    (hv : P.IncDiffAcrossStates v) {z₁ z₂ : Z} (hz : P.income z₁ ≤ P.income z₂)
    {x y : ℝ} (hx : x ∈ Icc assetFloor assetCap) (hy : y ∈ Icc assetFloor assetCap)
    (hxy : x ≤ y) :
    P.contOf v z₂ y - P.contOf v z₂ x ≤ P.contOf v z₁ y - P.contOf v z₁ x := by
  simp only [contOf, ← Finset.sum_sub_distrib, ← mul_sub]
  exact hmono z₁ z₂ hz (fun z' => v (y, z') - v (x, z')) fun w₁ w₂ hw => hv w₁ w₂ hw x y hx hy hxy

/-! ### Consumption rises with income at a fixed asset level

The exchange argument of `consumptionFn_mono_of_cont_eq`, with the shared continuation replaced
by an ordered pair: the richer state has a flatter continuation as well as more resources, and
both push consumption up. -/

/-- **Consumption is ordered across states** against a continuation whose increments are
antitone in income. -/
theorem consumptionFnOf_le_across_states {v : (ℝ × Z) →ᵇ ℝ}
    (hv : ConcaveSlices assetFloor assetCap v) {z₁ z₂ : Z}
    (hid : ∀ x y : ℝ, x ∈ Icc assetFloor assetCap → y ∈ Icc assetFloor assetCap → x ≤ y →
      P.contOf v z₂ y - P.contOf v z₂ x ≤ P.contOf v z₁ y - P.contOf v z₁ x)
    {a a' : ℝ} (ha : a ∈ Icc assetFloor assetCap) (ha' : a' ∈ Icc assetFloor assetCap)
    (hres : P.resources (a, z₁) ≤ P.resources (a', z₂)) :
    P.consumptionFnOf v z₁ a ≤ P.consumptionFnOf v z₂ a' := by
  set Δ : ℝ := P.resources (a', z₂) - P.resources (a, z₁) with hΔdef
  have hΔ : 0 ≤ Δ := by rw [hΔdef]; linarith
  set b : ℝ := P.policyOf v (a, z₁) with hbdef
  set b' : ℝ := P.policyOf v (a', z₂) with hb'def
  by_contra hcon
  rw [not_le] at hcon
  have hgap : b + Δ < b' := by
    simp only [consumptionFnOf, consumption] at hcon
    rw [hΔdef]; linarith
  have hbmem : b ∈ P.toExtended.feasible (a, z₁) := P.policyOf_mem v (a, z₁)
  have hb'mem : b' ∈ P.toExtended.feasible (a', z₂) := P.policyOf_mem v (a', z₂)
  rw [P.feasible_eq] at hbmem hb'mem
  have hms : P.maxSaving (a', z₂) ≤ P.maxSaving (a, z₁) + Δ := by
    have hmin : min assetCap (P.resources (a', z₂))
        ≤ min assetCap (P.resources (a, z₁)) + Δ := by
      rcases le_total assetCap (P.resources (a, z₁)) with h | h
      · rw [min_eq_left h]
        exact le_trans (min_le_left _ _) (by linarith)
      · rw [min_eq_right h]
        exact le_trans (min_le_right _ _) (by rw [hΔdef]; linarith)
    rw [P.maxSaving_eq, P.maxSaving_eq]
    linarith
  have hshiftup : b + Δ ∈ P.toExtended.feasible (a', z₂) := by
    rw [P.feasible_eq]
    exact ⟨by linarith [hbmem.1], by linarith [hb'mem.2]⟩
  have hshiftdown : b' - Δ ∈ P.toExtended.feasible (a, z₁) := by
    rw [P.feasible_eq]
    exact ⟨by linarith [hbmem.1], by linarith [hb'mem.2]⟩
  have hc1 : P.consumption (a, z₁) b ∈ P.dom := P.consumption_policyOf_mem_dom v ha
  have hc2 : P.consumption (a', z₂) b' ∈ P.dom := P.consumption_policyOf_mem_dom v ha'
  have he1 : P.consumption (a', z₂) (b + Δ) = P.consumption (a, z₁) b := by
    simp only [consumption, hΔdef]; ring
  have he2 : P.consumption (a, z₁) (b' - Δ) = P.consumption (a', z₂) b' := by
    simp only [consumption, hΔdef]; ring
  have hI := P.objROf_le_of_mem v ha hshiftdown (by rw [he2]; exact hc2)
  have hII := P.objROf_le_of_mem v ha' hshiftup (by rw [he1]; exact hc1)
  have hbreg : b ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policyOf_mem v _)
  have hb'reg : b' ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policyOf_mem v _)
  -- concavity of the poorer continuation, shifted by `Δ`
  have hshift := (P.concaveOn_contOf hv z₁).sub_le_sub_of_shift (c₁ := b) (c₂ := b' - Δ) (Δ := Δ)
    hbreg (by simpa using hb'reg) (by linarith) hΔ
  rw [sub_add_cancel] at hshift
  -- and the richer continuation is flatter still
  have hacross := hid (b + Δ) b' ⟨by linarith [hbreg.1], by linarith [hb'reg.2]⟩ hb'reg hgap.le
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hchain := mul_le_mul_of_nonneg_left (le_trans hacross hshift) hβ
  simp only [objROf, he1, he2] at hI hII
  have hIIeq : P.objROf v (a', z₂) (b + Δ) = P.objROf v (a', z₂) b' := by
    simp only [objROf, he1]
    linarith [hI, hII, hchain]
  have hbell : P.toExtended.objectiveE v (a', z₂) (b + Δ)
      = ((P.toExtended.bellmanFn v (a', z₂) : ℝ) : EReal) := by
    rw [P.objectiveE_eq_coe_of v ha' hshiftup (by rw [he1]; exact hc1), hIIeq,
      ← P.objectiveE_eq_coe_of v ha' (P.policyOf_mem v _) hc2]
    exact P.policyOf_optimal v _
  exact absurd (P.optimal_action_unique_of_concaveSlices hv ha' hshiftup (P.policyOf_mem v _)
    hbell (P.policyOf_optimal v _)) (by rw [← hb'def]; linarith)

/-! ### The Bellman step, by the envelope -/

/-- **Huggett's Lemma 1, one step.** If `v` has income-antitone increments then so does
`bellman v`: the derivative of `bellman v (·, z)` is `R · u'(c_v(·, z))`, and consumption at a
fixed asset level rises with income. -/
theorem incDiffAcrossStates_bellman (hmono : P.MonotoneTransitions)
    {v : (ℝ × Z) →ᵇ ℝ} {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ)))
    (hv : ConcaveSlices assetFloor assetCap v) (hpc : P.PositiveConsumptionAll)
    (hslack : ∀ x ∈ Icc assetFloor assetCap, ∀ z : Z, P.policyOf v (x, z) < assetCap)
    (hid : P.IncDiffAcrossStates v) :
    P.IncDiffAcrossStates (P.toExtended.bellman v) := by
  intro z₁ z₂ hz x y hx hy hxy
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  -- the difference `bellman v (·, z₁) - bellman v (·, z₂)` is monotone in assets
  have key : ∀ a ∈ Ioo assetFloor assetCap, ∃ D : ℝ, 0 ≤ D ∧
      HasDerivAt (fun t => (P.toExtended.bellman v) (t, z₁) - (P.toExtended.bellman v) (t, z₂))
        D a := by
    intro a ha
    have hamem : a ∈ Icc assetFloor assetCap := ⟨ha.1.le, ha.2.le⟩
    have hpos₁ : 0 < P.consumptionFnOf v z₁ a := hpc v hv z₁ a hamem
    have hpos₂ : 0 < P.consumptionFnOf v z₂ a := hpc v hv z₂ a hamem
    have hd₁ := P.hasDerivAt_bellman ha.1 ha.2 (P.concaveSlices_bellman hv z₁)
      (P.policyOf_lt_maxSaving hpc hv hamem (hslack a hamem z₁)) hpos₁ (hderiv _ hpos₁)
    have hd₂ := P.hasDerivAt_bellman ha.1 ha.2 (P.concaveSlices_bellman hv z₂)
      (P.policyOf_lt_maxSaving hpc hv hamem (hslack a hamem z₂)) hpos₂ (hderiv _ hpos₂)
    refine ⟨_, ?_, hd₁.sub hd₂⟩
    have hc : P.consumptionFnOf v z₁ a ≤ P.consumptionFnOf v z₂ a :=
      P.consumptionFnOf_le_across_states hv
        (fun x y hx hy hxy => P.contOf_sub_le_across_states hmono hid hz hx hy hxy) hamem hamem
        (by simp only [resources]; linarith)
    have hdu := hanti (mem_Ioi.mpr hpos₁) (mem_Ioi.mpr hpos₂) hc
    nlinarith [hR]
  have hmonoOn : MonotoneOn
      (fun t => (P.toExtended.bellman v) (t, z₁) - (P.toExtended.bellman v) (t, z₂))
      (Icc assetFloor assetCap) := by
    refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
    · exact (((P.toExtended.bellman v).continuous.comp
        (continuous_id.prodMk continuous_const)).sub ((P.toExtended.bellman v).continuous.comp
        (continuous_id.prodMk continuous_const))).continuousOn
    · rw [interior_Icc]
      intro t ht
      obtain ⟨D, _, hD⟩ := key t ht
      exact hD.differentiableAt.differentiableWithinAt
    · rw [interior_Icc]
      intro t ht
      obtain ⟨D, hD0, hD⟩ := key t ht
      rw [hD.deriv]
      exact hD0
  have := hmonoOn hx hy hxy
  simp only at this
  linarith

/-! ### Along the iteration, and at the fixed point -/

/-- **Huggett's Lemma 1 for the value function.** -/
theorem incDiffAcrossStates_valueFunction (hmono : P.MonotoneTransitions) {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hpc : P.PositiveConsumptionAll)
    (hslack : ∀ n : ℕ, ∀ x ∈ Icc assetFloor assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (x, z) < assetCap) :
    P.IncDiffAcrossStates P.toExtended.valueFunction := by
  have hslices : ∀ n : ℕ,
      ConcaveSlices assetFloor assetCap ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact concaveSlices_zero
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact P.concaveSlices_bellman ih
  have hstep : ∀ n : ℕ, P.IncDiffAcrossStates ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) := by
    intro n
    induction n with
    | zero => exact P.incDiffAcrossStates_zero
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact P.incDiffAcrossStates_bellman hmono hderiv hanti (hslices k) hpc (hslack k) ih
  have hpt : ∀ p : ℝ × Z,
      Tendsto (fun n => ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) p) atTop
        (𝓝 (P.toExtended.valueFunction p)) := fun p =>
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp
      (P.toExtended.tendsto_iterate_valueFunction 0)).tendsto_at p
  intro z₁ z₂ hz x y hx hy hxy
  exact le_of_tendsto_of_tendsto ((hpt (y, z₂)).sub (hpt (x, z₂))) ((hpt (y, z₁)).sub (hpt (x, z₁)))
    (Eventually.of_forall fun n => hstep n z₁ z₂ hz x y hx hy hxy)

/-- **Consumption is lowest where income is lowest**, for a persistent income process with
monotone transitions. The replacement for `consumptionFn_le_of_income_le`. -/
theorem consumptionFn_le_of_income_le_monotone (hmono : P.MonotoneTransitions) {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hpc : P.PositiveConsumptionAll)
    (hslack : ∀ n : ℕ, ∀ x ∈ Icc assetFloor assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (x, z) < assetCap)
    {z₁ z₂ : Z} (hinc : P.income z₁ ≤ P.income z₂) {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) :
    P.consumptionFn z₁ a ≤ P.consumptionFn z₂ a :=
  P.consumptionFnOf_le_across_states (v := P.toExtended.valueFunction) P.concaveSlices_valueFunction
    (fun x y hx hy hxy => P.contOf_sub_le_across_states hmono
      (P.incDiffAcrossStates_valueFunction hmono hderiv hanti hpc hslack) hinc hx hy hxy)
    ha ha (by simp only [resources]; linarith)

/-- **Açıkgöz Proposition 4 with persistent income.** Assets strictly decline at the lowest
income state, at every asset level above the borrowing constraint, given `β(1+r) < 1` and
monotone transitions. -/
theorem policy_lt_self_of_impatient_monotone
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) (hmono : P.MonotoneTransitions)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpc : P.PositiveConsumptionAll)
    (hslackIt : ∀ n : ℕ, ∀ x ∈ Icc assetFloor assetCap, ∀ z : Z,
      P.policyOf ((P.toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (x, z) < assetCap)
    (hslack : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, P.policy (x, z) < P.maxSaving (x, z))
    {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (ha0 : assetFloor < a) :
    P.policy (a, z₀) < a :=
  P.policy_lt_self_of_impatient hβR hderiv hanti hdupos
    (fun z x hx => hpc _ P.concaveSlices_valueFunction z x hx) hslack ha ha0
    (fun z' => P.consumptionFn_le_of_income_le_monotone hmono hderiv hanti hpc hslackIt (hz₀ z') ha)

/-! ### Two states -/

/-- **Huggett's condition is monotone transitions**, for two income states ordered by income:
`π(h | h) ≥ π(h | l)`. -/
theorem monotoneTransitions_of_two_states {assetFloor assetCap : ℝ}
    (P : IncomeFluctuation (Fin 2) assetFloor assetCap)
    (hinc : P.income 0 ≤ P.income 1)
    (hπ : P.transitionMatrix 0 1 ≤ P.transitionMatrix 1 1) : P.MonotoneTransitions := by
  intro z₁ z₂ hz f hf
  have hrow : ∀ z : Fin 2, P.transitionMatrix z 0 = 1 - P.transitionMatrix z 1 := by
    intro z
    have := P.transitionMatrix_sum z
    simp only [Fin.sum_univ_two] at this
    linarith
  have hsum : ∀ z : Fin 2, ∑ z' : Fin 2, P.transitionMatrix z z' * f z'
      = f 0 + P.transitionMatrix z 1 * (f 1 - f 0) := by
    intro z
    simp only [Fin.sum_univ_two, hrow z]
    ring
  rw [hsum, hsum]
  have hf10 : f 1 ≤ f 0 := hf 0 1 hinc
  have h₁ : z₁ = 0 ∨ z₁ = 1 := by fin_cases z₁ <;> simp
  have h₂ : z₂ = 0 ∨ z₂ = 1 := by fin_cases z₂ <;> simp
  rcases h₁ with rfl | rfl <;> rcases h₂ with rfl | rfl
  · exact le_rfl
  · nlinarith
  · -- `income 1 ≤ income 0` forces the incomes equal, hence `f 0 = f 1`
    have hf01 : f 0 ≤ f 1 := hf 1 0 hz
    nlinarith
  · exact le_rfl

end IncomeFluctuation

end LeanEconomics
