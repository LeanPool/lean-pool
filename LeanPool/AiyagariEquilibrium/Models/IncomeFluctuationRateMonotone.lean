/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationConsumption
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationRate

/-!
# Light (2018) Theorem 1: saving rises with the interest rate

Numbered Light references use the October 31, 2018 author draft, printed page 13:
https://www.researchgate.net/publication/314238962

This is the last link in the uniqueness chain. `CapitalSupplyMonotone` turns a uniformly larger
policy into larger aggregate capital (Theorem 2), and `Equilibrium.Uniqueness` turns monotone
capital supply into a unique equilibrium rate (Theorem 3). What is still needed is that the
policy IS uniformly larger at the higher rate, which is Theorem 1.

## The comparison is at a rescaled asset level

Light's device is that two problems at different rates share a budget set. Cash on hand at
`(a, R₁)` is `y + R₁ a`, and at `(t a, R₂)` with `t = R₁ / R₂` it is `y + R₂ t a = y + R₁ a` —
the same. The saving cap is the same too, being `min assetCap (cash on hand)`. So the two
maximisations run over the SAME interval with the SAME current-consumption map, and differ only
in the continuation.

That reduces the comparison to single crossing, and single crossing here is derivative-free.
`policy_le_of_cont_increasingDifferences` is the exchange argument of `policy_mono` run in the
other direction: there, one objective at two states; here, two objectives at one state. The
hypothesis is that the continuation has INCREASING DIFFERENCES across the two rates — the
integrated form of Light's `f'(·, R₂) ≥ f'(·, R₁)`, needing no derivative and closed under
pointwise limits.

The theorem then chains

  `g(a, R₁) ≤ g(t a, R₂) ≤ g(a, R₂)`,

the first step single crossing and the second `policy_mono`, since `t ≤ 1`.

## The hypothesis `hid`, and where it is discharged

The hypothesis `hid` is the property Light propagates through the operator, and propagating it
is his step 5. That step is not derivative-free and cannot be made so: it runs on the envelope
condition `(Tf)'(a, R) = R u'(σ_f(a, R))` as an EQUALITY, and the derivative-free substitute is a
sandwich between two utility increments which is strictly loose. The Clausen–Strub lemma in
`Analysis.DifferentiableSandwich` is exactly the statement that the sandwich closes only in the
derivative limit.

It is now PROVED, in `IncomeFluctuationRateStep`: `contIncreasingDifferences_withRate`. The
envelope equality it needs is `hasDerivAt_bellman`, Clausen–Strub's lazy agent, and the other
input is the Carroll–Kimball concavity of the consumption function. Theorem 1 with `hid`
discharged is `policy_mono_withRate'`.

Worth recording precisely: his step 5 applies Lemma 4 to `σ_f(·, R₂)` and needs it CONCAVE. That
is Light's Lemma 5, which is the Carroll and Kimball theorem — the hypothesis `hT` of
`IncomeFluctuationCarrollKimball`. So the residual hypothesis here and the residual hypothesis
there are not two gaps but one: concavity of the consumption function, which by Toda (2021) is
unavailable outside HARA. Closing it closes both.

The pivotal inequality that step 5 turns on, `mul_marginal_le_of_scale`, is already proved.
-/

@[expose] public section

open Set Filter Topology

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
-- Light's rescaling `a ↦ ((1+r₁)/(1+r₂))·a` maps the asset region into itself only when the
-- borrowing limit is at zero (or non-positive), so this file is stated at a zero limit.
variable {assetCap : ℝ}
variable (P Q : IncomeFluctuation Z 0 assetCap)

/-- **Increasing differences of the continuation across two rates**: the integrated form of
Light's `f'(·, R₂) ≥ f'(·, R₁)`. No derivative, and closed under pointwise limits. -/
def ContIncreasingDifferences : Prop :=
  ∀ (z : Z) (x y : ℝ), x ∈ Icc (0 : ℝ) assetCap → y ∈ Icc (0 : ℝ) assetCap → x ≤ y →
    P.cont z y - P.cont z x ≤ Q.cont z y - Q.cont z x

/-- It suffices to have increasing differences slice by slice in the value function, when the
two economies share an income process. -/
theorem contIncreasingDifferences_of_valueFunction
    (hP : P.transitionMatrix = Q.transitionMatrix)
    (hv : ∀ (z : Z) (x y : ℝ), x ∈ Icc (0 : ℝ) assetCap → y ∈ Icc (0 : ℝ) assetCap → x ≤ y →
      P.toExtended.valueFunction (y, z) - P.toExtended.valueFunction (x, z)
        ≤ Q.toExtended.valueFunction (y, z) - Q.toExtended.valueFunction (x, z)) :
    ContIncreasingDifferences P Q := by
  intro z x y hx hy hxy
  simp only [cont, ← Finset.sum_sub_distrib, ← mul_sub]
  refine Finset.sum_le_sum fun z' _ => ?_
  rw [show P.transitionMatrix z z' = Q.transitionMatrix z z' from by rw [hP]]
  exact mul_le_mul_of_nonneg_left (hv z' x y hx hy hxy) (Q.transitionMatrix_nonneg z z')

/-- **Single crossing across rates.** Two problems whose budget sets coincide and which differ
only in the continuation are ordered by the continuation: increasing differences make the second
save at least as much.

This is the exchange argument of `policy_mono`, turned round — there one objective at two
states, here two objectives at one state. -/
theorem policy_le_of_cont_increasingDifferences
    (hu : P.u = Q.u) (hdom : P.dom = Q.dom) (hβ : (P.discount : ℝ) = (Q.discount : ℝ))
    (hid : ContIncreasingDifferences P Q)
    {a₁ a₂ : ℝ} {z : Z} (h₁ : a₁ ∈ Icc (0 : ℝ) assetCap) (h₂ : a₂ ∈ Icc (0 : ℝ) assetCap)
    (hres : P.resources (a₁, z) = Q.resources (a₂, z)) :
    P.policy (a₁, z) ≤ Q.policy (a₂, z) := by
  by_contra hcon
  rw [not_le] at hcon
  set bP : ℝ := P.policy (a₁, z) with hbP
  set bQ : ℝ := Q.policy (a₂, z) with hbQ
  -- the two budget sets coincide
  have hms : P.maxSaving (a₁, z) = Q.maxSaving (a₂, z) := by simp only [maxSaving, hres]
  have hcons : ∀ x : ℝ, P.consumption (a₁, z) x = Q.consumption (a₂, z) x := by
    intro x; simp only [consumption, hres]
  have hbPm : bP ∈ P.toExtended.feasible (a₁, z) := P.policy_mem _
  have hbQm : bQ ∈ Q.toExtended.feasible (a₂, z) := Q.policy_mem _
  rw [P.feasible_eq] at hbPm
  rw [Q.feasible_eq] at hbQm
  have hbPQ : bP ∈ Q.toExtended.feasible (a₂, z) := by
    rw [Q.feasible_eq, ← hms]; exact hbPm
  have hbQP : bQ ∈ P.toExtended.feasible (a₁, z) := by
    rw [P.feasible_eq, hms]; exact hbQm
  -- all four consumptions are positive
  have hcP : P.consumption (a₁, z) bP ∈ P.dom := P.consumption_policy_mem_dom h₁
  have hcQ : Q.consumption (a₂, z) bQ ∈ Q.dom := Q.consumption_policy_mem_dom h₂
  have hcPQ : P.consumption (a₁, z) bQ ∈ P.dom := by rw [hcons, hdom]; exact hcQ
  have hcQP : Q.consumption (a₂, z) bP ∈ Q.dom := by rw [← hcons, ← hdom]; exact hcP
  -- optimality of each against the other's choice
  have hoptP := P.objR_le_of_mem h₁ hbQP hcPQ
  have hoptQ := Q.objR_le_of_mem h₂ hbPQ hcQP
  simp only [objR, hcons, hu, hβ] at hoptP
  simp only [objR] at hoptQ
  -- increasing differences on the pair `bQ < bP`
  have hreg : bP ∈ Icc (0 : ℝ) assetCap := P.policy_mem_region _
  have hreg' : bQ ∈ Icc (0 : ℝ) assetCap := Q.policy_mem_region _
  have hidd := hid z bQ bP hreg' hreg hcon.le
  -- both optimality comparisons are therefore equalities
  have hβ0 : (0 : ℝ) ≤ Q.discount := Q.discount.coe_nonneg
  have hQeq : Q.objR (a₂, z) bP = Q.objR (a₂, z) bQ := by
    simp only [objR]
    nlinarith [hoptP, hoptQ, mul_le_mul_of_nonneg_left hidd hβ0]
  -- so the first economy's choice is optimal in the second, and uniqueness closes it
  have hbell : Q.toExtended.objectiveE Q.toExtended.valueFunction (a₂, z) bP
      = ((Q.toExtended.bellmanFn Q.toExtended.valueFunction (a₂, z) : ℝ) : EReal) := by
    rw [Q.objectiveE_eq_coe h₂ hbPQ hcQP, hQeq, ← Q.objectiveE_eq_coe h₂ (Q.policy_mem _) hcQ]
    exact Q.policy_optimal _
  exact absurd (Q.eq_policy_of_optimal h₂ hbPQ hbell) (by rw [← hbQ]; linarith)

/-! ### The rescaled asset level -/

/-- The asset level at the higher rate that gives the same cash on hand. -/
noncomputable def rateScale : ℝ := (1 + P.interest) / (1 + Q.interest)

theorem rateScale_pos : 0 < rateScale P Q :=
  div_pos P.interest_gt_neg_one Q.interest_gt_neg_one

theorem rateScale_le_one (hr : P.interest ≤ Q.interest) : rateScale P Q ≤ 1 := by
  rw [rateScale, div_le_one Q.interest_gt_neg_one]; linarith

theorem resources_rateScale (hinc : P.income = Q.income) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap)
    (z : Z) :
    P.resources (a, z) = Q.resources (rateScale P Q * a, z) := by
  have hscale : (0 : ℝ) ≤ rateScale P Q * a := mul_nonneg (rateScale_pos P Q).le ha.1
  have hmax : max 0 (rateScale P Q * a) = rateScale P Q * a := max_eq_right hscale
  simp only [resources, hinc, max_eq_right ha.1, hmax]
  simp only [rateScale]
  have hne : (1 : ℝ) + Q.interest ≠ 0 := Q.interest_gt_neg_one.ne'
  field_simp

theorem rateScale_mem (hr : P.interest ≤ Q.interest) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    rateScale P Q * a ∈ Icc (0 : ℝ) assetCap := by
  have h1 := rateScale_pos P Q
  have h2 := rateScale_le_one P Q hr
  exact ⟨mul_nonneg h1.le ha.1, by nlinarith [ha.1, ha.2]⟩

/-! ### Theorem 1 -/

/-- **Light (2018) Theorem 1.** A household facing a higher interest rate saves at least as much,
at every asset level and every income state.

The hypothesis `hid` is Light's step 5; it is discharged in `IncomeFluctuationRateStep` by
`contIncreasingDifferences_withRate`, which needs the envelope condition together with concavity
of the consumption function. See `policy_mono_withRate'` for the form without it. -/
theorem policy_mono_interest (hu : P.u = Q.u) (hdom : P.dom = Q.dom)
    (hβ : (P.discount : ℝ) = (Q.discount : ℝ))
    (hinc : P.income = Q.income) (hr : P.interest ≤ Q.interest)
    (hid : ContIncreasingDifferences P Q)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    P.policy (a, z) ≤ Q.policy (a, z) := by
  have hmem := rateScale_mem P Q hr ha
  refine le_trans (policy_le_of_cont_increasingDifferences P Q hu hdom hβ hid ha hmem
    (resources_rateScale P Q hinc ha z)) ?_
  refine Q.policy_mono hmem ha ?_
  nlinarith [rateScale_le_one P Q hr, ha.1, rateScale_pos P Q]

/-- **Theorem 1 for a rate family**, in the form `CapitalSupplyMonotone` consumes: the policy of
`P.withRate r` rises with `r`. -/
theorem policy_mono_withRate {r₁ r₂ : ℝ} (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hid : ContIncreasingDifferences (P.withRate r₁ h₁) (P.withRate r₂ h₂))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.withRate r₁ h₁).policy (a, z) ≤ (P.withRate r₂ h₂).policy (a, z) :=
  policy_mono_interest (P.withRate r₁ h₁) (P.withRate r₂ h₂) rfl rfl rfl rfl hr hid ha z

end IncomeFluctuation

end LeanEconomics
