/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationIterate
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationRateMonotone

/-!
# Light (2018), step 5: increasing differences propagate across rates

`IncomeFluctuationRateMonotone` reduces Theorem 1 to one hypothesis, `ContIncreasingDifferences`,
and records that propagating it needs two things this development did not have: the envelope
condition as an EQUALITY, and concavity of the consumption function. Both are now proved
(`hasDerivAt_bellman`, `concaveOn_consumptionFnOf_bellman`), so the step is available.

## The identity the whole thing rests on

Two rates share a budget set: cash on hand at `(a, R₁)` equals cash on hand at `(t a, R₂)` for
`t = R₁ / R₂`, and the saving cap is the same because it is `min assetCap (cash on hand)`. So the
two maximisations are literally the same maximisation, and `lazyValue_withRate` says so. Hence
`bellmanFn_withRate`, `policyOf_withRate` and `consumptionFnOf_withRate`: the whole solution at
`(a, R₁)` is the solution at `(t a, R₂)`.

That turns the difference `(T_{R₂} f)(a) - (T_{R₁} f)(a)` into `(T_{R₂} f)(a) - (T_{R₂} f)(t a)`,
a statement about ONE economy, and increasing differences across rates becomes monotonicity of
that difference in `a`. The envelope makes its derivative `R₂ u'(c_w(a)) - R₁ u'(c_v(t a))`,
where `v` and `w` are the two continuations, and two moves sign it: single crossing in the
continuation at the scaled asset level, then `mul_marginal_le_of_scale` — concavity of the
consumption function for one factor, relative risk aversion at most one for the other.

Doing it in that order matters. Applying the pivotal inequality directly to `c_v` would need
Carroll–Kimball for economy two's choice against economy ONE's continuation, a hybrid object no
induction produces; going through `c_v(t a) ≥ c_w(t a)` first puts the pivotal inequality on
`c_w`, economy two's own, which is exactly what `concaveOn_consumptionFn_of_iterates` delivers.

## What is left

`contIncreasingDifferences_withRate` discharges the `hid` of `policy_mono_interest`, so Light's
Theorem 1 holds outright. Its hypotheses are the standing ones of this development: utility
differentiable with decreasing, non-negative marginal utility and relative risk aversion at most
one; consumption positive at every optimum; the asset cap slack along the iteration; and the
Carroll–Kimball concavity of the iterates' consumption functions. `CESConcaveConsumption` shows
these hold together at concrete CES calibrations.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### The two rates solve the same problem at rescaled assets -/

variable {r₁ r₂ : ℝ}

/-- **The objective at `(a, r₁)` is the objective at `(t a, r₂)`**, action for action. -/
theorem lazyValue_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (v : (ℝ × Z) →ᵇ ℝ) (z : Z)
    (x : ℝ) {a : ℝ} (ha : 0 ≤ a) :
    (P.withRate r₁ h₁).lazyValue v z x a
      = (P.withRate r₂ h₂).lazyValue v z x ((1 + r₁) / (1 + r₂) * a) := by
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hscale : (0 : ℝ) ≤ (1 + r₁) / (1 + r₂) * a := by
    have : (0 : ℝ) < 1 + r₁ := h₁.1
    positivity
  have harg : P.income z + (1 + r₂) * ((1 + r₁) / (1 + r₂) * a)
      = P.income z + (1 + r₁) * a := by field_simp
  simp only [lazyValue, resources, IncomeFluctuation.withRate_income,
    IncomeFluctuation.withRate_interest, IncomeFluctuation.withRate_discount,
    IncomeFluctuation.withRate_transitionMatrix, IncomeFluctuation.withRate_u,
    max_eq_right ha, max_eq_right hscale, harg]

/-- The feasible sets coincide. -/
theorem feasible_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (z : Z) {a : ℝ} (ha : 0 ≤ a) :
    (P.withRate r₁ h₁).toExtended.feasible (a, z)
      = (P.withRate r₂ h₂).toExtended.feasible ((1 + r₁) / (1 + r₂) * a, z) := by
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hscale : (0 : ℝ) ≤ (1 + r₁) / (1 + r₂) * a := by
    have : (0 : ℝ) < 1 + r₁ := h₁.1
    positivity
  have hres : (P.withRate r₁ h₁).resources (a, z)
      = (P.withRate r₂ h₂).resources ((1 + r₁) / (1 + r₂) * a, z) := by
    have harg : P.income z + (1 + r₂) * ((1 + r₁) / (1 + r₂) * a)
        = P.income z + (1 + r₁) * a := by field_simp
    simp only [resources, IncomeFluctuation.withRate_income,
      IncomeFluctuation.withRate_interest, max_eq_right ha, max_eq_right hscale, harg]
  rw [(P.withRate r₁ h₁).feasible_eq, (P.withRate r₂ h₂).feasible_eq,
    (P.withRate r₁ h₁).maxSaving_eq, (P.withRate r₂ h₂).maxSaving_eq, hres]

/-- Consumption at a given action coincides. -/
theorem consumption_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (z : Z) (x : ℝ) {a : ℝ}
    (ha : 0 ≤ a) :
    (P.withRate r₁ h₁).consumption (a, z) x
      = (P.withRate r₂ h₂).consumption ((1 + r₁) / (1 + r₂) * a, z) x := by
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hscale : (0 : ℝ) ≤ (1 + r₁) / (1 + r₂) * a := by
    have : (0 : ℝ) < 1 + r₁ := h₁.1
    positivity
  have harg : P.income z + (1 + r₂) * ((1 + r₁) / (1 + r₂) * a)
      = P.income z + (1 + r₁) * a := by field_simp
  simp only [consumption, resources, IncomeFluctuation.withRate_income,
    IncomeFluctuation.withRate_interest, max_eq_right ha, max_eq_right hscale, harg]

/-- **The whole solution at `(a, r₁)` is the solution at `(t a, r₂)`.** -/
theorem bellmanFn_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (v : (ℝ × Z) →ᵇ ℝ) (z : Z) {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).toExtended.bellmanFn v (a, z)
      = (P.withRate r₂ h₂).toExtended.bellmanFn v ((1 + r₁) / (1 + r₂) * a, z) := by
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have ht1 : (1 + r₁) / (1 + r₂) ≤ 1 := by rw [div_le_one hR₂]; linarith
  have hscale : (1 + r₁) / (1 + r₂) * a ∈ Icc (0 : ℝ) assetCap := by
    refine ⟨mul_nonneg (le_of_lt (div_pos hR₁ hR₂)) ha.1, ?_⟩
    nlinarith [ha.1, ha.2, div_pos hR₁ hR₂]
  refine le_antisymm ?_ ?_
  · set b := (P.withRate r₁ h₁).policyOf v (a, z) with hb
    have heq := (P.withRate r₁ h₁).lazyValue_eq_dom v z ha
      ((P.withRate r₁ h₁).policyOf_mem v (a, z))
      ((P.withRate r₁ h₁).consumption_policyOf_mem_dom v ha)
      ((P.withRate r₁ h₁).policyOf_optimal v (a, z))
    have hfe : b ∈ (P.withRate r₂ h₂).toExtended.feasible ((1 + r₁) / (1 + r₂) * a, z) := by
      rw [← P.feasible_withRate h₁ h₂ z ha.1]
      exact (P.withRate r₁ h₁).policyOf_mem v (a, z)
    have hcd : (P.withRate r₂ h₂).consumption ((1 + r₁) / (1 + r₂) * a, z) b
        ∈ (P.withRate r₂ h₂).dom := by
      rw [← P.consumption_withRate h₁ h₂ z b ha.1]
      exact (P.withRate r₁ h₁).consumption_policyOf_mem_dom v ha
    have hle := (P.withRate r₂ h₂).lazyValue_le_dom v z hscale hfe hcd
    rw [← P.lazyValue_withRate h₁ h₂ v z b ha.1, heq] at hle
    exact hle
  · set b := (P.withRate r₂ h₂).policyOf v ((1 + r₁) / (1 + r₂) * a, z) with hb
    have heq := (P.withRate r₂ h₂).lazyValue_eq_dom v z hscale
      ((P.withRate r₂ h₂).policyOf_mem v _)
      ((P.withRate r₂ h₂).consumption_policyOf_mem_dom v hscale)
      ((P.withRate r₂ h₂).policyOf_optimal v _)
    have hfe : b ∈ (P.withRate r₁ h₁).toExtended.feasible (a, z) := by
      rw [P.feasible_withRate h₁ h₂ z ha.1]
      exact (P.withRate r₂ h₂).policyOf_mem v _
    have hcd : (P.withRate r₁ h₁).consumption (a, z) b ∈ (P.withRate r₁ h₁).dom := by
      rw [P.consumption_withRate h₁ h₂ z b ha.1]
      exact (P.withRate r₂ h₂).consumption_policyOf_mem_dom v hscale
    have hle := (P.withRate r₁ h₁).lazyValue_le_dom v z ha hfe hcd
    rw [P.lazyValue_withRate h₁ h₂ v z b ha.1, heq] at hle
    exact hle

/-- **The saving chosen at `(a, r₁)` is the saving chosen at `(t a, r₂)`.** -/
theorem policyOf_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices (0 : ℝ) assetCap v) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).policyOf v (a, z)
      = (P.withRate r₂ h₂).policyOf v ((1 + r₁) / (1 + r₂) * a, z) := by
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have ht1 : (1 + r₁) / (1 + r₂) ≤ 1 := by rw [div_le_one hR₂]; linarith
  have hscale : (1 + r₁) / (1 + r₂) * a ∈ Icc (0 : ℝ) assetCap := by
    refine ⟨mul_nonneg (le_of_lt (div_pos hR₁ hR₂)) ha.1, ?_⟩
    nlinarith [ha.1, ha.2, div_pos hR₁ hR₂]
  set b := (P.withRate r₁ h₁).policyOf v (a, z) with hb
  have hfe : b ∈ (P.withRate r₂ h₂).toExtended.feasible ((1 + r₁) / (1 + r₂) * a, z) := by
    rw [← P.feasible_withRate h₁ h₂ z ha.1]
    exact (P.withRate r₁ h₁).policyOf_mem v (a, z)
  have hcd : (P.withRate r₂ h₂).consumption ((1 + r₁) / (1 + r₂) * a, z) b
      ∈ (P.withRate r₂ h₂).dom := by
    rw [← P.consumption_withRate h₁ h₂ z b ha.1]
    exact (P.withRate r₁ h₁).consumption_policyOf_mem_dom v ha
  refine (P.withRate r₂ h₂).optimal_action_unique_of_concaveSlices hv
    (s := ((1 + r₁) / (1 + r₂) * a, z)) hscale hfe
    ((P.withRate r₂ h₂).policyOf_mem v _) ?_ ((P.withRate r₂ h₂).policyOf_optimal v _)
  rw [(P.withRate r₂ h₂).objectiveE_eq_coe_of v hscale hfe hcd,
    ← P.bellmanFn_withRate h₁ h₂ hr v z ha]
  have hobj : (P.withRate r₂ h₂).objROf v ((1 + r₁) / (1 + r₂) * a, z) b
      = (P.withRate r₁ h₁).lazyValue v z b a := by
    change (P.withRate r₂ h₂).lazyValue v z b ((1 + r₁) / (1 + r₂) * a) = _
    rw [P.lazyValue_withRate h₁ h₂ v z b ha.1]
  rw [hobj]
  exact congrArg _ ((P.withRate r₁ h₁).lazyValue_eq_dom v z ha
    ((P.withRate r₁ h₁).policyOf_mem v (a, z))
    ((P.withRate r₁ h₁).consumption_policyOf_mem_dom v ha)
    ((P.withRate r₁ h₁).policyOf_optimal v (a, z)))

/-- **Consumption too.** This is the function `mul_marginal_le_of_scale` is applied to. -/
theorem consumptionFnOf_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    {v : (ℝ × Z) →ᵇ ℝ} (hv : ConcaveSlices (0 : ℝ) assetCap v) (z : Z) {a : ℝ}
    (ha : a ∈ Icc (0 : ℝ) assetCap) :
    (P.withRate r₁ h₁).consumptionFnOf v z a
      = (P.withRate r₂ h₂).consumptionFnOf v z ((1 + r₁) / (1 + r₂) * a) := by
  simp only [consumptionFnOf]
  rw [P.policyOf_withRate h₁ h₂ hr hv z ha, P.consumption_withRate h₁ h₂ z _ ha.1]

/-! ### The derivative assembly

With the budget coincidence in hand the whole comparison lives in ONE economy: the difference to
be signed is

  `F a = (T w)(a) - (T v)(t a)`,     `t = R₁ / R₂ ≤ 1`.

`hasDerivAt_bellman` — the Clausen–Strub lazy-agent envelope — differentiates both terms, giving

  `F' a = R₂ u'(c_w(a)) - t R₂ u'(c_v(t a)) = R₂ u'(c_w(a)) - R₁ u'(c_v(t a))`.

The second term is signed in two moves. Single crossing in the continuation puts
`c_w(t a) ≤ c_v(t a)`, so `u'(c_v(t a)) ≤ u'(c_w(t a))`; and then `mul_marginal_le_of_scale`,
Light's pivotal inequality, carries `R₁ u'(c_w(t a)) ≤ R₂ u'(c_w(a))`. Note which consumption
function the pivotal inequality is applied to: `c_w`, economy TWO's own, whose concavity is what
Carroll–Kimball delivers. Routing the comparison through `c_w` rather than through `c_v` is what
keeps the argument inside one economy's Carroll–Kimball theorem — `c_v` is the hybrid object
(economy two's choice against economy one's continuation) and no concavity of it is needed.

Note what the envelope is asked for: the state interior and the CHOICE strictly below the saving
cap. Nothing is asked at the borrowing constraint, so the argument survives where it binds. -/

/-- **The monotone difference, in one economy, from the pivotal inequality as a hypothesis.** If
`t ≤ 1`, the continuations `v` and `w` have increasing differences, and `t R u'(c_w(t a)) ≤
R u'(c_w(a))` at every interior `a`, then `a ↦ (T w)(a) - (T v)(t a)` is nondecreasing. -/
theorem monotoneOn_bellman_sub_scaled_of_piv {assetCap : ℝ} (Q : IncomeFluctuation Z 0 assetCap)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {v w : (ℝ × Z) →ᵇ ℝ} {z : Z} {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt Q.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ)))
    (hwc : ConcaveSlices (0 : ℝ) assetCap w) (hid : Q.ContOfIncreasingDifferences v w)
    (hbv : ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      fun x => (Q.toExtended.bellman v) (x, z))
    (hbw : ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      fun x => (Q.toExtended.bellman w) (x, z))
    (hintv : ∀ x ∈ Icc (0 : ℝ) assetCap, Q.policyOf v (x, z) < Q.maxSaving (x, z))
    (hintw : ∀ x ∈ Icc (0 : ℝ) assetCap, Q.policyOf w (x, z) < Q.maxSaving (x, z))
    (hposv : ∀ x ∈ Icc (0 : ℝ) assetCap, 0 < Q.consumptionFnOf v z x)
    (hposw : ∀ x ∈ Icc (0 : ℝ) assetCap, 0 < Q.consumptionFnOf w z x)
    (hpiv : ∀ a ∈ Ioo (0 : ℝ) assetCap,
      t * (1 + Q.interest) * du (Q.consumptionFnOf w z (t * a))
        ≤ (1 + Q.interest) * du (Q.consumptionFnOf w z a)) :
    MonotoneOn (fun a => (Q.toExtended.bellman w) (a, z) - (Q.toExtended.bellman v) (t * a, z))
      (Icc (0 : ℝ) assetCap) := by
  have hR : (0 : ℝ) < 1 + Q.interest := Q.interest_gt_neg_one
  -- the derivative, and its sign, at every interior point
  have key : ∀ a ∈ Ioo (0 : ℝ) assetCap, ∃ D : ℝ, 0 ≤ D ∧
      HasDerivAt (fun x => (Q.toExtended.bellman w) (x, z) - (Q.toExtended.bellman v) (t * x, z))
        D a := by
    intro a ha
    have ha0 : (0 : ℝ) < a := ha.1
    have hamem : a ∈ Icc (0 : ℝ) assetCap := ⟨ha.1.le, ha.2.le⟩
    have hta0 : (0 : ℝ) < t * a := mul_pos ht0 ha0
    have htale : t * a ≤ a := by nlinarith
    have htamem : t * a ∈ Icc (0 : ℝ) assetCap := ⟨hta0.le, le_trans htale hamem.2⟩
    -- the two envelope derivatives
    have hd1 : HasDerivAt (fun x => (Q.toExtended.bellman w) (x, z))
        ((1 + Q.interest) * du (Q.consumptionFnOf w z a)) a :=
      Q.hasDerivAt_bellman ha0 ha.2 hbw (hintw a hamem) (hposw a hamem)
        (hderiv _ (hposw a hamem))
    have hbase : HasDerivAt (fun x => (Q.toExtended.bellman v) (x, z))
        ((1 + Q.interest) * du (Q.consumptionFnOf v z (t * a))) (t * a) :=
      Q.hasDerivAt_bellman hta0 (lt_of_le_of_lt htale ha.2) hbv (hintv _ htamem)
        (hposv _ htamem) (hderiv _ (hposv _ htamem))
    have hlin : HasDerivAt (fun x : ℝ => t * x) t a := by
      simpa using (hasDerivAt_id a).const_mul t
    have hd2 : HasDerivAt (fun x : ℝ => (Q.toExtended.bellman v) (t * x, z))
        ((1 + Q.interest) * du (Q.consumptionFnOf v z (t * a)) * t) a := hbase.comp a hlin
    refine ⟨_, ?_, hd1.sub hd2⟩
    have hpiv := hpiv a ha
    -- single crossing in the continuation, at the SCALED asset level
    have hcross : Q.consumptionFnOf w z (t * a) ≤ Q.consumptionFnOf v z (t * a) :=
      Q.consumptionFnOf_le_of_contOf_increasingDifferences hwc hid htamem
    have hdu := hanti (mem_Ioi.mpr (hposw _ htamem)) (mem_Ioi.mpr (hposv _ htamem)) hcross
    have ht1' : (0 : ℝ) < t * (1 + Q.interest) := by positivity
    nlinarith [hpiv, hdu, hR, ht1']
  refine monotoneOn_of_deriv_nonneg (convex_Icc _ _) ?_ ?_ ?_
  · refine ContinuousOn.sub ?_ ?_
    · exact ((Q.toExtended.bellman w).continuous.comp
        (continuous_id.prodMk continuous_const)).continuousOn
    · exact ((Q.toExtended.bellman v).continuous.comp
        ((continuous_const.mul continuous_id).prodMk continuous_const)).continuousOn
  · rw [interior_Icc]
    intro x hx
    obtain ⟨D, _, hD⟩ := key x hx
    exact hD.differentiableAt.differentiableWithinAt
  · rw [interior_Icc]
    intro x hx
    obtain ⟨D, hD0, hD⟩ := key x hx
    rw [hD.deriv]
    exact hD0

/-- **The monotone difference, in one economy.** If `t ≤ 1` and the continuations `v` and `w` have
increasing differences, then `a ↦ (T w)(a) - (T v)(t a)` is nondecreasing. The pivotal inequality
is supplied by `mul_marginal_le_of_scale`: relative risk aversion at most one and a concave,
increasing consumption function. -/
theorem monotoneOn_bellman_sub_scaled {assetCap : ℝ} (Q : IncomeFluctuation Z 0 assetCap)
    {t : ℝ} (ht0 : 0 < t) (ht1 : t ≤ 1) {v w : (ℝ × Z) →ᵇ ℝ} {z : Z} {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt Q.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hrra : MonotoneOn (fun y => y * du y) (Ioi (0 : ℝ)))
    (hdunn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ du y)
    (hwc : ConcaveSlices (0 : ℝ) assetCap w) (hid : Q.ContOfIncreasingDifferences v w)
    (hbv : ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      fun x => (Q.toExtended.bellman v) (x, z))
    (hbw : ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      fun x => (Q.toExtended.bellman w) (x, z))
    (hintv : ∀ x ∈ Icc (0 : ℝ) assetCap, Q.policyOf v (x, z) < Q.maxSaving (x, z))
    (hintw : ∀ x ∈ Icc (0 : ℝ) assetCap, Q.policyOf w (x, z) < Q.maxSaving (x, z))
    (hposv : ∀ x ∈ Icc (0 : ℝ) assetCap, 0 < Q.consumptionFnOf v z x)
    (hposw : ∀ x ∈ Icc (0 : ℝ) assetCap, 0 < Q.consumptionFnOf w z x)
    (hcw : ConcaveOn ℝ (Icc (0 : ℝ) assetCap) (Q.consumptionFnOf w z))
    (hmw : MonotoneOn (Q.consumptionFnOf w z) (Icc (0 : ℝ) assetCap)) :
    MonotoneOn (fun a => (Q.toExtended.bellman w) (a, z) - (Q.toExtended.bellman v) (t * a, z))
      (Icc (0 : ℝ) assetCap) := by
  refine Q.monotoneOn_bellman_sub_scaled_of_piv ht0 ht1 hderiv hanti hwc hid hbv hbw hintv hintw
    hposv hposw ?_
  intro a ha
  have hR : 0 < 1 + Q.interest := Q.interest_gt_neg_one
  simpa only [mul_div_cancel_right₀ _ hR.ne'] using
    mul_marginal_le_of_ratio hcw (hposw 0 ⟨le_rfl, Q.assetFloor_le_assetCap⟩)
      hmw hrra hdunn (mul_pos ht0 hR) (mul_le_of_le_one_left hR.le ht1) ha

/-! ### The step, across rates

Reading the difference back through the budget coincidence turns the previous theorem into the
statement Light's induction propagates: the Bellman images of two continuations with increasing
differences again have increasing differences, at the two rates. -/

omit [Fintype Z] [Nonempty Z] [DiscreteTopology Z] in
theorem incDiffSlices_refl (v : (ℝ × Z) →ᵇ ℝ) : IncDiffSlices (0 : ℝ) assetCap v v :=
  fun _ _ _ _ _ _ => le_rfl

/-- **Light (2018), step 5, from the pivotal inequality as a hypothesis.** -/
theorem incDiffSlices_bellman_withRate_of_piv (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    (hr : r₁ ≤ r₂) {v w : (ℝ × Z) →ᵇ ℝ} {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ)))
    (hvc : ConcaveSlices (0 : ℝ) assetCap v) (hwc : ConcaveSlices (0 : ℝ) assetCap w)
    (hposv : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      0 < (P.withRate r₂ h₂).consumptionFnOf v z a)
    (hposw : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      0 < (P.withRate r₂ h₂).consumptionFnOf w z a)
    (hslackv : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (P.withRate r₂ h₂).policyOf v (a, z) < assetCap)
    (hslackw : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (P.withRate r₂ h₂).policyOf w (a, z) < assetCap)
    (hpiv : ∀ z : Z, ∀ a ∈ Ioo (0 : ℝ) assetCap,
      (1 + r₁) * du ((P.withRate r₂ h₂).consumptionFnOf w z ((1 + r₁) / (1 + r₂) * a))
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFnOf w z a))
    (hid : IncDiffSlices (0 : ℝ) assetCap v w) :
    IncDiffSlices (0 : ℝ) assetCap ((P.withRate r₁ h₁).toExtended.bellman v)
      ((P.withRate r₂ h₂).toExtended.bellman w) := by
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  intro z x y hx hy hxy
  have hmono := (P.withRate r₂ h₂).monotoneOn_bellman_sub_scaled_of_piv
    (t := (1 + r₁) / (1 + r₂)) (div_pos hR₁ hR₂) (by rw [div_le_one hR₂]; linarith)
    (v := v) (w := w) (z := z) (du := du) hderiv hanti hwc
    ((P.withRate r₂ h₂).contOfIncreasingDifferences_of_slices hid)
    ((P.withRate r₂ h₂).concaveSlices_bellman hvc z)
    ((P.withRate r₂ h₂).concaveSlices_bellman hwc z)
    (fun a ha => (P.withRate r₂ h₂).policyOf_lt_maxSaving_of_pos (hposv a ha z)
      (hslackv a ha z))
    (fun a ha => (P.withRate r₂ h₂).policyOf_lt_maxSaving_of_pos (hposw a ha z)
      (hslackw a ha z))
    (fun a ha => hposv a ha z) (fun a ha => hposw a ha z)
    (fun a ha => by
      rw [IncomeFluctuation.withRate_interest,
        show (1 + r₁) / (1 + r₂) * (1 + r₂) = 1 + r₁ from div_mul_cancel₀ _ hR₂.ne']
      exact hpiv z a ha)
  have hkey := hmono hx hy hxy
  have hcoin : ∀ a ∈ Icc (0 : ℝ) assetCap,
      ((P.withRate r₁ h₁).toExtended.bellman v) (a, z)
        = ((P.withRate r₂ h₂).toExtended.bellman v) ((1 + r₁) / (1 + r₂) * a, z) := by
    intro a ha
    rw [(P.withRate r₁ h₁).toExtended.bellman_apply,
      (P.withRate r₂ h₂).toExtended.bellman_apply]
    exact P.bellmanFn_withRate h₁ h₂ hr v z ha
  rw [hcoin x hx, hcoin y hy]
  linarith

/-- **Light (2018) Theorem 1 from the pivotal inequality, the induction started anywhere.** -/
theorem contIncreasingDifferences_withRate_of_piv (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂)
    (hr : r₁ ≤ r₂) {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (v₀ : (ℝ × Z) →ᵇ ℝ)
    (hv₀ : ConcaveSlices (0 : ℝ) assetCap v₀)
    (hposv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, 0 <
      (P.withRate r₂ h₂).consumptionFnOf (((P.withRate r₁ h₁).toExtended.bellman)^[n] v₀) z a)
    (hposw : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, 0 <
      (P.withRate r₂ h₂).consumptionFnOf (((P.withRate r₂ h₂).toExtended.bellman)^[n] v₀) z a)
    (hslackv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₁ h₁).toExtended.bellman)^[n] v₀) (a, z) < assetCap)
    (hslackw : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₂ h₂).toExtended.bellman)^[n] v₀) (a, z) < assetCap)
    (hpiv : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Ioo (0 : ℝ) assetCap,
      (1 + r₁) * du ((P.withRate r₂ h₂).consumptionFnOf
          (((P.withRate r₂ h₂).toExtended.bellman)^[n] v₀) z ((1 + r₁) / (1 + r₂) * a))
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFnOf
          (((P.withRate r₂ h₂).toExtended.bellman)^[n] v₀) z a)) :
    ContIncreasingDifferences (P.withRate r₁ h₁) (P.withRate r₂ h₂) := by
  have hvs : ∀ n : ℕ, ConcaveSlices (0 : ℝ) assetCap
      (((P.withRate r₁ h₁).toExtended.bellman)^[n] v₀) :=
    (P.withRate r₁ h₁).concaveSlices_iterate_bellman hv₀
  have hws : ∀ n : ℕ, ConcaveSlices (0 : ℝ) assetCap
      (((P.withRate r₂ h₂).toExtended.bellman)^[n] v₀) :=
    (P.withRate r₂ h₂).concaveSlices_iterate_bellman hv₀
  have hstep : ∀ n : ℕ, IncDiffSlices (0 : ℝ) assetCap
      (((P.withRate r₁ h₁).toExtended.bellman)^[n] v₀)
      (((P.withRate r₂ h₂).toExtended.bellman)^[n] v₀) := by
    intro n
    induction n with
    | zero => exact incDiffSlices_refl v₀
    | succ k ih =>
      rw [Function.iterate_succ_apply', Function.iterate_succ_apply']
      exact P.incDiffSlices_bellman_withRate_of_piv h₁ h₂ hr hderiv hanti (hvs k) (hws k)
        (hposv k) (hposw k) (hslackv k) (hslackw k) (hpiv k) ih
  refine contIncreasingDifferences_of_valueFunction _ _ rfl ?_
  intro z x y hx hy hxy
  have hlim₁ : Tendsto (fun n => ((P.withRate r₁ h₁).toExtended.bellman)^[n] v₀) atTop
      (𝓝 (P.withRate r₁ h₁).toExtended.valueFunction) :=
    (P.withRate r₁ h₁).toExtended.tendsto_iterate_valueFunction v₀
  have hlim₂ : Tendsto (fun n => ((P.withRate r₂ h₂).toExtended.bellman)^[n] v₀) atTop
      (𝓝 (P.withRate r₂ h₂).toExtended.valueFunction) :=
    (P.withRate r₂ h₂).toExtended.tendsto_iterate_valueFunction v₀
  have hpt : ∀ (F : ℕ → (ℝ × Z) →ᵇ ℝ) (G : (ℝ × Z) →ᵇ ℝ), Tendsto F atTop (𝓝 G) →
      ∀ p : ℝ × Z, Tendsto (fun n => F n p) atTop (𝓝 (G p)) := fun F G hF p =>
    (BoundedContinuousFunction.tendsto_iff_tendstoUniformly.mp hF).tendsto_at p
  have hev₁ := hpt _ _ hlim₁
  have hev₂ := hpt _ _ hlim₂
  exact le_of_tendsto_of_tendsto ((hev₁ (y, z)).sub (hev₁ (x, z)))
    ((hev₂ (y, z)).sub (hev₂ (x, z))) (Eventually.of_forall fun n => hstep n z x y hx hy hxy)

/-- **Light (2018), step 5.** Increasing differences survive the Bellman operator. -/
theorem incDiffSlices_bellman_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    {v w : (ℝ × Z) →ᵇ ℝ} {du : ℝ → ℝ}
    (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hrra : MonotoneOn (fun y => y * du y) (Ioi (0 : ℝ)))
    (hdunn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ du y)
    (hvc : ConcaveSlices (0 : ℝ) assetCap v) (hwc : ConcaveSlices (0 : ℝ) assetCap w)
    (hposv : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      0 < (P.withRate r₂ h₂).consumptionFnOf v z a)
    (hposw : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      0 < (P.withRate r₂ h₂).consumptionFnOf w z a)
    (hslackv : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (P.withRate r₂ h₂).policyOf v (a, z) < assetCap)
    (hslackw : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (P.withRate r₂ h₂).policyOf w (a, z) < assetCap)
    (hcw : ∀ z : Z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap) ((P.withRate r₂ h₂).consumptionFnOf w z))
    (hid : IncDiffSlices (0 : ℝ) assetCap v w) :
    IncDiffSlices (0 : ℝ) assetCap ((P.withRate r₁ h₁).toExtended.bellman v)
      ((P.withRate r₂ h₂).toExtended.bellman w) := by
  refine P.incDiffSlices_bellman_withRate_of_piv h₁ h₂ hr hderiv hanti hvc hwc
    hposv hposw hslackv hslackw ?_ hid
  intro z a ha
  exact mul_marginal_le_of_ratio (hcw z)
    (hposw 0 ⟨le_rfl, P.assetFloor_le_assetCap⟩ z)
    (fun x hx y hy hxy => (P.withRate r₂ h₂).consumptionFnOf_mono hwc hx hy hxy)
    hrra hdunn h₁.1 (add_le_add le_rfl hr) ha

/-! ### The induction, and the limit

`IncDiffSlices` mentions no economy and is closed under pointwise limits, so the step iterates
from the common start `0` and passes to the two value functions. That discharges the hypothesis
`hid` of `policy_mono_interest`, and with it Light's Theorem 1. -/

/-- **Light (2018) Theorem 1, with step 5 discharged.** The value functions at two rates have
increasing differences in assets, so the continuations do. -/
theorem contIncreasingDifferences_withRate (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hrra : MonotoneOn (fun y => y * du y) (Ioi (0 : ℝ)))
    (hdunn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ du y)
    (hposv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, 0 <
      (P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hposw : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, 0 <
      (P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hslackv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (hslackw : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (hcons : ∀ n : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      ((P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z)) :
    ContIncreasingDifferences (P.withRate r₁ h₁) (P.withRate r₂ h₂) := by
  refine P.contIncreasingDifferences_withRate_of_piv h₁ h₂ hr hderiv hanti 0
    concaveSlices_zero hposv hposw hslackv hslackw ?_
  intro n z a ha
  exact mul_marginal_le_of_ratio (hcons n z)
    (hposw n 0 ⟨le_rfl, P.assetFloor_le_assetCap⟩ z)
    (fun x hx y hy hxy => (P.withRate r₂ h₂).consumptionFnOf_mono
      ((P.withRate r₂ h₂).concaveSlices_iterate_bellman concaveSlices_zero n) hx hy hxy)
    hrra hdunn h₁.1 (add_le_add le_rfl hr) ha

/-- **Light (2018) Theorem 1, unconditional on the increasing-differences hypothesis.** A
household facing a higher interest rate saves at least as much, at every asset level and every
income state. -/
theorem policy_mono_withRate' (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hrra : MonotoneOn (fun y => y * du y) (Ioi (0 : ℝ)))
    (hdunn : ∀ y ∈ Ioi (0 : ℝ), 0 ≤ du y)
    (hposv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, 0 <
      (P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hposw : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, 0 <
      (P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hslackv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (hslackw : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (hcons : ∀ n : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      ((P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.withRate r₁ h₁).policy (a, z) ≤ (P.withRate r₂ h₂).policy (a, z) :=
  P.policy_mono_withRate h₁ h₂ hr
    (P.contIncreasingDifferences_withRate h₁ h₂ hr hderiv hanti hrra hdunn hposv hposw hslackv
      hslackw hcons) ha z

/-! ### CRRA, with the marginal-utility hypotheses discharged

For `u = crraUtility γ` marginal utility is `c ^ (-γ)`, which is decreasing and non-negative for
every `γ > 0`, and `c · u'(c) = c ^ (1 - γ)` is nondecreasing exactly when `γ ≤ 1` — relative
risk aversion at most one, the hypothesis Light needs and the one this development has carried
since `RelativeRiskAversion`. -/

theorem policy_mono_withRate_crra {γ : ℝ} (hγ0 : 0 < γ) (hγ1 : γ ≤ 1) (hu : P.u = crraUtility γ)
    (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hposv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, 0 <
      (P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hposw : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, 0 <
      (P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a)
    (hslackv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₁ h₁).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (hslackw : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (hcons : ∀ n : ℕ, ∀ z : Z, ConcaveOn ℝ (Icc (0 : ℝ) assetCap)
      ((P.withRate r₂ h₂).consumptionFnOf
        (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.withRate r₁ h₁).policy (a, z) ≤ (P.withRate r₂ h₂).policy (a, z) := by
  have hpow : ∀ c : ℝ, 0 < c → c * c ^ (-γ) = c ^ (1 - γ) := by
    intro c hc
    rw [show (1 : ℝ) - γ = 1 + -γ by ring, Real.rpow_add hc, Real.rpow_one]
  refine P.policy_mono_withRate' h₁ h₂ hr (du := fun c => c ^ (-γ)) ?_ ?_ ?_ ?_
    hposv hposw hslackv hslackw hcons ha z
  · intro c hc
    rw [hu]
    exact hasDerivAt_crraUtility γ hc
  · intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos hx hxy (by linarith)
  · intro x hx y hy hxy
    simp only []
    rw [hpow x hx, hpow y hy]
    exact Real.rpow_le_rpow hx.le hxy (by linarith)
  · intro y hy
    exact Real.rpow_nonneg hy.le _

/-! ### Beyond relative risk aversion one

The relative-risk-aversion specializations use `γ ≤ 1` in one place: the pivotal inequality
`t R u'(c_w(t a)) ≤ R u'(c_w(a))` applied to economy two's consumption function against the
CURRENT continuation `w`. Two changes make that inequality a hypothesis one can hope to meet
when `γ > 1`.

First, run the induction from economy two's own value function rather than from `0`. The
economy-two iterates are then constant — `T₂ V₂ = V₂` — so the pivotal inequality is asked of
economy two's TRUE consumption function alone, not of every iterate (whose consumption functions
start at "eat everything", where no such inequality holds).

Second, `mul_rpow_neg_le_of_scale` gives the inequality for `u' = c^{-γ}`, any `γ`, wherever
`(1 - c₂(0)/c₂(t a))(ρ - 1) ≤ ρ^{1/γ} - 1` with `ρ = R₂/R₁` — a condition on the range of the
consumption function, roughly `c₂(a) ≤ (γ/(γ-1)) c₂(0)` for rates close together. It is a
restriction on wealth, not on preferences: for a small enough asset cap, or on an invariant
interval, Light's Theorem 1 holds for every `γ`. -/

/-- **Light (2018) Theorem 1 from the pivotal inequality on economy two's OWN consumption
function.** The induction is started at economy two's value function, which its Bellman
operator fixes, so the only consumption function the inequality is asked of is the true one at
the higher rate. -/
theorem policy_mono_withRate_of_piv (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ)))
    (hposv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, 0 <
      (P.withRate r₂ h₂).consumptionFnOf (((P.withRate r₁ h₁).toExtended.bellman)^[n]
        (P.withRate r₂ h₂).toExtended.valueFunction) z a)
    (hslackv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₁ h₁).toExtended.bellman)^[n] (P.withRate r₂ h₂).toExtended.valueFunction)
        (a, z) < assetCap)
    (hposw : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, 0 < (P.withRate r₂ h₂).consumptionFn z a)
    (hslackw : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policy (a, z) < assetCap)
    (hpiv : ∀ z : Z, ∀ a ∈ Ioo (0 : ℝ) assetCap,
      (1 + r₁) * du ((P.withRate r₂ h₂).consumptionFn z ((1 + r₁) / (1 + r₂) * a))
        ≤ (1 + r₂) * du ((P.withRate r₂ h₂).consumptionFn z a))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.withRate r₁ h₁).policy (a, z) ≤ (P.withRate r₂ h₂).policy (a, z) := by
  have hfix : ∀ n : ℕ, ((P.withRate r₂ h₂).toExtended.bellman)^[n]
      (P.withRate r₂ h₂).toExtended.valueFunction = (P.withRate r₂ h₂).toExtended.valueFunction :=
    fun n => Function.iterate_fixed (P.withRate r₂ h₂).toExtended.bellman_valueFunction n
  refine P.policy_mono_withRate h₁ h₂ hr ?_ ha z
  refine P.contIncreasingDifferences_withRate_of_piv h₁ h₂ hr hderiv hanti
    (P.withRate r₂ h₂).toExtended.valueFunction (P.withRate r₂ h₂).concaveSlices_valueFunction
    hposv (fun n a ha' z' => by rw [hfix n]; exact hposw a ha' z') hslackv
    (fun n a ha' z' => by rw [hfix n]; exact hslackw a ha' z')
    (fun n z' a ha' => by rw [hfix n]; exact hpiv z' a ha')

/-- **Light (2018) Theorem 1 for CRRA with ANY `γ > 0`, on a range condition.** Saving rises with
the rate at every state provided economy two's consumption function satisfies
`(1 - c₂(0,z)/c₂(t a, z)) (ρ - 1) ≤ ρ^{1/γ} - 1` for `ρ = R₂/R₁`, `t = 1/ρ`, at every interior
`a` — for rates close together, consumption at most about `γ/(γ-1)` times its value at zero
assets. Concavity of that consumption function is Carroll--Kimball at the fixed point
(`concaveOn_consumptionFn_of_crra`). -/
theorem policy_mono_withRate_crra_of_range {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβ : 0 < (P.discount : ℝ)) (h₁ : P.RateOK r₁) (h₂ : P.RateOK r₂) (hr : r₁ ≤ r₂)
    (hpc₂ : (P.withRate r₂ h₂).PositiveConsumptionAll)
    (hslackIt : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₂ h₂).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (a, z) < assetCap)
    (hslackv : ∀ n : ℕ, ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policyOf
      (((P.withRate r₁ h₁).toExtended.bellman)^[n] (P.withRate r₂ h₂).toExtended.valueFunction)
        (a, z) < assetCap)
    (hslackw : ∀ a ∈ Icc (0 : ℝ) assetCap, ∀ z : Z, (P.withRate r₂ h₂).policy (a, z) < assetCap)
    (hrange : ∀ z : Z, ∀ a ∈ Ioo (0 : ℝ) assetCap,
      (1 - (P.withRate r₂ h₂).consumptionFn z 0
          / (P.withRate r₂ h₂).consumptionFn z ((1 + r₁) / (1 + r₂) * a))
        * ((1 + r₂) / (1 + r₁) - 1) ≤ ((1 + r₂) / (1 + r₁)) ^ (1 / γ) - 1)
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z) :
    (P.withRate r₁ h₁).policy (a, z) ≤ (P.withRate r₂ h₂).policy (a, z) := by
  have hR₁ : (0 : ℝ) < 1 + r₁ := h₁.1
  have hR₂ : (0 : ℝ) < 1 + r₂ := h₂.1
  have hcap : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hzero : (0 : ℝ) ∈ Icc (0 : ℝ) assetCap := ⟨le_rfl, hcap⟩
  have hconc : ∀ n : ℕ, ConcaveSlices (0 : ℝ) assetCap
      (((P.withRate r₁ h₁).toExtended.bellman)^[n]
        (P.withRate r₂ h₂).toExtended.valueFunction) := by
    intro n
    induction n with
    | zero => exact (P.withRate r₂ h₂).concaveSlices_valueFunction
    | succ k ih =>
      rw [Function.iterate_succ_apply']
      exact (P.withRate r₁ h₁).concaveSlices_bellman ih
  refine P.policy_mono_withRate_of_piv h₁ h₂ hr (du := fun c => c ^ (-γ))
    (fun c hc => by rw [hu]; exact hasDerivAt_crraUtility γ hc)
    (fun x hx y _ hxy => Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
    (fun n a' ha' z' => hpc₂ _ (hconc n) z' a' ha') hslackv
    (fun a' ha' z' => hpc₂ _ (P.withRate r₂ h₂).concaveSlices_valueFunction z' a' ha')
    hslackw ?_ ha z
  intro z' a' ha'
  have hcc : ConcaveOn ℝ (Icc (0 : ℝ) assetCap) ((P.withRate r₂ h₂).consumptionFn z') :=
    (P.withRate r₂ h₂).concaveOn_consumptionFn_of_crra hpc₂ hγ0 hβ hu hslackIt z'
  have hmono : MonotoneOn ((P.withRate r₂ h₂).consumptionFn z') (Icc (0 : ℝ) assetCap) :=
    fun x hx y hy hxy => (P.withRate r₂ h₂).consumptionFn_mono hx hy hxy
  have hc0 : 0 < (P.withRate r₂ h₂).consumptionFn z' 0 :=
    hpc₂ _ (P.withRate r₂ h₂).concaveSlices_valueFunction z' 0 hzero
  have hta : (1 + r₁) / (1 + r₂) * a' ∈ Icc (0 : ℝ) assetCap := by
    have ht1 : (1 + r₁) / (1 + r₂) ≤ 1 := by rw [div_le_one hR₂]; linarith
    have ht0 : 0 < (1 + r₁) / (1 + r₂) := div_pos hR₁ hR₂
    constructor
    · exact mul_nonneg ht0.le ha'.1.le
    · nlinarith [ha'.2]
  have e1 : (1 + r₁) * (a' / (1 + r₂)) = (1 + r₁) / (1 + r₂) * a' := by field_simp
  have e2 : (1 + r₂) / (1 + r₁) * (1 + r₁) * (a' / (1 + r₂)) = a' := by field_simp
  have e3 : (1 + r₂) / (1 + r₁) * (1 + r₁) = 1 + r₂ := div_mul_cancel₀ _ hR₁.ne'
  have hpiv := mul_rpow_neg_le_of_scale hγ0 hcc hzero hc0 hmono (α₁ := 1 + r₁)
    (ρ := (1 + r₂) / (1 + r₁)) (x := a' / (1 + r₂)) hR₁ (by rw [le_div_iff₀ hR₁]; linarith)
    (div_pos ha'.1 hR₂) (by rw [e1]; exact hta) (by rw [e2]; exact ⟨ha'.1.le, ha'.2.le⟩)
    (by rw [e1]; exact hrange z' a' ha')
  rw [e1, e2, e3] at hpiv
  exact hpiv

end IncomeFluctuation

end LeanEconomics
