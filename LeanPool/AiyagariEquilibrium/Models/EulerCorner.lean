/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.ImpatientDecline


/-!
# The corner condition from the Euler inequality

`policy_eq_zero_of_corner_at` gets the corner from a LIPSCHITZ bound on the value function,
`β L < m`. The constant `L` is `slopeBound / (1 - βR)`, and at Aiyagari's `β = 0.96` that is
several hundred times the true slope, so the test fails by orders of magnitude. This file gets the
corner from the Euler inequality instead, and the only thing it asks is `βR < 1`.

## The argument

Two steps, both at the fixed point.

**Nobody at the borrowing limit consumes less than the worst income.** Take the income state at
which consumption at the limit is smallest. If that household were saving, its Euler inequality
(`euler_ge`) would read `u'(c) ≤ βR E[u'(c')]`; but tomorrow's consumption is at least today's
minimum (consumption rises with assets, and assets can only have risen), so `u'(c') ≤ u'(c)` and
`u'(c) ≤ βR u'(c)`, impossible with `βR < 1`. So the household at the minimum is at the corner,
consumes its whole income, and the minimum is at least `minIncome`.

**The corner, state by state.** At any state where `βR · u'(minIncome) < u'(cash on hand)`,
saving is not optimal: if it were, the Euler inequality and step one would give
`u'(cash on hand) ≤ u'(c) ≤ βR u'(minIncome)`. This is the contrapositive of `euler_ge`.

For log utility the test at the worst income state is `a < minIncome (1 - βR) / (βR²)`: a small
but positive corner region, at every `β < 1/R`. Compare Clarida (1987), who has the corner on
`[ε - rφ, w_bar]` under `u'(0) < ∞`; here nothing is assumed about `u'(0)`.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- **At the borrowing limit, nobody consumes less than the worst income.** The household at the
minimum is at the corner — otherwise its own Euler inequality would push it up by `1/βR`. -/
theorem minIncome_le_consumptionFn_floor
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpos : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, 0 < P.consumptionFn z x)
    (hslack : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, P.policy (x, z) < P.maxSaving (x, z))
    (z : Z) : P.minIncome + P.interest * assetFloor ≤ P.consumptionFn z assetFloor := by
  have hfl : assetFloor ∈ Icc assetFloor assetCap := ⟨le_rfl, P.assetFloor_le_assetCap⟩
  -- the state at which consumption at the limit is smallest
  obtain ⟨z₀, -, hz₀⟩ := Finset.exists_min_image Finset.univ
    (fun z' => P.consumptionFn z' assetFloor) Finset.univ_nonempty
  have hmin : ∀ z', P.consumptionFn z₀ assetFloor ≤ P.consumptionFn z' assetFloor :=
    fun z' => hz₀ z' (Finset.mem_univ _)
  -- it is at the corner
  have hcorner : P.policy (assetFloor, z₀) = assetFloor := by
    by_contra hne
    set A : ℝ := P.policy (assetFloor, z₀) with hA
    have hAmem : A ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policy_mem _)
    have hA0 : assetFloor < A := lt_of_le_of_ne hAmem.1 (Ne.symm hne)
    have hbv := P.toExtended.bellman_valueFunction
    have hc : 0 < P.consumptionFn z₀ assetFloor := hpos z₀ _ hfl
    have hE := P.euler_ge (v := P.toExtended.valueFunction) (z := z₀) (a := assetFloor) (A := A)
      (du := du (P.consumptionFn z₀ assetFloor)) (du' := fun z' => du (P.consumptionFn z' A))
      hfl (by rw [hbv, hA]; exact congrFun P.policyOf_valueFunction (assetFloor, z₀)) hA0
      (fun z' => hslack z' A hAmem) (by rw [hbv]; exact hc)
      (by rw [hbv]; exact hderiv _ hc) (fun z' => hpos z' A hAmem)
      (fun z' => hderiv _ (hpos z' A hAmem))
    -- tomorrow's consumption is at least today's minimum, so marginal utility is at most today's
    have hbound : ∀ z', du (P.consumptionFn z' A) ≤ du (P.consumptionFn z₀ assetFloor) :=
      fun z' => hanti (mem_Ioi.mpr hc) (mem_Ioi.mpr (hpos z' A hAmem))
        (le_trans (hmin z') (P.consumptionFn_mono hfl hAmem hAmem.1))
    have hsum : ∑ z' : Z, P.transitionMatrix z₀ z' * du (P.consumptionFn z' A)
        ≤ du (P.consumptionFn z₀ assetFloor) := by
      refine le_trans (Finset.sum_le_sum fun z' _ =>
        mul_le_mul_of_nonneg_left (hbound z') (P.transitionMatrix_nonneg z₀ z')) ?_
      rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]
    have hdu : 0 < du (P.consumptionFn z₀ assetFloor) := hdupos _ hc
    have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
    have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
    have hcoef : (0 : ℝ) ≤ (P.discount : ℝ) * (1 + P.interest) := mul_nonneg hβ hR.le
    have h2 := mul_le_mul_of_nonneg_left hsum hcoef
    nlinarith [hE, h2, hdu, hβR]
  -- so it consumes its whole income
  have hres : P.resources (assetFloor, z₀) = P.income z₀ + (1 + P.interest) * assetFloor := by
    simp only [resources, max_self]
  have hc₀ : P.consumptionFn z₀ assetFloor = P.income z₀ + P.interest * assetFloor := by
    simp only [consumptionFn, consumption, hcorner, hres]; ring
  have := P.minIncome_le z₀
  linarith [hmin z, hc₀]

/-- **The corner from the Euler inequality.** Wherever `βR · u'(minIncome + r·floor)` is below the
marginal utility of cash on hand, the household saves nothing. The contrapositive of `euler_ge`,
with `minIncome_le_consumptionFn_floor` bounding tomorrow's marginal utility.

Nothing here depends on how large `β` is beyond `βR < 1`; that is what makes it usable at
`β = 0.96`, where the Lipschitz corner `policy_eq_zero_of_corner_at` is hopeless. -/
theorem policy_eq_floor_of_euler
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpos : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, 0 < P.consumptionFn z x)
    (hslack : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, P.policy (x, z) < P.maxSaving (x, z))
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (z : Z)
    (hcond : (P.discount : ℝ) * (1 + P.interest) * du (P.minIncome + P.interest * assetFloor)
      < du (P.resources (a, z) - assetFloor)) :
    P.policy (a, z) = assetFloor := by
  by_contra hne
  set A : ℝ := P.policy (a, z) with hA
  have hAmem : A ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policy_mem _)
  have hA0 : assetFloor < A := lt_of_le_of_ne hAmem.1 (Ne.symm hne)
  have hbv := P.toExtended.bellman_valueFunction
  have hc : 0 < P.consumptionFn z a := hpos z a ha
  have hE := P.euler_ge (v := P.toExtended.valueFunction) (z := z) (a := a) (A := A)
    (du := du (P.consumptionFn z a)) (du' := fun z' => du (P.consumptionFn z' A))
    ha (by rw [hbv, hA]; exact congrFun P.policyOf_valueFunction (a, z)) hA0
    (fun z' => hslack z' A hAmem) (by rw [hbv]; exact hc)
    (by rw [hbv]; exact hderiv _ hc) (fun z' => hpos z' A hAmem)
    (fun z' => hderiv _ (hpos z' A hAmem))
  -- the worst income bounds tomorrow's marginal utility
  have hy : 0 < P.minIncome + P.interest * assetFloor := by
    have h1 := P.minConsumption_le_floor
    have h2 := P.minConsumption_pos
    linarith
  have hfl : assetFloor ∈ Icc assetFloor assetCap := ⟨le_rfl, P.assetFloor_le_assetCap⟩
  have hbound : ∀ z', du (P.consumptionFn z' A) ≤ du (P.minIncome + P.interest * assetFloor) :=
    fun z' => hanti (mem_Ioi.mpr hy) (mem_Ioi.mpr (hpos z' A hAmem))
      (le_trans (P.minIncome_le_consumptionFn_floor hβR hderiv hanti hdupos hpos hslack z')
        (P.consumptionFn_mono hfl hAmem hAmem.1))
  have hsum : ∑ z' : Z, P.transitionMatrix z z' * du (P.consumptionFn z' A)
      ≤ du (P.minIncome + P.interest * assetFloor) := by
    refine le_trans (Finset.sum_le_sum fun z' _ =>
      mul_le_mul_of_nonneg_left (hbound z') (P.transitionMatrix_nonneg z z')) ?_
    rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]
  -- and cash on hand bounds today's from below
  have hcle : P.consumptionFn z a ≤ P.resources (a, z) - assetFloor := by
    simp only [consumptionFn, consumption]; linarith [hAmem.1]
  have hres0 : 0 < P.resources (a, z) - assetFloor := lt_of_lt_of_le hc hcle
  have htoday : du (P.resources (a, z) - assetFloor) ≤ du (P.consumptionFn z a) :=
    hanti (mem_Ioi.mpr hc) (mem_Ioi.mpr hres0) hcle
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hcoef : (0 : ℝ) ≤ (P.discount : ℝ) * (1 + P.interest) := mul_nonneg hβ hR.le
  have h2 := mul_le_mul_of_nonneg_left hsum hcoef
  linarith [hE, h2, htoday, hcond]

/-! ### CRRA and log -/

/-- **The Euler corner for CRRA**, `u' c = c ^ (-γ)`, at a zero borrowing limit. The test at
state `z` is `βR · minIncome^(-γ) < resources^(-γ)`, i.e.
`resources (a, z) < minIncome · (βR)^(-1/γ)`. -/
theorem crra_policy_eq_zero_of_euler {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hfl : assetFloor = 0) (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    (hpos : ∀ (z : Z), ∀ x ∈ Icc (0 : ℝ) assetCap, 0 < P.consumptionFn z x)
    (hslack : ∀ (z : Z), ∀ x ∈ Icc (0 : ℝ) assetCap, P.policy (x, z) < P.maxSaving (x, z))
    {a : ℝ} (ha : a ∈ Icc (0 : ℝ) assetCap) (z : Z)
    (hcond : (P.discount : ℝ) * (1 + P.interest) * P.minIncome ^ (-γ)
      < P.resources (a, z) ^ (-γ)) :
    P.policy (a, z) = 0 := by
  subst hfl
  refine P.policy_eq_floor_of_euler hβR (du := fun c => c ^ (-γ))
    (fun c hc => by rw [hu]; exact hasDerivAt_crraUtility γ hc)
    (fun _ hx _ _ hxy => Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
    (fun c hc => Real.rpow_pos_of_pos hc _) hpos hslack ha z ?_
  simpa using hcond

end IncomeFluctuation

end LeanEconomics
