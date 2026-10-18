/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.IncomeFluctuationIterate
public import LeanPool.AiyagariEquilibrium.Distribution.Uniqueness


/-!
# Açıkgöz (2018) Proposition 4: the natural asset bound from impatience alone

`NaturalAssetBound` gets assets to decline from a LINEAR lower bound on consumption, which it
can supply only for log utility, and with the very lossy constant `exp (-2 β ‖V‖)`. Its own
docstring says what the sharp argument would need: "Getting it needs the Euler equation, hence
the envelope condition, hence the machinery that `IncomeFluctuationEnvelope` supplies only under
side conditions." That machinery now exists (`hasDerivAt_bellman`, `euler_ge`), and with it the
decline condition is not a calibration at all — it is exactly impatience.

## The argument, in one line

Let `z` be the income state at which consumption is LOWEST, and suppose the household does not
decumulate there: `A = g(a, z) ≥ a`. The Euler inequality from saving less is

  `u'(c(a, z)) ≤ β R · Σ_{z'} π_{z z'} u'(c(A, z'))`.

Consumption rises with assets and `A ≥ a`, so `c(A, z') ≥ c(a, z') ≥ c(a, z)`, and marginal
utility falls, so every term on the right is at most `u'(c(a, z))`. The weights sum to one.
Hence `u'(c(a,z)) ≤ β R · u'(c(a,z))`, and since marginal utility is positive, `1 ≤ β R`.

So `β R < 1` forces decline. No limits, no asymptotic marginal propensity to consume, no
calibration — and nothing is asked of the utility beyond a positive, decreasing derivative.

## What it costs

Only the Euler inequality's own side conditions: consumption positive at every optimum and the
saving strictly below its cap (`hslack`), which is `policyOf_lt_maxSaving` once the asset cap is
slack. Note the direction — `euler_ge` comes from the deviation "save LESS", so it needs room
BELOW, which is exactly what `A ≥ a > assetFloor` provides.
-/

@[expose] public section

open Set Filter Topology BoundedContinuousFunction

namespace LeanEconomics

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetFloor assetCap : ℝ} (P : IncomeFluctuation Z assetFloor assetCap)

/-- **Impatience forces decumulation at a state where consumption is lowest.** -/
theorem policy_lt_self_of_impatient
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpos : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, 0 < P.consumptionFn z x)
    (hslack : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, P.policy (x, z) < P.maxSaving (x, z))
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (ha0 : assetFloor < a) {z : Z}
    (hmin : ∀ z' : Z, P.consumptionFn z a ≤ P.consumptionFn z' a) :
    P.policy (a, z) < a := by
  by_contra hcon
  rw [not_lt] at hcon
  set A : ℝ := P.policy (a, z) with hA
  have hAmem : A ∈ Icc assetFloor assetCap := P.feasible_subset_region (P.policy_mem _)
  have hA0 : assetFloor < A := lt_of_lt_of_le ha0 hcon
  have hbv := P.toExtended.bellman_valueFunction
  have hc : 0 < P.consumptionFn z a := hpos z a ha
  -- the Euler inequality from saving less
  have hE := P.euler_ge (v := P.toExtended.valueFunction) (z := z) (a := a) (A := A)
    (du := du (P.consumptionFn z a)) (du' := fun z' => du (P.consumptionFn z' A))
    ha (by rw [hbv, hA]; exact congrFun P.policyOf_valueFunction (a, z)) hA0
    (fun z' => hslack z' A hAmem) (by rw [hbv]; exact hc)
    (by rw [hbv]; exact hderiv _ hc) (fun z' => hpos z' A hAmem)
    (fun z' => hderiv _ (hpos z' A hAmem))
  -- every next-period marginal utility is at most today's
  have hbound : ∀ z' : Z, du (P.consumptionFn z' A) ≤ du (P.consumptionFn z a) := fun z' =>
    hanti (mem_Ioi.mpr hc) (mem_Ioi.mpr (hpos z' A hAmem))
      (le_trans (hmin z') (P.consumptionFn_mono ha hAmem hcon))
  have hsum : ∑ z' : Z, P.transitionMatrix z z' * du (P.consumptionFn z' A)
      ≤ du (P.consumptionFn z a) := by
    refine le_trans (Finset.sum_le_sum fun z' _ =>
      mul_le_mul_of_nonneg_left (hbound z') (P.transitionMatrix_nonneg z z')) ?_
    rw [← Finset.sum_mul, P.transitionMatrix_sum, one_mul]
  have hdu : 0 < du (P.consumptionFn z a) := hdupos _ hc
  have hβ : (0 : ℝ) ≤ (P.discount : ℝ) := P.discount.coe_nonneg
  have hR : (0 : ℝ) < 1 + P.interest := P.interest_gt_neg_one
  have hcoef : (0 : ℝ) ≤ (P.discount : ℝ) * (1 + P.interest) := mul_nonneg hβ hR.le
  have h2 : ((P.discount : ℝ) * (1 + P.interest))
      * (∑ z' : Z, P.transitionMatrix z z' * du (P.consumptionFn z' A))
      ≤ ((P.discount : ℝ) * (1 + P.interest)) * du (P.consumptionFn z a) :=
    mul_le_mul_of_nonneg_left hsum hcoef
  nlinarith [hE, h2, hdu, hβR]

/-! ### Which income state consumes least

The Euler argument above runs at the state where consumption is lowest, and the Doeblin
construction wants a FIXED state to repeat. The two agree when income is iid: the continuation
is then the same function of saving whatever today's state, so the problem depends on the state
only through cash on hand, and `consumptionFn_mono` generalises from two asset levels at one
income state to two states with ordered resources. -/

/-- **Consumption rises with resources**, across income states as well as asset levels, whenever
the two states share a continuation. This is `consumptionFn_mono` with the state allowed to
move: its proof never used `z` for anything but `cont z`. -/
theorem consumptionFn_mono_of_cont_eq {a a' : ℝ} {z₁ z₂ : Z} (hcont : P.cont z₁ = P.cont z₂)
    (ha : a ∈ Icc assetFloor assetCap) (ha' : a' ∈ Icc assetFloor assetCap)
    (hres : P.resources (a, z₁) ≤ P.resources (a', z₂)) :
    P.consumptionFn z₁ a ≤ P.consumptionFn z₂ a' := by
  set Δ : ℝ := P.resources (a', z₂) - P.resources (a, z₁) with hΔdef
  have hΔ : 0 ≤ Δ := by rw [hΔdef]; linarith
  set b : ℝ := P.policy (a, z₁) with hbdef
  set b' : ℝ := P.policy (a', z₂) with hb'def
  by_contra hcon
  rw [not_le] at hcon
  have hgap : b + Δ < b' := by
    simp only [consumptionFn, consumption] at hcon
    rw [hΔdef]; linarith
  have hbmem : b ∈ P.toExtended.feasible (a, z₁) := P.policy_mem _
  have hb'mem : b' ∈ P.toExtended.feasible (a', z₂) := P.policy_mem _
  rw [P.feasible_eq] at hbmem hb'mem
  -- the saving cap cannot grow by more than resources do, across states as within one
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
  have hc1 : P.consumption (a, z₁) b ∈ P.dom := P.consumption_policy_mem_dom (s := (a, z₁)) ha
  have hc2 : P.consumption (a', z₂) b' ∈ P.dom := P.consumption_policy_mem_dom (s := (a', z₂)) ha'
  have he1 : P.consumption (a', z₂) (b + Δ) = P.consumption (a, z₁) b := by
    simp only [consumption, hΔdef]; ring
  have he2 : P.consumption (a, z₁) (b' - Δ) = P.consumption (a', z₂) b' := by
    simp only [consumption, hΔdef]; ring
  have hI := P.objR_le_of_mem ha hshiftdown (by rw [he2]; exact hc2)
  have hII := P.objR_le_of_mem ha' hshiftup (by rw [he1]; exact hc1)
  have hbreg : b ∈ Icc assetFloor assetCap := P.policy_mem_region _
  have hb'reg : b' ∈ Icc assetFloor assetCap := P.policy_mem_region _
  have hshift := (P.concaveOn_cont z₁).sub_le_sub_of_shift (c₁ := b) (c₂ := b' - Δ) (Δ := Δ)
    hbreg (by simpa using hb'reg) (by linarith) hΔ
  rw [sub_add_cancel] at hshift
  have hβ : (0 : ℝ) ≤ P.discount := P.discount.coe_nonneg
  have hscaled := mul_le_mul_of_nonneg_left hshift hβ
  simp only [objR, he1, he2, ← hcont] at hI hII
  have hIIeq : P.objR (a', z₂) (b + Δ) = P.objR (a', z₂) b' := by
    simp only [objR, he1, ← hcont]
    nlinarith [hI, hII, hscaled]
  have hbell : P.toExtended.objectiveE P.toExtended.valueFunction (a', z₂) (b + Δ)
      = ((P.toExtended.bellmanFn P.toExtended.valueFunction (a', z₂) : ℝ) : EReal) := by
    rw [P.objectiveE_eq_coe ha' hshiftup (by rw [he1]; exact hc1), hIIeq,
      ← P.objectiveE_eq_coe ha' (P.policy_mem _) hc2]
    exact P.policy_optimal _
  exact absurd (P.eq_policy_of_optimal ha' hshiftup hbell) (by rw [← hb'def]; linarith)

/-- Income is iid: the transition probabilities do not depend on today's state. -/
def IidIncome : Prop := ∀ z₁ z₂ z' : Z, P.transitionMatrix z₁ z' = P.transitionMatrix z₂ z'

theorem cont_eq_of_iid (hiid : P.IidIncome) (z₁ z₂ : Z) : P.cont z₁ = P.cont z₂ := by
  funext x
  exact Finset.sum_congr rfl fun z' _ => by rw [hiid z₁ z₂ z']

/-- **Consumption is lowest where income is lowest**, for an iid income process. -/
theorem consumptionFn_le_of_income_le (hiid : P.IidIncome) {z₁ z₂ : Z}
    (hinc : P.income z₁ ≤ P.income z₂) {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) :
    P.consumptionFn z₁ a ≤ P.consumptionFn z₂ a :=
  P.consumptionFn_mono_of_cont_eq (P.cont_eq_of_iid hiid z₁ z₂) ha ha
    (by simp only [resources]; linarith)

/-! ### The decline condition, from impatience

Putting the two together: with iid income the lowest-income state is the lowest-consumption
state, so the Euler argument runs there, and assets decline at it from EVERY asset level above
the borrowing constraint. That is the hypothesis `hdecl` of `exists_exhaust_of_decline`, which
every witness has been discharging by a numerical calibration. It is impatience.

What is NOT replaced is the corner condition `hzero`: decline alone gives a strictly falling
sequence, and the Doeblin argument needs an ATOM — the constraint has to be reached exactly, not
approached. That is a statement about the bottom of the state space, where the Euler equation
does not hold, and it stays a calibration. -/

/-- **Açıkgöz (2018) Proposition 4.** With iid income and `β(1+r) < 1`, assets strictly decline
at the lowest income state, at every asset level above the borrowing constraint. -/
theorem policy_lt_self_of_impatient_iid
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) (hiid : P.IidIncome)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpos : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, 0 < P.consumptionFn z x)
    (hslack : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, P.policy (x, z) < P.maxSaving (x, z))
    {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    {a : ℝ} (ha : a ∈ Icc assetFloor assetCap) (ha0 : assetFloor < a) :
    P.policy (a, z₀) < a :=
  P.policy_lt_self_of_impatient hβR hderiv hanti hdupos hpos hslack ha ha0
    (fun z' => P.consumptionFn_le_of_income_le hiid (hz₀ z') ha)

/-- **The Doeblin exhaustion data, with the decline half free.** Only the corner condition is
left as a calibration. -/
theorem exists_exhaust_of_impatient
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) (hiid : P.IidIncome)
    {du : ℝ → ℝ} (hderiv : ∀ c : ℝ, 0 < c → HasDerivAt P.u (du c) c)
    (hanti : AntitoneOn du (Ioi (0 : ℝ))) (hdupos : ∀ c : ℝ, 0 < c → 0 < du c)
    (hpos : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, 0 < P.consumptionFn z x)
    (hslack : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, P.policy (x, z) < P.maxSaving (x, z))
    {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    {a₀ : ℝ} (ha₀ : assetFloor < a₀) (hle : a₀ ≤ assetCap)
    (hzero : ∀ a ∈ Icc assetFloor a₀, P.policy (a, z₀) = assetFloor) :
    ∃ N : ℕ, (P.gBad z₀)^[N] P.topState = P.botState :=
  P.exists_exhaust_of_decline ha₀ hle hzero fun _a ha =>
    P.policy_lt_self_of_impatient_iid hβR hiid hderiv hanti hdupos hpos hslack hz₀
      ⟨le_trans ha₀.le ha.1, ha.2⟩ (lt_of_lt_of_le ha₀ ha.1)

/-! ### CRRA, with the marginal-utility hypotheses discharged -/

/-- **Açıkgöz Proposition 4 for CRRA.** Marginal utility `c ^ (-γ)` is positive and decreasing
for every `γ > 0`, so impatience is the whole hypothesis. -/
theorem crra_exists_exhaust_of_impatient {γ : ℝ} (hγ0 : 0 < γ) (hu : P.u = crraUtility γ)
    (hβR : (P.discount : ℝ) * (1 + P.interest) < 1) (hiid : P.IidIncome)
    (hpos : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, 0 < P.consumptionFn z x)
    (hslack : ∀ (z : Z), ∀ x ∈ Icc assetFloor assetCap, P.policy (x, z) < P.maxSaving (x, z))
    {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    {a₀ : ℝ} (ha₀ : assetFloor < a₀) (hle : a₀ ≤ assetCap)
    (hzero : ∀ a ∈ Icc assetFloor a₀, P.policy (a, z₀) = assetFloor) :
    ∃ N : ℕ, (P.gBad z₀)^[N] P.topState = P.botState :=
  P.exists_exhaust_of_impatient hβR hiid (du := fun c => c ^ (-γ))
    (fun c hc => by rw [hu]; exact hasDerivAt_crraUtility γ hc)
    (fun _ hx _ _ hxy => Real.rpow_le_rpow_of_nonpos hx hxy (by linarith))
    (fun c hc => Real.rpow_pos_of_pos hc _) hpos hslack hz₀ ha₀ hle hzero

end IncomeFluctuation

end LeanEconomics
