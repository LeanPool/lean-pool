/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.LogAiyagari
public import LeanPool.AiyagariEquilibrium.Equilibrium.CapitalSupplyMonotone
public import LeanPool.AiyagariEquilibrium.Equilibrium.Uniqueness
public import LeanPool.AiyagariEquilibrium.Equilibrium.AiyagariContinuity
public import LeanPool.AiyagariEquilibrium.Equilibrium.SignChange

/-!
# Rate uniqueness for normalized capped-log clearing

This file combines rate monotonicity of household saving, monotonicity of stationary mean
assets and a strictly decreasing prescribed demand schedule. The log-household constants
support discount `24/25`.

## The prescribed normalized schedule

`normalisedDemand α δ r = α / ((1 - α) * (r + δ))` is the capital-to-wage ratio for a
Cobb–Douglas firm per unit of effective labor. The clearing equation used here equates this
schedule to mean household assets. No mean-one endowment condition or wage/asset-cap scaling
bridge to full competitive equilibrium is supplied. The result is uniqueness for this
explicit unit-wage normalized clearing problem.

## Household conditions

Transitions are monotone in income, and a lowest-income state is reached with positive
probability in one step from every state. The Tauchen construction verifies these properties
for its arbitrary positive earnings scale. The cap inequality
`2β * maxIncome < (1 - β * (1 + rhi)) * cap` guarantees the required saving bound across
the rate interval; the asset bounds are fixed across that family.
-/

@[expose] public section

open Set Filter Topology MeasureTheory BoundedContinuousFunction

namespace LeanEconomics

/-! ### The prescribed normalized demand -/

/-- The prescribed unit-wage normalized demand schedule, per unit of effective labor. -/
noncomputable def normalisedDemand (α δ r : ℝ) : ℝ := α / ((1 - α) * (r + δ))

theorem normalisedDemand_strictAntiOn {α δ rlo rhi : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ : 0 < rlo + δ) : StrictAntiOn (normalisedDemand α δ) (Icc rlo rhi) := by
  intro x hx y hy hxy
  simp only [normalisedDemand]
  have hx0 : 0 < (1 - α) * (x + δ) := mul_pos (by linarith) (by linarith [hx.1])
  have hlt : (1 - α) * (x + δ) < (1 - α) * (y + δ) :=
    mul_lt_mul_of_pos_left (by linarith) (by linarith)
  exact div_lt_div_of_pos_left hα0 hx0 hlt

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-! ### Theorem 1 on the interval, by chaining -/

/-- **Saving rises with the rate on `[rlo, rhi]`**, for log utility. Local comparisons from
`crra_policy_mono_withRate_of_minMPC` chained by `monotoneOn_of_local`. For log the minimal MPC is
`1 - β` at every rate, so every cap condition collapses to the one on `hcap`. -/
theorem log_policy_mono_rateFamily {rlo rhi ε : ℝ} (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβ : 0 < (P.discount : ℝ)) (hrlo : 0 < 1 + rlo)
    (hlohi : rlo ≤ rhi)
    (hε : 0 < ε)
    (hcap : (P.discount : ℝ) * P.maxIncome
      + ((P.discount : ℝ) * (1 + rhi) + ε) * assetCap < assetCap) :
    ∀ r ∈ Icc rlo rhi, ∀ r' ∈ Icc rlo rhi, r ≤ r' →
      ∀ s : ℝ × Z, s.1 ∈ Icc (0 : ℝ) assetCap →
        (P.rateFamily hrlo hlohi r).policy s
          ≤ (P.rateFamily hrlo hlohi r').policy s := by
  have hβ1 : (P.discount : ℝ) < 1 := P.discount_lt_one
  intro r hr r' hr' hle s hs
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hmono : MonotoneOn (fun x => (P.rateFamily hrlo hlohi x).policy s)
      (Icc rlo rhi) := by
    refine monotoneOn_of_local hε ?_
    intro x hx y hy hxy hgapxy
    have hxok : P.RateOK x := rateOK_of_floor_zero (by linarith [hx.1])
    have hyok : P.RateOK y := rateOK_of_floor_zero (by linarith [hy.1])
    change (P.rateFamily hrlo hlohi x).policy s
      ≤ (P.rateFamily hrlo hlohi y).policy s
    rw [P.rateFamily_eq _ _ hx hxok, P.rateFamily_eq _ _ hy hyok]
    obtain ⟨a, z⟩ := s
    have hκx : 1 - (P.withRate x hxok).minMPC 1 = (P.discount : ℝ) := by
      rw [IncomeFluctuation.minMPC_one, IncomeFluctuation.withRate_discount]; ring
    have hκy : 1 - (P.withRate y hyok).minMPC 1 = (P.discount : ℝ) := by
      rw [IncomeFluctuation.minMPC_one, IncomeFluctuation.withRate_discount]; ring
    have hκxpos : 0 < (P.withRate x hxok).minMPC 1 := by
      rw [IncomeFluctuation.minMPC_one, IncomeFluctuation.withRate_discount]; linarith
    have hκypos : 0 < (P.withRate y hyok).minMPC 1 := by
      rw [IncomeFluctuation.minMPC_one, IncomeFluctuation.withRate_discount]; linarith
    have hx_le : (P.discount : ℝ) * (1 + x) ≤ (P.discount : ℝ) * (1 + rhi) :=
      mul_le_mul_of_nonneg_left (by linarith [hx.2]) hβ.le
    have hy_le : (P.discount : ℝ) * (1 + y) ≤ (P.discount : ℝ) * (1 + rhi) :=
      mul_le_mul_of_nonneg_left (by linarith [hy.2]) hβ.le
    have hεcap : (0 : ℝ) ≤ ε * assetCap := mul_nonneg hε.le hcap0
    refine P.crra_policy_mono_withRate_of_minMPC (γ := 1) one_pos le_rfl hu hxok hyok hxy hκxpos
      hκypos hβ
      ((P.withRate x hxok).positiveConsumptionAll_of_unbounded hunb)
      ((P.withRate y hyok).positiveConsumptionAll_of_unbounded hunb) ?_ ?_ ?_ hs z
    · rw [hκx]
      have := mul_le_mul_of_nonneg_left hx_le hcap0
      nlinarith
    · rw [hκy]
      have := mul_le_mul_of_nonneg_left hy_le hcap0
      nlinarith
    · rw [hκx]
      have h1 : ((P.discount : ℝ) * (1 + x) + (y - x)) * assetCap
          ≤ ((P.discount : ℝ) * (1 + rhi) + ε) * assetCap :=
        mul_le_mul_of_nonneg_right (by linarith) hcap0
      linarith
  exact hmono hr hr' hle

/-! ### The Doeblin chain on the interval -/

section Measure

variable [MeasurableSpace Z] [BorelSpace Z]

omit [MeasurableSpace Z] [BorelSpace Z] in
/-- The per-rate corner test, from its worst case at the top of the interval. For log the test
at rate `r` is `β(1+r)(income z₀ + (1+r) a₀) < minIncome`, increasing in `r`. -/
theorem log_corner_of_top {rlo rhi a₀ : ℝ} {z₀ : Z} (hβ : 0 < (P.discount : ℝ)) (ha₀ : 0 < a₀)
    (hcorn : (P.discount : ℝ) * (1 + rhi) * (P.income z₀ + (1 + rhi) * a₀) < P.minIncome)
    {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r) :
    ((P.withRate r hrr).discount : ℝ) * (1 + (P.withRate r hrr).interest)
        * (P.withRate r hrr).minIncome ^ (-(1 : ℝ))
      < ((P.withRate r hrr).income z₀ + (1 + (P.withRate r hrr).interest) * a₀) ^ (-(1 : ℝ)) := by
  have hy : 0 < P.income z₀ := lt_of_lt_of_le P.minIncome_pos (P.minIncome_le z₀)
  have hmin : 0 < P.minIncome := P.minIncome_pos
  have hq : 0 < P.income z₀ + (1 + r) * a₀ := by nlinarith [hrr.1]
  have hstep : (P.discount : ℝ) * (1 + r) * (P.income z₀ + (1 + r) * a₀)
      ≤ (P.discount : ℝ) * (1 + rhi) * (P.income z₀ + (1 + rhi) * a₀) := by
    have h1 : (P.discount : ℝ) * (1 + r) ≤ (P.discount : ℝ) * (1 + rhi) :=
      mul_le_mul_of_nonneg_left (by linarith [hr.2]) hβ.le
    have h2 : P.income z₀ + (1 + r) * a₀ ≤ P.income z₀ + (1 + rhi) * a₀ := by
      nlinarith [hr.2]
    exact mul_le_mul h1 h2 hq.le (mul_nonneg hβ.le (by linarith [hrr.1, hr.2]))
  simp only [IncomeFluctuation.withRate_discount, IncomeFluctuation.withRate_interest,
    IncomeFluctuation.withRate_minIncome, IncomeFluctuation.withRate_income,
    Real.rpow_neg_one]
  rw [mul_inv_lt_iff₀ hmin, inv_mul_eq_div, lt_div_iff₀ hq]
  linarith

/-- **A unique stationary distribution at every rate in `[0, rhi]`**, for log utility. -/
theorem log_existsUnique_isStationary {rlo rhi a₀ : ℝ} (hu : P.u = crraUtility 1)
    (hunb : P.Unbounded)
    (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + rhi) < 1)
    (hcap : (P.discount : ℝ) * (P.maxIncome + (1 + rhi) * assetCap) < assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hreach : ∀ z, 0 < P.transitionMatrix z z₀) (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hcorn : (P.discount : ℝ) * (1 + rhi) * (P.income z₀ + (1 + rhi) * a₀) < P.minIncome)
    {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r) :
    ∃! μ : ProbabilityMeasure P.State, (P.withRate r hrr).IsStationary μ := by
  have hβ1 : (P.discount : ℝ) < 1 := P.discount_lt_one
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hκ : 1 - (P.withRate r hrr).minMPC 1 = (P.discount : ℝ) := by
    rw [IncomeFluctuation.minMPC_one, IncomeFluctuation.withRate_discount]; ring
  have hκpos : 0 < (P.withRate r hrr).minMPC 1 := by
    rw [IncomeFluctuation.minMPC_one, IncomeFluctuation.withRate_discount]; linarith
  refine (P.withRate r hrr).crra_existsUnique_isStationary_of_euler_corner_monotone (γ := 1)
    one_pos hu rfl hκpos hβ (by simpa using
        (show (P.discount : ℝ) * (1 + r) < 1 by nlinarith [hr.2, hβ]))
    (P.monotoneTransitions_withRate hmono hrr)
    ((P.withRate r hrr).positiveConsumptionAll_of_unbounded hunb) ?_ hz₀ hreach ha₀ hle
    (P.log_corner_of_top hβ ha₀ hcorn hr hrr)
  rw [hκ]
  simp only [IncomeFluctuation.withRate_maxIncome, IncomeFluctuation.withRate_interest]
  have := mul_le_mul_of_nonneg_left (show (1 + r) * assetCap ≤ (1 + rhi) * assetCap from
    mul_le_mul_of_nonneg_right (by linarith [hr.2]) hcap0) hβ.le
  nlinarith

/-- **Convergence to it from any start**, at every rate in `[0, rhi]`. -/
theorem log_tendsto_pushProb {rlo rhi a₀ : ℝ} (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβ : 0 < (P.discount : ℝ))
    (hβR : (P.discount : ℝ) * (1 + rhi) < 1)
    (hcap : (P.discount : ℝ) * (P.maxIncome + (1 + rhi) * assetCap) < assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hreach : ∀ z, 0 < P.transitionMatrix z z₀) (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hcorn : (P.discount : ℝ) * (1 + rhi) * (P.income z₀ + (1 + rhi) * a₀) < P.minIncome)
    {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r)
    (μ₀ : ProbabilityMeasure P.State) {μ : ProbabilityMeasure P.State}
    (hμ : (P.withRate r hrr).IsStationary μ) :
    Tendsto (fun m => (P.withRate r hrr).pushProb^[m] μ₀) atTop (𝓝 μ) := by
  have hβ1 : (P.discount : ℝ) < 1 := P.discount_lt_one
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hκ : 1 - (P.withRate r hrr).minMPC 1 = (P.discount : ℝ) := by
    rw [IncomeFluctuation.minMPC_one, IncomeFluctuation.withRate_discount]; ring
  have hκpos : 0 < (P.withRate r hrr).minMPC 1 := by
    rw [IncomeFluctuation.minMPC_one, IncomeFluctuation.withRate_discount]; linarith
  refine (P.withRate r hrr).crra_tendsto_pushProb_of_euler_corner_monotone (γ := 1)
    one_pos hu rfl hκpos hβ (by simpa using
        (show (P.discount : ℝ) * (1 + r) < 1 by nlinarith [hr.2, hβ]))
    (P.monotoneTransitions_withRate hmono hrr)
    ((P.withRate r hrr).positiveConsumptionAll_of_unbounded hunb) ?_ hz₀ hreach ha₀ hle
    (P.log_corner_of_top hβ ha₀ hcorn hr hrr) μ₀ hμ
  rw [hκ]
  simp only [IncomeFluctuation.withRate_maxIncome, IncomeFluctuation.withRate_interest]
  have := mul_le_mul_of_nonneg_left (show (1 + r) * assetCap ≤ (1 + rhi) * assetCap from
    mul_le_mul_of_nonneg_right (by linarith [hr.2]) hcap0) hβ.le
  nlinarith

/-! ### Theorem 2: capital supply is monotone -/

/-- **Capital supply rises with the rate on `[0, rhi]`**, for log utility, along any selection of
stationary distributions. Light's Theorems 1 and 2. -/
theorem log_monotoneOn_capitalSupply {rlo rhi ε a₀ : ℝ} (hu : P.u = crraUtility 1)
    (hunb : P.Unbounded)
    (hβ : 0 < (P.discount : ℝ)) (hrlo : 0 < 1 + rlo)
    (hlohi : rlo ≤ rhi) (hβR : (P.discount : ℝ) * (1 + rhi) < 1)
    (hε : 0 < ε)
    (hcap : (P.discount : ℝ) * P.maxIncome
      + ((P.discount : ℝ) * (1 + rhi) + ε) * assetCap < assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hreach : ∀ z, 0 < P.transitionMatrix z z₀) (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hcorn : (P.discount : ℝ) * (1 + rhi) * (P.income z₀ + (1 + rhi) * a₀) < P.minIncome)
    (ν : ℝ → ProbabilityMeasure P.State)
    (hν : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).IsStationary (ν r)) :
    MonotoneOn (fun r => P.aggregateCapital (ν r)) (Icc rlo rhi) := by
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hcap' : (P.discount : ℝ) * (P.maxIncome + (1 + rhi) * assetCap) < assetCap := by
    have := mul_nonneg hε.le hcap0
    nlinarith
  refine P.monotoneOn_capitalSupply_of_policy_mono (P.rateFamily hrlo hlohi)
    (fun r r' z z' => rfl)
    (P.log_policy_mono_rateFamily hu hunb hβ hrlo hlohi hε hcap)
    ⟨Measure.dirac (Classical.ofNonempty : P.State), inferInstance⟩ ν ?_
  intro r hr
  have hrr : P.RateOK r := rateOK_of_floor_zero (by linarith [hr.1])
  rw [P.rateFamily_eq _ _ hr hrr]
  exact P.log_tendsto_pushProb hu hunb hβ hβR hcap' hmono hz₀ hreach ha₀ hle hcorn hr hrr _
    (hν r hr hrr)

/-! ### Theorem 3: single crossing -/

/-- **The normalized clearing rate is unique on `[rlo, rhi]`.** Two rates with stationary
household distributions whose mean assets equal the prescribed `normalisedDemand α δ r`
have the same rate, under the stated cap, transition and impatience hypotheses. -/
theorem log_equilibriumRate_unique {rlo rhi ε a₀ α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ : 0 < rlo + δ)
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβ : 0 < (P.discount : ℝ)) (hrlo : 0 < 1 + rlo)
    (hlohi : rlo ≤ rhi) (hβR : (P.discount : ℝ) * (1 + rhi) < 1)
    (hε : 0 < ε)
    (hcap : (P.discount : ℝ) * P.maxIncome
      + ((P.discount : ℝ) * (1 + rhi) + ε) * assetCap < assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hreach : ∀ z, 0 < P.transitionMatrix z z₀) (ha₀ : 0 < a₀) (hle : a₀ ≤ assetCap)
    (hcorn : (P.discount : ℝ) * (1 + rhi) * (P.income z₀ + (1 + rhi) * a₀) < P.minIncome)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (hμ₁ : (P.withRate r₁ hrr₁).IsStationary μ₁) (hμ₂ : (P.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : P.aggregateCapital μ₁ = normalisedDemand α δ r₁)
    (he₂ : P.aggregateCapital μ₂ = normalisedDemand α δ r₂) : r₁ = r₂ := by
  classical
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hcap' : (P.discount : ℝ) * (P.maxIncome + (1 + rhi) * assetCap) < assetCap := by
    have := mul_nonneg hε.le hcap0
    nlinarith
  -- the selection of stationary distributions, defined through the clamped rate
  have hE : ∀ r : ℝ, ∃! μ : ProbabilityMeasure P.State,
      (P.withRate (clampRate rlo rhi r)
        (rateOK_of_floor_zero (one_add_clampRate_pos hrlo hlohi r))).IsStationary μ :=
    fun r => P.log_existsUnique_isStationary hu hunb hβ hβR hcap' hmono hz₀ hreach ha₀ hle
      hcorn (clampRate_mem hlohi r) _
  set ν : ℝ → ProbabilityMeasure P.State := fun r => (hE r).choose with hνdef
  have hν : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).IsStationary (ν r) := by
    intro r hr hrr
    have hc : clampRate rlo rhi r = r := clampRate_eq hr
    rw [← P.withRate_congr hc _ hrr]
    exact (hE r).choose_spec.1
  have hid : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ μ : ProbabilityMeasure P.State,
      (P.withRate r hrr).IsStationary μ → μ = ν r := by
    intro r hr hrr μ hμ
    have hc : clampRate rlo rhi r = r := clampRate_eq hr
    refine (hE r).choose_spec.2 μ ?_
    rw [P.withRate_congr hc _ hrr]
    exact hμ
  rw [hid r₁ h₁ hrr₁ μ₁ hμ₁] at he₁
  rw [hid r₂ h₂ hrr₂ μ₂ hμ₂] at he₂
  exact eq_of_monotoneOn_of_strictAntiOn
    (P.log_monotoneOn_capitalSupply hu hunb hβ hrlo hlohi hβR hε hcap hmono hz₀ hreach ha₀ hle
      hcorn ν hν)
    (normalisedDemand_strictAntiOn hα0 hα1 hδ) h₁ h₂ he₁ he₂

/-! ### With the constants constructed

The interval, the step and the corner level are not primitives of the economy. Given only that
the cap clears `2β · maxIncome / (1 - β(1+rhi))`, choose the step as half the room under `1` and
the corner level as small as the corner test needs. -/

/-- **Uniqueness from one inequality on the cap.** -/
theorem log_equilibriumRate_unique_of_cap {rlo rhi α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1)
    (hδ : 0 < rlo + δ)
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβ : 0 < (P.discount : ℝ)) (hrlo : 0 < 1 + rlo)
    (hlohi : rlo ≤ rhi) (hβR : (P.discount : ℝ) * (1 + rhi) < 1)
    (hcap : 2 * (P.discount : ℝ) * P.maxIncome < (1 - (P.discount : ℝ) * (1 + rhi)) * assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hmin : P.income z₀ = P.minIncome) (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (hμ₁ : (P.withRate r₁ hrr₁).IsStationary μ₁) (hμ₂ : (P.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : P.aggregateCapital μ₁ = normalisedDemand α δ r₁)
    (he₂ : P.aggregateCapital μ₂ = normalisedDemand α δ r₂) : r₁ = r₂ := by
  set β : ℝ := (P.discount : ℝ) with hβdef
  set R : ℝ := 1 + rhi with hRdef
  have hR : 0 < R := by rw [hRdef]; linarith [hrlo, hlohi]
  have hroom : 0 < 1 - β * R := by rw [hβdef, hRdef]; linarith
  have hmaxpos : 0 < P.maxIncome := lt_of_lt_of_le P.minIncome_pos P.minIncome_le_maxIncome
  have hcap0 : 0 < assetCap := by
    by_contra h
    have h' : assetCap ≤ 0 := not_lt.mp h
    have : (1 - β * R) * assetCap ≤ 0 := mul_nonpos_of_nonneg_of_nonpos hroom.le h'
    nlinarith [hcap, hβ, hmaxpos]
  have hminpos : 0 < P.minIncome := P.minIncome_pos
  -- the step: half the room under `1`
  set ε : ℝ := (1 - β * R) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  -- the corner level: small enough for the corner test, and below the cap
  set A : ℝ := P.minIncome * (1 - β * R) / (2 * β * R ^ 2) with hAdef
  have hA : 0 < A := by rw [hAdef]; positivity
  set a₀ : ℝ := min assetCap A with ha₀def
  have ha₀ : 0 < a₀ := lt_min hcap0 hA
  have hle : a₀ ≤ assetCap := min_le_left _ _
  have ha₀A : a₀ ≤ A := min_le_right _ _
  -- the cap condition with the chosen step
  have hcapε : β * P.maxIncome + (β * R + ε) * assetCap < assetCap := by
    rw [hεdef]
    nlinarith [hcap]
  -- the corner test at the top of the interval
  have hcorn : β * R * (P.income z₀ + R * a₀) < P.minIncome := by
    rw [hmin]
    have hkey : β * R * (R * A) = P.minIncome * (1 - β * R) / 2 := by
      rw [hAdef]; field_simp; try ring
    have hmono : β * R * (R * a₀) ≤ β * R * (R * A) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha₀A hR.le) (by positivity)
    have : β * R * (P.minIncome + R * a₀) = β * R * P.minIncome + β * R * (R * a₀) := by ring
    rw [this]
    nlinarith [hkey, hmono, hroom, hminpos]
  exact P.log_equilibriumRate_unique hα0 hα1 hδ hu hunb hβ hrlo hlohi hβR hε hcapε hmono hz₀
    hreach ha₀ hle hcorn h₁ h₂ hrr₁ hrr₂ hμ₁ hμ₂ he₁ he₂

/-! ### Negative rates

The uniqueness theorems live on `[0, rhi]`. Below zero the minimal-MPC ceiling on capital
supply, `β · maxIncome / (1 - β(1+r))`, still holds for log utility — `κ = 1 - β` at every
rate — while Cobb--Douglas demand blows up as `r ↓ -δ`. Where the ceiling is below demand there
is no equilibrium. -/

/-- **The log capital ceiling at any admissible rate** with `β(1+r) < 1`: no sign restriction on
`r`, because `κ = 1 - β` (`minMPC_one`). -/
theorem log_aggregateCapital_le {r : ℝ} (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβ : 0 < (P.discount : ℝ)) (hrr : P.RateOK r)
    (hβR : (P.discount : ℝ) * (1 + r) < 1)
    (hthr : (P.discount : ℝ) * (P.maxIncome + (1 + r) * assetCap) < assetCap)
    {μ : ProbabilityMeasure P.State} (hμ : (P.withRate r hrr).IsStationary μ) :
    P.aggregateCapital μ
      ≤ (P.discount : ℝ) * P.maxIncome / (1 - (P.discount : ℝ) * (1 + r)) := by
  have hβ1 : (P.discount : ℝ) < 1 := P.discount_lt_one
  have hκ : 1 - (P.withRate r hrr).minMPC 1 = (P.discount : ℝ) := by
    rw [IncomeFluctuation.minMPC_one, IncomeFluctuation.withRate_discount]; ring
  have hκpos : 0 < (P.withRate r hrr).minMPC 1 := by
    rw [IncomeFluctuation.minMPC_one, IncomeFluctuation.withRate_discount]; linarith
  have hβR' : ((P.withRate r hrr).discount : ℝ) * (1 + (P.withRate r hrr).interest) < 1 := hβR
  have hthr' : (1 - (P.withRate r hrr).minMPC 1)
      * ((P.withRate r hrr).maxIncome + (1 + (P.withRate r hrr).interest) * assetCap)
      < assetCap := by
    rw [hκ]; exact hthr
  have hpc : (P.withRate r hrr).PositiveConsumptionAll :=
    (P.withRate r hrr).positiveConsumptionAll_of_unbounded hunb
  have hposIt : ∀ n : ℕ, ∀ z : Z, ∀ a ∈ Icc (0 : ℝ) assetCap,
      0 < (P.withRate r hrr).consumptionFnOf
        (((P.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) z a :=
    fun n z a ha => hpc _ ((P.withRate r hrr).concaveSlices_iterate_zero n) z a ha
  have hslackIt : ∀ n : ℕ, ∀ x ∈ Icc (0 : ℝ) assetCap, ∀ z : Z,
      (P.withRate r hrr).policyOf
        (((P.withRate r hrr).toExtended.bellman)^[n] (0 : (ℝ × Z) →ᵇ ℝ)) (x, z) < assetCap :=
    fun n x hx z => ((P.withRate r hrr).crra_minMPC_of_cap one_pos hu rfl hκpos hβ
      hposIt hthr' n).2 x hx z
  have hkey := (P.withRate r hrr).crra_aggregateCapital_le_of_minMPC one_pos hu hκpos hβ hβR'
    hposIt hslackIt hμ
  rw [hκ] at hkey
  exact hkey

/-- **No equilibrium where the ceiling is below demand.** -/
theorem log_no_equilibrium_of_ceiling {α δ r : ℝ} (hu : P.u = crraUtility 1)
    (hunb : P.Unbounded) (hβ : 0 < (P.discount : ℝ))
    (hrr : P.RateOK r) (hβR : (P.discount : ℝ) * (1 + r) < 1)
    (hthr : (P.discount : ℝ) * (P.maxIncome + (1 + r) * assetCap) < assetCap)
    (hD : (P.discount : ℝ) * P.maxIncome / (1 - (P.discount : ℝ) * (1 + r))
      < normalisedDemand α δ r)
    {μ : ProbabilityMeasure P.State} (hμ : (P.withRate r hrr).IsStationary μ) :
    P.aggregateCapital μ ≠ normalisedDemand α δ r := fun h => by
  have := P.log_aggregateCapital_le hu hunb hβ hrr hβR hthr hμ
  linarith

/-! ### Normalized clearing with the Aiyagari (1994) log calibration

The constants are `β = 0.96`, `α = 0.36` and `δ = 0.08`, with log utility, no borrowing,
and monotone earnings transitions reaching a lowest-income state with positive probability
in one step. The time-preference rate is `λ = 1/0.96 - 1 = 1/24`. The theorems concern the
prescribed normalized equation on intervals `-δ < rlo ≤ rhi < λ`; they do not identify it
with full competitive market clearing for arbitrary household earnings scales. -/

/-- **The calibrated normalized clearing rate is unique on `[rlo, rhi]`.** The interval is
above `-δ` and below the time-preference rate `1/24`. Earnings transitions are monotone and
reach a lowest-income state in one step; the asset cap must exceed
`(48/25) · maxIncome / (1 - (24/25)(1+rhi))`. -/
theorem aiyagari1994_log_equilibriumRate_unique {rlo rhi : ℝ}
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded) (hβ : (P.discount : ℝ) = 24 / 25)
    (hrlo : -2 / 25 < rlo) (hlohi : rlo ≤ rhi) (hlam : rhi < 1 / 24)
    (hcap : 2 * (24 / 25) * P.maxIncome < (1 - 24 / 25 * (1 + rhi)) * assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hmin : P.income z₀ = P.minIncome) (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Icc rlo rhi) (h₂ : r₂ ∈ Icc rlo rhi)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (hμ₁ : (P.withRate r₁ hrr₁).IsStationary μ₁) (hμ₂ : (P.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : P.aggregateCapital μ₁ = normalisedDemand (9 / 25) (2 / 25) r₁)
    (he₂ : P.aggregateCapital μ₂ = normalisedDemand (9 / 25) (2 / 25) r₂) : r₁ = r₂ :=
  P.log_equilibriumRate_unique_of_cap (by norm_num) (by norm_num) (by linarith) hu hunb
    (by rw [hβ]; norm_num) (by linarith) hlohi (by rw [hβ]; linarith)
    (by rw [hβ]; exact hcap) hmono hz₀ hmin hreach h₁ h₂ hrr₁ hrr₂ hμ₁ hμ₂ he₁ he₂

/-- **Two normalized clearing rates in `(-δ, λ)` coincide.** The interval version is applied
to `[min r₁ r₂, max r₁ r₂]`; the cap condition is required at the larger rate. The clearing
hypotheses equate stationary mean household assets to the prescribed normalized demand. -/
theorem aiyagari1994_log_equilibriumRate_unique_Ioo
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded) (hβ : (P.discount : ℝ) = 24 / 25)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hmin : P.income z₀ = P.minIncome) (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    {r₁ r₂ : ℝ} (h₁ : r₁ ∈ Ioo (-2 / 25 : ℝ) (1 / 24)) (h₂ : r₂ ∈ Ioo (-2 / 25 : ℝ) (1 / 24))
    (hcap : 2 * (24 / 25) * P.maxIncome < (1 - 24 / 25 * (1 + max r₁ r₂)) * assetCap)
    (hrr₁ : P.RateOK r₁) (hrr₂ : P.RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure P.State}
    (hμ₁ : (P.withRate r₁ hrr₁).IsStationary μ₁) (hμ₂ : (P.withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : P.aggregateCapital μ₁ = normalisedDemand (9 / 25) (2 / 25) r₁)
    (he₂ : P.aggregateCapital μ₂ = normalisedDemand (9 / 25) (2 / 25) r₂) : r₁ = r₂ :=
  P.aiyagari1994_log_equilibriumRate_unique hu hunb hβ (rlo := min r₁ r₂) (rhi := max r₁ r₂)
    (lt_min h₁.1 h₂.1) min_le_max (max_lt h₁.2 h₂.2) hcap hmono hz₀ hmin hreach
    ⟨min_le_left _ _, le_max_left _ _⟩ ⟨min_le_right _ _, le_max_right _ _⟩
    hrr₁ hrr₂ hμ₁ hμ₂ he₁ he₂

/-- **No normalized clearing at a negative rate where the saving ceiling is below demand.**
The ceiling–demand inequality uses the calibrated constants and is polynomial in `r` and
`maxIncome`, so it can be checked for any earnings grid. -/
theorem aiyagari1994_log_no_equilibrium_of_ceiling {r : ℝ}
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded) (hβ : (P.discount : ℝ) = 24 / 25)
    (hcap : 24 * P.maxIncome < assetCap) (hlo : -2 / 25 < r) (hr0 : r ≤ 0) (hrr : P.RateOK r)
    (hD : 24 / 25 * P.maxIncome * (r + 2 / 25) < 9 / 16 * (1 - 24 / 25 * (1 + r)))
    {μ : ProbabilityMeasure P.State} (hμ : (P.withRate r hrr).IsStationary μ) :
    P.aggregateCapital μ ≠ normalisedDemand (9 / 25) (2 / 25) r := by
  have hcap0 : (0 : ℝ) ≤ assetCap := P.assetCap_nonneg
  have hmax : 0 < P.maxIncome := lt_of_lt_of_le P.minIncome_pos P.minIncome_le_maxIncome
  refine P.log_no_equilibrium_of_ceiling hu hunb (by rw [hβ]; norm_num)
    hrr (by rw [hβ]; linarith) ?_ ?_ hμ
  · rw [hβ]
    have := mul_nonneg (neg_nonneg.mpr hr0) hcap0
    nlinarith
  · rw [hβ]
    simp only [normalisedDemand]
    have h1 : (0 : ℝ) < 1 - 24 / 25 * (1 + r) := by linarith
    have h2 : (0 : ℝ) < (1 - 9 / 25) * (r + 2 / 25) := by nlinarith
    rw [div_lt_div_iff₀ h1 h2]
    nlinarith [hD]

/-- **No normalized clearing on `(-δ, -1/20]`** when household income is at most `3/2` and
the stated asset-cap bound holds. The income bound is an explicit hypothesis in household
units; it is not inferred from a mean-one endowment normalization. -/
theorem aiyagari1994_log_no_equilibrium_below {r : ℝ}
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded) (hβ : (P.discount : ℝ) = 24 / 25)
    (hcap : 24 * P.maxIncome < assetCap) (hmax : P.maxIncome ≤ 3 / 2)
    (hr : r ∈ Ioc (-2 / 25 : ℝ) (-1 / 20)) (hrr : P.RateOK r)
    {μ : ProbabilityMeasure P.State} (hμ : (P.withRate r hrr).IsStationary μ) :
    P.aggregateCapital μ ≠ normalisedDemand (9 / 25) (2 / 25) r := by
  refine P.aiyagari1994_log_no_equilibrium_of_ceiling hu hunb hβ hcap hr.1 (by linarith [hr.2])
    hrr ?_ hμ
  have hx : (0 : ℝ) ≤ r + 2 / 25 := by linarith [hr.1]
  have := mul_le_mul_of_nonneg_right hmax hx
  nlinarith [hr.2]

end Measure

end IncomeFluctuation

end LeanEconomics
