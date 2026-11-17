/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.Tauchen
public import LeanPool.AiyagariEquilibrium.Equilibrium.AiyagariUniqueness

/-!
# Finite Tauchen earnings for normalized capped-log clearing

The earnings chain discretizes `log l' = ρ log l + σ √(1 - ρ²) ε`, with standard normal `ε`,
on `n + 2` grid points in `[-3σ, 3σ]`. Its earnings scale `c > 0` is arbitrary: no mean-one
endowment normalization is imposed. Monotone transitions and positive one-step access to the
lowest state follow from `monotoneTransitions_of_tauchen` and `tauchen_pos_zero`.

The household has discount `24/25`, log utility, no borrowing and a fixed finite asset cap.
The rate-uniqueness endpoint uses the prescribed unit-wage normalized clearing equation
`aggregateCapital μ = normalisedDemand (9/25) (2/25) r`, with demand `9 / (16 * (r + 2/25))`,
and an explicit cap-slack inequality at the larger rate.

A bridge from these household units and the fixed cap to full competitive market clearing
for arbitrary earnings scales is not established here. The theorem concerns this explicit
normalized clearing equation.
-/

@[expose] public section

open Set MeasureTheory

namespace LeanEconomics

/-- A capped log household with a Tauchen earnings chain: `β = 0.96`, no borrowing,
`n + 2` grid points on `[-3σ, 3σ]`, persistence `ρ`, unconditional standard deviation `σ`
and arbitrary positive earnings scale `c`. -/
noncomputable def aiyagariTauchen (n : ℕ) (ρ σ c cap : ℝ) (hρ0 : 0 ≤ ρ) (hρ1 : ρ < 1)
    (hσ : 0 < σ) (hc : 0 < c) (hcap : 0 ≤ cap) : IncomeFluctuation (Fin (n + 2)) 0 cap where
  income i := c * Real.exp (-3 * σ + i * (6 * σ / (n + 1)))
  transitionMatrix := tauchen ρ (σ * Real.sqrt (1 - ρ ^ 2)) (-3 * σ) (6 * σ / (n + 1)) (n + 1)
  interest := 0
  discount := 24 / 25
  u := crraUtility 1
  minIncome := c * Real.exp (-3 * σ)
  maxIncome := c * Real.exp (3 * σ)
  minIncome_pos := mul_pos hc (Real.exp_pos _)
  minIncome_le i := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply Real.exp_le_exp.mpr
    have hi : (0 : ℝ) ≤ i := Nat.cast_nonneg _
    have hw : (0 : ℝ) ≤ 6 * σ / (n + 1) := by positivity
    nlinarith
  le_maxIncome i := by
    apply mul_le_mul_of_nonneg_left _ hc.le
    apply Real.exp_le_exp.mpr
    have hi : (i : ℝ) ≤ n + 1 := by exact_mod_cast Nat.le_of_lt_succ i.isLt
    have hw : (0 : ℝ) ≤ 6 * σ / (n + 1) := by positivity
    have h1 : (i : ℝ) * (6 * σ / (n + 1)) ≤ (n + 1) * (6 * σ / (n + 1)) :=
      mul_le_mul_of_nonneg_right hi hw
    have h2 : ((n : ℝ) + 1) * (6 * σ / (n + 1)) = 6 * σ := by field_simp
    linarith
  transitionMatrix_nonneg i j :=
    tauchen_nonneg (mul_pos hσ (Real.sqrt_pos.mpr (by nlinarith))) (by positivity) i j
  transitionMatrix_sum i := tauchen_sum i
  interest_gt_neg_one := by norm_num
  assetFloor_le_assetCap := hcap
  assetCap_nonneg := hcap
  minConsumption_pos := by
    have := mul_pos hc (Real.exp_pos (-3 * σ))
    linarith
  minConsumption_le_floor := le_rfl
  discount_lt_one := by norm_num
  dom := Ioi 0
  Ioi_subset_dom := subset_rfl
  dom_subset_Ici := Ioi_subset_Ici_self
  continuousOn_u_dom := continuousOn_crraUtility 1
  monotoneOn_u_dom := monotoneOn_crraUtility 1
  strictConcaveOn_u_dom := strictConcaveOn_crraUtility one_pos
  continuousOn_extendDom :=
    continuousOn_extendDom_Ioi (continuousOn_crraUtility 1) (tendsto_atBot_crraUtility le_rfl)

variable {n : ℕ} {ρ σ c cap : ℝ} {hρ0 : 0 ≤ ρ} {hρ1 : ρ < 1} {hσ : 0 < σ} {hc : 0 < c}
  {hcap : 0 ≤ cap}

/-- Income rises strictly with the state. -/
theorem aiyagariTauchen_income_strictMono :
    StrictMono (aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).income := by
  intro i j hij
  apply mul_lt_mul_of_pos_left _ hc
  apply Real.exp_lt_exp.mpr
  have hw : (0 : ℝ) < 6 * σ / (n + 1) := by positivity
  have : (i : ℝ) < j := by exact_mod_cast hij
  nlinarith

/-- The lowest state has the lowest income, which is `minIncome`. -/
theorem aiyagariTauchen_income_zero :
    (aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).income 0
      = (aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).minIncome := by
  change c * Real.exp (-3 * σ + ((0 : Fin (n + 2)) : ℝ) * (6 * σ / (n + 1))) = c * Real.exp (-3 * σ)
  simp

/-- The chain has monotone transitions. -/
theorem aiyagariTauchen_monotone :
    (aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).MonotoneTransitions :=
  monotoneTransitions_of_tauchen _ rfl aiyagariTauchen_income_strictMono hρ0
    (mul_pos hσ (Real.sqrt_pos.mpr (by nlinarith))) (by positivity)

/-- **Two normalized clearing rates in `(-δ, λ)` coincide** for the finite Tauchen household,
for any number of states, `ρ ∈ [0, 1)`, `σ > 0` and positive earnings scale, given the cap
condition at the larger rate. The hypotheses use the explicit prescribed normalized demand. -/
theorem aiyagariTauchen_equilibriumRate_unique_Ioo {r₁ r₂ : ℝ}
    (h₁ : r₁ ∈ Ioo (-2 / 25 : ℝ) (1 / 24)) (h₂ : r₂ ∈ Ioo (-2 / 25 : ℝ) (1 / 24))
    (hcapc : 2 * (24 / 25) * (c * Real.exp (3 * σ)) < (1 - 24 / 25 * (1 + max r₁ r₂)) * cap)
    (hrr₁ : (aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).RateOK r₁)
    (hrr₂ : (aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).RateOK r₂)
    {μ₁ μ₂ : ProbabilityMeasure (aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).State}
    (hμ₁ : ((aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).withRate r₁ hrr₁).IsStationary μ₁)
    (hμ₂ : ((aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).withRate r₂ hrr₂).IsStationary μ₂)
    (he₁ : (aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).aggregateCapital μ₁
      = normalisedDemand (9 / 25) (2 / 25) r₁)
    (he₂ : (aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).aggregateCapital μ₂
      = normalisedDemand (9 / 25) (2 / 25) r₂) : r₁ = r₂ :=
  (aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).aiyagari1994_log_equilibriumRate_unique_Ioo
    rfl rfl rfl aiyagariTauchen_monotone (z₀ := 0)
    (fun z => by
      rw [aiyagariTauchen_income_zero]
      exact (aiyagariTauchen n ρ σ c cap hρ0 hρ1 hσ hc hcap).minIncome_le z)
    aiyagariTauchen_income_zero (fun z => tauchen_pos_zero z) h₁ h₂ hcapc hrr₁ hrr₂ hμ₁ hμ₂ he₁ he₂

end LeanEconomics
