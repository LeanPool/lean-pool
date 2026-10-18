/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Models.Tauchen
public import LeanPool.AiyagariEquilibrium.Equilibrium.AiyagariUniqueness


/-!
# Aiyagari (1994) with his own earnings process

Aiyagari's labour endowment follows `log l' = ρ log l + σ √(1 - ρ²) ε`, `ε ~ N(0,1)`, discretised
by Tauchen's method on `[-3σ, 3σ]`, and scaled so that its mean is one. He used seven states,
`ρ ∈ {0, 0.3, 0.6, 0.9}` and `σ ∈ {0.2, 0.4}`. The economy here has `n + 2` states for any `n`,
any `ρ ∈ [0, 1)`, any `σ > 0`, and any scale `c > 0` — the normalising constant is whatever it
is; uniqueness does not depend on it except through the cap condition, where it enters via the
highest endowment `c · e^{3σ}`.

The two facts about the chain that the uniqueness theorem needs — monotone transitions and a
lowest state reachable from everywhere — are `monotoneTransitions_of_tauchen` and
`tauchen_pos_zero`, both consequences of `Φ` being monotone and positive. Everything else is
`rfl` and `norm_num`, as for the two-state witnesses.
-/

@[expose] public section

open Set MeasureTheory

namespace LeanEconomics

/-- **Aiyagari (1994)'s economy with a Tauchen earnings chain**: `β = 0.96`, log utility, no
borrowing, `n + 2` grid points on `[-3σ, 3σ]` for the AR(1) with persistence `ρ` and
unconditional standard deviation `σ`, endowment scaled by `c`. -/
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

/-- **Aiyagari (1994) at `μ = 1` with his Tauchen earnings process: two equilibrium rates in
`(-δ, λ)` coincide**, for any number of states, any `ρ ∈ [0, 1)`, any `σ > 0` and any scale,
given the cap condition at the larger rate. -/
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
