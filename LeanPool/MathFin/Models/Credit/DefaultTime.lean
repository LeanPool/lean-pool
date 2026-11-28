/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Contracts.Instruments.Credit
public import LeanPool.MathFin.Pricing.Value
public import LeanPool.MathFin.Models.Credit.Cox
public import LeanPool.MathFin.Models.Credit.CVA

/-!
# The credit default swap priced against a default time

`Contracts/Instruments/Credit.lean` writes the CDS on a payment grid as a contract that observes
the default indicator `N u = 1{τ ≤ u}`. Here a default time `τ : Ω → ℝ` is the model:
`defaultIndicator τ` reads `N` off it, so each leg is a finite sum of discounted values
`𝔼[N u] = Q(τ ≤ u)`. Given the survival function `S` (`Q(τ ≤ u) = 1 − S u`) the legs are worth

* the premium leg, `s` times the **grid annuity** `∑ D(tᵢ₊₁) (tᵢ₊₁ − tᵢ) S(tᵢ₊₁)`
  (`cdsAnnuityGrid`, `value_cdsPremiumLeg`);
* the protection leg, `1 − R` times the **grid losses** `∑ D(tᵢ₊₁) (S tᵢ − S tᵢ₊₁)`
  (`cdsLossesGrid`, `value_cdsProtectionLeg`);

and the protection buyer's CDS is worth their difference (`value_cdsBuyer`), zero exactly at the
**grid par spread** `(1 − R) · losses / annuity` (`value_cdsBuyer_eq_zero_iff`). These are the
discrete analogues of `Cox.cdsAnnuity`, `Cox.cdsLosses` and `Cox.cdsFairSpreadTV`.

The Cox default time of `Models/Credit/Cox.lean`, built by inverting a unit-exponential clock
through the cumulative hazard, has `S = hazardSurvival h` (`cox_cdf_timeVarying`), so under it the
CDS contract is worth the grid legs of the hazard curve (`value_cdsBuyer_coxDefaultTime`). The
protection leg paid at `τ` itself is the contract `cdsProtectionAtDefault` (`Contract.payAtHit` on
the default indicator): its value is `(1 − R)·𝔼[D(τ)·1{τ ≤ T}]` (`value_cdsProtectionAtDefault`),
which under the Cox default time at a flat rate is `Cox.protectionLeg`
(`value_cdsProtectionAtDefault_coxDefaultTime`, by `CVA.protectionLeg_eq_integral_coxDefaultTime`).
Against the continuous legs: with no discounting the grid losses on any grid from `0` to `T`
telescope to the default probability `1 − S(T)`, which is `Cox.cdsLosses 0 h T`
(`cdsLossesGrid_one_eq_cdsLosses`). With discounting the grid legs converge to the continuous ones
as the mesh goes to zero (`Models/Credit/DefaultTimeMesh.lean`).

## Main definitions

* `defaultIndicator` — the process `N u = 1{τ ≤ u}` as a model.
* `cdsAnnuityGrid`, `cdsLossesGrid`, `cdsParSpreadGrid`.

## Main results

* `value_cdsPremiumLeg`, `value_cdsProtectionLeg`, `value_cdsBuyer`, `value_cdsBuyer_eq_zero_iff`.
* `value_cdsBuyer_coxDefaultTime`, `cdsLossesGrid_one_eq_cdsLosses`.
* `hitTime_defaultIndicator`, `pathPV_cdsProtectionAtDefault`, `value_cdsProtectionAtDefault`,
  `value_cdsProtectionAtDefault_coxDefaultTime` — the protection leg paid at the default time.

## References

* [S. Bagaria, *Notes on Fixed Income Derivative Pricing*][BagariaFIDP], ch. 16
* [P. Bilokon, *The Contract Is Not the Model*][Bilokon2026]
* [D. Lando, *Credit Risk Modeling*][Lando2004], ch. 5
* [S. Peyton Jones, J. M. Eber and J. Seward, *Composing contracts*][PeytonJonesEberSeward2000]

## Tags

credit default swap, default time, survival probability, par spread, Cox process, hazard rate,
protection leg, MSC 91G40, JEL G12, JEL G33
-/

@[expose] public section

open MeasureTheory ProbabilityTheory
open scoped NNReal ENNReal

namespace MathFin.Contracts

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-- The default indicator process of a default time `τ`, `N u = 1{τ ≤ u}`, as the model of the
single underlying `()`. -/
noncomputable def defaultIndicator (τ : Ω → ℝ) : Unit → ℝ≥0 → Ω → ℝ :=
  fun _ u ↦ {ω | τ ω ≤ u}.indicator 1

/-- The **grid annuity** (premium-leg kernel) of the survival function `S` on the grid `t`:
`∑ D(tᵢ₊₁) (tᵢ₊₁ − tᵢ) S(tᵢ₊₁)`. -/
noncomputable def cdsAnnuityGrid (D : ℝ≥0 → ℝ) (S : ℝ → ℝ) (t : ℕ → ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, D (t (i + 1)) * (((t (i + 1) : ℝ) - t i) * S (t (i + 1)))

/-- The **grid losses** (protection-leg kernel): `∑ D(tᵢ₊₁) (S tᵢ − S tᵢ₊₁)`, the discounted
probabilities of defaulting in each period. -/
noncomputable def cdsLossesGrid (D : ℝ≥0 → ℝ) (S : ℝ → ℝ) (t : ℕ → ℝ≥0) (n : ℕ) : ℝ :=
  ∑ i ∈ Finset.range n, D (t (i + 1)) * (S (t i) - S (t (i + 1)))

/-- The **grid par spread** `(1 − R) · losses / annuity`. -/
noncomputable def cdsParSpreadGrid (D : ℝ≥0 → ℝ) (S : ℝ → ℝ) (t : ℕ → ℝ≥0) (R : ℝ) (n : ℕ) : ℝ :=
  (1 - R) * cdsLossesGrid D S t n / cdsAnnuityGrid D S t n

section Value

variable {Q : Measure Ω} [IsProbabilityMeasure Q] {τ : Ω → ℝ} {S : ℝ → ℝ}

private theorem integrable_defaultIndicator (hτ : Measurable τ) (u : ℝ≥0) :
    Integrable (defaultIndicator τ () u) Q :=
  (integrable_const (1 : ℝ)).indicator (measurableSet_le hτ measurable_const)

private theorem integrable_one_sub_defaultIndicator (hτ : Measurable τ) (u : ℝ≥0) :
    Integrable (fun ω ↦ 1 - defaultIndicator τ () u ω) Q :=
  (integrable_const (1 : ℝ)).sub (integrable_defaultIndicator hτ u)

private theorem integrable_sub_defaultIndicator (hτ : Measurable τ) (u v : ℝ≥0) :
    Integrable (fun ω ↦ defaultIndicator τ () u ω - defaultIndicator τ () v ω) Q :=
  (integrable_defaultIndicator hτ u).sub (integrable_defaultIndicator hτ v)

omit [IsProbabilityMeasure Q] in
private theorem integral_defaultIndicator (hτ : Measurable τ)
    (hS : ∀ u : ℝ≥0, Q.real {ω | τ ω ≤ u} = 1 - S u) (u : ℝ≥0) :
    ∫ ω, defaultIndicator τ () u ω ∂Q = 1 - S u := by
  rw [← hS u]
  exact integral_indicator_one (measurableSet_le hτ measurable_const)

/-- **The premium leg is `s` times the grid annuity.** Against a default time `τ` with survival
function `S` (`Q(τ ≤ u) = 1 − S u`), the premium leg of the CDS is worth `s` times
`cdsAnnuityGrid D S t n`. -/
theorem value_cdsPremiumLeg (hτ : Measurable τ) (hS : ∀ u : ℝ≥0, Q.real {ω | τ ω ≤ u} = 1 - S u)
    (D : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0) (s : ℝ) (n : ℕ) :
    (cdsPremiumLeg t s n).value Q (fun t _ ↦ D t) (defaultIndicator τ)
      = s * cdsAnnuityGrid D S t n := by
  simp only [Contract.value, pathPV_cdsPremiumLeg, scenarioAt, cdsAnnuityGrid, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦
    ((integrable_one_sub_defaultIndicator hτ (t (i + 1))).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_const_mul, integral_const_mul, integral_sub (integrable_const 1)
    (integrable_defaultIndicator hτ _), integral_defaultIndicator hτ hS]
  simp
  ring

/-- **The protection leg is `1 − R` times the grid losses.** -/
theorem value_cdsProtectionLeg (hτ : Measurable τ)
    (hS : ∀ u : ℝ≥0, Q.real {ω | τ ω ≤ u} = 1 - S u) (D : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0) (R : ℝ)
    (n : ℕ) :
    (cdsProtectionLeg t R n).value Q (fun t _ ↦ D t) (defaultIndicator τ)
      = (1 - R) * cdsLossesGrid D S t n := by
  simp only [Contract.value, pathPV_cdsProtectionLeg, scenarioAt, cdsLossesGrid, Finset.mul_sum]
  rw [integral_finsetSum _ fun i _ ↦
    ((integrable_sub_defaultIndicator hτ (t (i + 1)) (t i)).const_mul _).const_mul _]
  refine Finset.sum_congr rfl fun i _ ↦ ?_
  rw [integral_const_mul, integral_const_mul, integral_sub (integrable_defaultIndicator hτ _)
    (integrable_defaultIndicator hτ _), integral_defaultIndicator hτ hS,
    integral_defaultIndicator hτ hS]
  ring

private theorem integrable_pathPV_cdsPremiumLeg (hτ : Measurable τ) (D : ℝ≥0 → ℝ)
    (t : ℕ → ℝ≥0) (s : ℝ) (n : ℕ) :
    Integrable (fun ω ↦ (cdsPremiumLeg t s n).pathPV D (scenarioAt (defaultIndicator τ) ω)) Q := by
  simp only [pathPV_cdsPremiumLeg]
  exact integrable_finsetSum _ fun i _ ↦
    ((integrable_one_sub_defaultIndicator hτ _).const_mul _).const_mul _

private theorem integrable_pathPV_cdsProtectionLeg (hτ : Measurable τ) (D : ℝ≥0 → ℝ)
    (t : ℕ → ℝ≥0) (R : ℝ) (n : ℕ) :
    Integrable
      (fun ω ↦ (cdsProtectionLeg t R n).pathPV D (scenarioAt (defaultIndicator τ) ω)) Q := by
  simp only [pathPV_cdsProtectionLeg]
  exact integrable_finsetSum _ fun i _ ↦
    ((integrable_sub_defaultIndicator hτ _ _).const_mul _).const_mul _

/-- **The protection buyer's CDS is worth protection less premium**: `(1 − R)` times the grid
losses minus `s` times the grid annuity. -/
theorem value_cdsBuyer (hτ : Measurable τ) (hS : ∀ u : ℝ≥0, Q.real {ω | τ ω ≤ u} = 1 - S u)
    (D : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0) (s R : ℝ) (n : ℕ) :
    (cdsBuyer t s R n).value Q (fun t _ ↦ D t) (defaultIndicator τ)
      = (1 - R) * cdsLossesGrid D S t n - s * cdsAnnuityGrid D S t n := by
  have hprem : Integrable (fun ω ↦ (Contract.scale (-1) (cdsPremiumLeg t s n)).pathPV D
      (scenarioAt (defaultIndicator τ) ω)) Q := by
    simp only [Contract.pathPV_scale]
    exact (integrable_pathPV_cdsPremiumLeg hτ D t s n).const_mul _
  rw [cdsBuyer, Contract.value_both _ _ _ _ _ (integrable_pathPV_cdsProtectionLeg hτ D t R n) hprem,
    Contract.value_scale, value_cdsProtectionLeg hτ hS, value_cdsPremiumLeg hτ hS]
  ring

/-- **The buyer's CDS is worth zero exactly at the grid par spread** (nonzero annuity). -/
theorem value_cdsBuyer_eq_zero_iff (hτ : Measurable τ)
    (hS : ∀ u : ℝ≥0, Q.real {ω | τ ω ≤ u} = 1 - S u) (D : ℝ≥0 → ℝ) (t : ℕ → ℝ≥0) (s R : ℝ)
    (n : ℕ) (hA : cdsAnnuityGrid D S t n ≠ 0) :
    (cdsBuyer t s R n).value Q (fun t _ ↦ D t) (defaultIndicator τ) = 0
      ↔ s = cdsParSpreadGrid D S t R n := by
  rw [value_cdsBuyer hτ hS, cdsParSpreadGrid, eq_div_iff hA, sub_eq_zero, eq_comm]

end Value

/-! ### The protection leg paid at the default time -/

section AtDefault

variable {μ : Measure Ω}

private theorem defaultIndicator_mem_Ici (τ : Ω → ℝ) (ω : Ω) (u : ℝ≥0) :
    defaultIndicator τ () u ω ∈ Set.Ici (1 : ℝ) ↔ τ ω ≤ u := by
  by_cases h : τ ω ≤ u <;> norm_num [defaultIndicator, Set.indicator, h]

/-- **The default indicator hits `[1, ∞)` at the default time**: the first time the observed
process `N u = 1{τ ≤ u}` reaches `1` is `τ`, or `0` if `τ` is negative. -/
theorem hitTime_defaultIndicator (τ : Ω → ℝ) (ω : Ω) :
    (scenarioAt (defaultIndicator τ) ω).hitTime () (Set.Ici 1) = ((τ ω).toNNReal : ℝ≥0) := by
  have hset : {i : ℝ≥0 | 0 ≤ i ∧ scenarioAt (defaultIndicator τ) ω () i ∈ Set.Ici (1 : ℝ)}
      = Set.Ici (τ ω).toNNReal := by
    ext i
    rw [Set.mem_ofPred_eq, scenarioAt, defaultIndicator_mem_Ici, Set.mem_Ici,
      Real.toNNReal_le_iff_le_coe]
    exact ⟨fun h ↦ h.2, fun h ↦ ⟨zero_le, h⟩⟩
  have hex : ∃ j : ℝ≥0, 0 ≤ j ∧ scenarioAt (defaultIndicator τ) ω () j ∈ Set.Ici (1 : ℝ) :=
    ⟨(τ ω).toNNReal, zero_le, (defaultIndicator_mem_Ici τ ω _).2 (Real.le_coe_toNNReal _)⟩
  rw [Scenario.hitTime, MeasureTheory.hittingAfter_def]
  beta_reduce
  simp only [hex, ↓reduceIte]
  rw [hset, csInf_Ici]

/-- **The path value of the protection leg paid at the default time**: `(1 − R)` discounted at
`τ`, if default happens by `T`. -/
theorem pathPV_cdsProtectionAtDefault (D : ℝ≥0 → ℝ) (τ : Ω → ℝ) (T : ℝ≥0) (R : ℝ) (ω : Ω) :
    (cdsProtectionAtDefault T R).pathPV D (scenarioAt (defaultIndicator τ) ω)
      = D (τ ω).toNNReal * ((1 - R) * defaultIndicator τ () T ω) := by
  rw [cdsProtectionAtDefault,
    Contract.pathPV_payAtHit_of_eq _ _ _ (hitTime_defaultIndicator τ ω)]
  simp [Payoff.eval, scenarioAt]

/-- **The protection leg paid at the default time is worth `(1 − R)·𝔼[D(τ)·1{τ ≤ T}]`**, for any
pricing measure, default time and discount curve (`D` is read at `τ` made nonnegative). It is an
identity of Bochner integrals with no integrability assumed: when the integrand is not integrable
both sides are `0`. -/
theorem value_cdsProtectionAtDefault (D : ℝ≥0 → ℝ) (τ : Ω → ℝ) (T : ℝ≥0)
    (R : ℝ) :
    (cdsProtectionAtDefault T R).value μ (fun t _ ↦ D t) (defaultIndicator τ)
      = (1 - R) * ∫ ω, (Set.Iic (T : ℝ)).indicator (fun s ↦ D s.toNNReal) (τ ω) ∂μ := by
  rw [Contract.value, ← integral_const_mul]
  refine integral_congr_ae (ae_of_all _ fun ω ↦ ?_)
  beta_reduce
  rw [pathPV_cdsProtectionAtDefault]
  by_cases h : τ ω ≤ T
  · simp [defaultIndicator, Set.indicator, h]
    ring
  · simp [defaultIndicator, Set.indicator, h]

end AtDefault

section Cox

open MathFin.Cox

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {h : ℝ → ℝ}

omit [IsProbabilityMeasure μ] in
/-- **The Cox default time has survival function `hazardSurvival h`**, in the form the CDS
legs consume: `μ(τ ≤ u) = 1 − S u` for every date `u ≥ 0`. -/
theorem measureReal_coxDefaultTime_le (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop) {ξ : Ω → ℝ}
    (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1) (u : ℝ≥0) :
    μ.real {ω | coxDefaultTime h ξ ω ≤ u} = 1 - hazardSurvival h u := by
  have hS1 : hazardSurvival h u ≤ 1 :=
    Real.exp_le_one_iff.2 (neg_nonpos.2 (intervalIntegral.integral_nonneg u.coe_nonneg fun s _ ↦
      (hpos s).le))
  have hcdf := cox_cdf_timeVarying (μ := μ) hh hpos hdiv hξmeas hξlaw u.coe_nonneg
  refine (congrArg ENNReal.toReal hcdf).trans ?_
  rw [ENNReal.toReal_sub_of_le (ENNReal.ofReal_le_one.2 hS1) ENNReal.one_ne_top,
    ENNReal.toReal_ofReal (hazardSurvival_pos h u).le, ENNReal.toReal_one]

/-- **The CDS contract under the Cox default time**: the protection buyer's CDS on the grid `t`,
priced against the default time built from a unit-exponential clock `ξ` by inverting the
cumulative hazard of a continuous positive intensity `h`, is worth `(1 − R)` times the grid losses
of the hazard curve less `s` times its grid annuity. -/
theorem value_cdsBuyer_coxDefaultTime (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop) {ξ : Ω → ℝ}
    (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1) (D : ℝ≥0 → ℝ)
    (t : ℕ → ℝ≥0) (s R : ℝ) (n : ℕ) :
    (cdsBuyer t s R n).value μ (fun t _ ↦ D t) (defaultIndicator (coxDefaultTime h ξ))
      = (1 - R) * cdsLossesGrid D (hazardSurvival h) t n
        - s * cdsAnnuityGrid D (hazardSurvival h) t n :=
  value_cdsBuyer (measurable_coxDefaultTime hh hpos hξmeas)
    (measureReal_coxDefaultTime_le hh hpos hdiv hξmeas hξlaw) D t s R n

/-- Without discounting the grid losses telescope to the default probability, whatever the grid. -/
theorem cdsLossesGrid_one (S : ℝ → ℝ) (t : ℕ → ℝ≥0) (n : ℕ) :
    cdsLossesGrid (fun _ ↦ 1) S t n = S (t 0) - S (t n) := by
  simpa [cdsLossesGrid] using Finset.sum_range_sub' (fun i ↦ S (t i)) n

/-- **The undiscounted grid losses are the continuous ones**: on any grid from `t 0 = 0` to `t n`,
the undiscounted grid losses of the hazard curve equal `Cox.cdsLosses 0 h (t n)`, the integral
of the default density. -/
theorem cdsLossesGrid_one_eq_cdsLosses (hh : Continuous h) (t : ℕ → ℝ≥0) (n : ℕ)
    (h0 : t 0 = 0) :
    cdsLossesGrid (fun _ ↦ 1) (hazardSurvival h) t n = cdsLosses 0 h (t n) := by
  rw [cdsLossesGrid_one, h0, NNReal.coe_zero, hazardSurvival_at_zero, cdsLosses]
  simp only [zero_mul, neg_zero, Real.exp_zero, one_mul]
  exact (defaultDensity_antideriv hh _).symm

/-! ### The protection leg paid at the Cox default time -/

omit [IsProbabilityMeasure μ] in
/-- **The Cox default time is a.s. positive**: its law has no atom at `0`,
`μ(τ ≤ 0) = 1 − S(0) = 0`. -/
theorem ae_pos_coxDefaultTime (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop) {ξ : Ω → ℝ}
    (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1) :
    ∀ᵐ ω ∂μ, 0 < coxDefaultTime h ξ ω := by
  have h0 := cox_cdf_timeVarying (μ := μ) hh hpos hdiv hξmeas hξlaw (le_refl (0 : ℝ))
  rw [hazardSurvival_at_zero, ENNReal.ofReal_one, tsub_self] at h0
  filter_upwards [measure_eq_zero_iff_ae_notMem.1 h0] with ω hω
  exact not_le.1 hω

/-- **The protection leg paid at the default time, under the Cox default time, is the continuous
protection leg `Cox.protectionLeg`**: for a continuous positive intensity `h` with divergent
cumulative hazard, the contract that pays `1 − R` at the first time the default indicator reaches
`1`, if that is by `T`, discounted at the flat rate `r` (`D u = e^{−ru}`), is worth
`(1 − R) ∫₀ᵀ e^{−rs} h(s) S(s) ds`. -/
theorem value_cdsProtectionAtDefault_coxDefaultTime (hh : Continuous h) (hpos : ∀ s, 0 < h s)
    (hdiv : Filter.Tendsto (cumHazard h) Filter.atTop Filter.atTop) {ξ : Ω → ℝ}
    (hξmeas : Measurable ξ) (hξlaw : Measure.map ξ μ = expMeasure 1) (r R : ℝ) (T : ℝ≥0) :
    (cdsProtectionAtDefault T R).value μ (fun (u : ℝ≥0) _ ↦ Real.exp (-(r * u)))
        (defaultIndicator (coxDefaultTime h ξ))
      = protectionLeg R r h T := by
  rw [value_cdsProtectionAtDefault,
    CVA.protectionLeg_eq_integral_coxDefaultTime hh hpos hdiv hξmeas hξlaw R r T.coe_nonneg]
  congr 1
  refine integral_congr_ae ?_
  filter_upwards [ae_pos_coxDefaultTime hh hpos hdiv hξmeas hξlaw] with ω hω
  simp only [Set.indicator, Set.mem_Iic, Real.coe_toNNReal _ hω.le]

end Cox

end MathFin.Contracts
