/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Pricing.Market
public import LeanPool.MathFin.Probability.Martingales.TimeChange

/-!
# The one-date market

The smallest market with a pricing measure, and the one a closed-form family reads in when it
prices at a single date: one traded asset that is quoted at its initial price `s₀` (growing at the
rate `r` of the money market, so that the deflated price is the constant `s₀`) until a date `τ`,
and at a random value `X` from `τ` on, with the money market `e^{rt}` as numéraire and no
information before `τ` (`Market.oneDate`).

Up to the horizon `τ`, the deflated asset is a martingale for a measure `Q` exactly when it is a
probability measure for which `X` is integrable with `𝔼_Q[X] = s₀ e^{rτ}`. With `Q` equivalent to
the reference measure `P`, it is a pricing measure (`Market.isPricingMeasure_oneDate`). The
information is the time change of the two-step filtration `⊥ ≤ mΩ` along the date `τ`
(`Market.dateFiltration`), so the martingale is that of `martingale_min_of_condExp_succ`, read
along the time change (`Martingale.comp`).

The price of a contract that reads the asset at `τ` only is the integral against `Q` of its payoff,
discounted by `e^{−rτ}` (`Market.price_pay_obs_oneDate`, `Market.price_europeanCall_oneDate`).

The model is as small as can be: the initial price is a parameter, with no dynamics before `τ`,
so that a measure prices the market says only that it is equivalent to `P` and calibrated to the
quote `s₀`. A family's socket here certifies that its law prices a market, and the work is in the
family's own moment identity (the Esscher or Merton compensator, the tilted mean).
The families that instantiate it (`Models/Jumps/Market.lean`, `Insurance/EsscherPremium.lean`) say
which law of `X` and which `Q` they read in it.

## Main definitions

* `Market.oneDate`: the market of a terminal value `X`, an initial price `s₀`, a rate `r` and a
  date `τ`.
* `Market.dateFiltration`: the information of the market, nothing before `τ` and everything from
  `τ` on.

## Main results

* `Market.isPricingMeasure_oneDate`: a probability measure equivalent to `P`, with `X` integrable
  and `𝔼_Q[X] = s₀ e^{rτ}`, is a pricing measure up to `τ`.
* `Market.integral_eq_of_isPricingMeasure_oneDate`: the converse for `τ > 0`: a pricing measure
  makes `X` integrable with mean `s₀ e^{rτ}`.
* `Market.price_pay_obs_oneDate`: the claim paying the asset at `τ` is worth `𝔼_Q[e^{−rτ} X]`.
* `Market.price_europeanCall_oneDate`: the call struck at `K` is worth `𝔼_Q[e^{−rτ} (X − K)⁺]`.

## References

* [J. M. Harrison and S. R. Pliska, *Martingales and stochastic integrals in the theory of
  continuous trading*][HarrisonPliska1981]
* [H. Föllmer and A. Schied, *Stochastic Finance: An Introduction in Discrete Time*][FollmerSchied],
  §5.2

## Tags

one-period market, pricing measure, equivalent martingale measure, risk-neutral pricing,
MSC 91G20, MSC 60G44, JEL G13
-/

@[expose] public section

open MeasureTheory MathFin.Contracts
open scoped NNReal

namespace MathFin.Market

/-- The two-step filtration of `ℕ`: nothing is known at `0`, everything from `1` on. -/
def twoStepFiltration (Ω : Type*) [mΩ : MeasurableSpace Ω] : Filtration ℕ mΩ where
  seq n := if n = 0 then ⊥ else mΩ
  mono' a b hab := by
    dsimp only
    split_ifs with ha hb hb
    · exact le_rfl
    · exact bot_le
    · exact absurd (Nat.le_zero.mp (hb ▸ hab)) ha
    · exact le_rfl
  le' := fun n ↦ by
    split_ifs
    · exact bot_le
    · exact le_rfl

section TwoStep

variable (Ω : Type*) [mΩ : MeasurableSpace Ω]

theorem twoStepFiltration_zero : twoStepFiltration Ω 0 = ⊥ := rfl

theorem twoStepFiltration_one : twoStepFiltration Ω 1 = mΩ := rfl

end TwoStep

/-- The step of a date: `0` before `τ`, `1` from `τ` on. -/
noncomputable def dateStep (τ t : ℝ≥0) : ℕ := if t < τ then 0 else 1

theorem monotone_dateStep (τ : ℝ≥0) : Monotone (dateStep τ) := by
  intro a b hab
  by_cases hb : b < τ
  · simp [dateStep, hb, hab.trans_lt hb]
  · by_cases ha : a < τ <;> simp [dateStep, ha, hb]

theorem dateStep_of_lt {τ t : ℝ≥0} (h : t < τ) : dateStep τ t = 0 := by simp [dateStep, h]

theorem dateStep_of_not_lt {τ t : ℝ≥0} (h : ¬ t < τ) : dateStep τ t = 1 := by simp [dateStep, h]

/-- **The information of the one-date market**: nothing is known before `τ`, everything from `τ`
on. It is the two-step filtration read along the step of the date. -/
noncomputable def dateFiltration (Ω : Type*) [mΩ : MeasurableSpace Ω] (τ : ℝ≥0) :
    Filtration ℝ≥0 mΩ :=
  (twoStepFiltration Ω).comp (monotone_dateStep τ)

section DateFiltration

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {τ t : ℝ≥0}

theorem dateFiltration_of_lt (h : t < τ) : dateFiltration Ω τ t = ⊥ := by
  rw [dateFiltration, Filtration.comp_apply, dateStep_of_lt h, twoStepFiltration_zero]

theorem dateFiltration_of_not_lt (h : ¬ t < τ) : dateFiltration Ω τ t = mΩ := by
  rw [dateFiltration, Filtration.comp_apply, dateStep_of_not_lt h, twoStepFiltration_one]

end DateFiltration

variable {Ω : Type*} [mΩ : MeasurableSpace Ω]

/-- **The one-date market**: one asset, quoted at `s₀ e^{rt}` before the date `τ` and at the
random value `X` from `τ` on, with the money market `e^{rt}` as numéraire, no information before
`τ` (`dateFiltration`) and the reference measure `P`. The deflated asset is `s₀` before `τ` and
`X e^{−rτ}` at `τ`. -/
noncomputable def oneDate (P : Measure Ω) {X : Ω → ℝ} (hX : Measurable X) (s₀ r : ℝ) (τ : ℝ≥0) :
    Market Unit Ω where
  P := P
  𝓕 := dateFiltration Ω τ
  asset _ t ω := if t < τ then s₀ * Real.exp (r * t) else X ω
  numeraire t _ := Real.exp (r * t)
  numeraire_pos _ _ := Real.exp_pos _
  asset_adapted _ t := by
    by_cases h : t < τ
    · simp only [h, ↓reduceIte]
      have hc : StronglyMeasurable[(⊥ : MeasurableSpace Ω)]
          (fun _ : Ω ↦ s₀ * Real.exp (r * t)) := stronglyMeasurable_const
      exact hc.mono (dateFiltration_of_lt h).ge
    · simp only [h, ↓reduceIte]
      exact hX.stronglyMeasurable.mono (dateFiltration_of_not_lt h).ge
  numeraire_adapted _ := stronglyMeasurable_const

variable (P : Measure Ω) {X : Ω → ℝ} (hX : Measurable X) (s₀ r : ℝ) (τ : ℝ≥0)

/-- The asset of the one-date market at the date `τ` is `X`. -/
theorem asset_oneDate_self (ω : Ω) : (oneDate P hX s₀ r τ).asset () τ ω = X ω := by
  simp [oneDate]

/-- The deflator of the one-date market at `τ` is the discount `e^{−rτ}`. -/
theorem deflator_oneDate (ω : Ω) : (oneDate P hX s₀ r τ).deflator τ ω = Real.exp (-r * τ) :=
  Market.deflator_of_numeraire_exp (fun _ _ ↦ rfl) τ ω

/-- The deflated price at step `0` is `s₀`, and from step `1` on it is `X e^{−rτ}`. -/
noncomputable def deflatedStep (X : Ω → ℝ) (s₀ r : ℝ) (τ : ℝ≥0) : ℕ → Ω → ℝ
  | 0 => fun _ ↦ s₀
  | _ + 1 => fun ω ↦ X ω / Real.exp (r * τ)

/-- **The deflated asset, frozen at `τ`, is the deflated step process read along the date**:
`S_tilde (min t τ) = g (min (step t) 1)`. -/
theorem deflated_oneDate_min (i : Unit) (t : ℝ≥0) (ω : Ω) :
    (oneDate P hX s₀ r τ).deflated i (min t τ) ω
      = deflatedStep X s₀ r τ (min (dateStep τ t) 1) ω := by
  by_cases h : t < τ
  · rw [dateStep_of_lt h, Nat.zero_min]
    change (if min t τ < τ then s₀ * Real.exp (r * ((min t τ : ℝ≥0) : ℝ)) else X ω)
        / Real.exp (r * ((min t τ : ℝ≥0) : ℝ)) = s₀
    rw [min_eq_left h.le]
    simp only [h, ↓reduceIte]
    exact mul_div_cancel_right₀ _ (Real.exp_pos _).ne'
  · rw [dateStep_of_not_lt h, min_self]
    change (if min t τ < τ then s₀ * Real.exp (r * ((min t τ : ℝ≥0) : ℝ)) else X ω)
        / Real.exp (r * ((min t τ : ℝ≥0) : ℝ)) = X ω / Real.exp (r * τ)
    rw [min_eq_right (not_lt.1 h)]
    simp only [lt_self_iff_false, ↓reduceIte]

variable {P hX s₀ r τ}

/-- **A pricing measure of the one-date market.** A probability measure `Q` equivalent to `P`
under which `X` is integrable with mean `s₀ e^{rτ}` prices the one-date market up to `τ`: the
deflated asset is the constant `s₀` before `τ` and `X e^{−rτ}` at `τ`, and `Q`-integrating the
latter gives back `s₀`. -/
theorem isPricingMeasure_oneDate {Q : Measure Ω} [IsProbabilityMeasure Q] (hQP : Q ≪ P)
    (hPQ : P ≪ Q) (hint : Integrable X Q) (hmean : ∫ ω, X ω ∂Q = s₀ * Real.exp (r * τ)) :
    (oneDate P hX s₀ r τ).IsPricingMeasure τ Q := by
  have hmart : Martingale (fun n ↦ deflatedStep X s₀ r τ (min n 1)) (twoStepFiltration Ω) Q := by
    refine martingale_min_of_condExp_succ (𝓕 := twoStepFiltration Ω) (S := deflatedStep X s₀ r τ)
      (T := 1) (fun t ht ↦ ?_) (fun t ht ↦ ?_) (fun t ht ↦ ?_)
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
      · have hc : StronglyMeasurable[(⊥ : MeasurableSpace Ω)] (fun _ : Ω ↦ s₀) :=
          stronglyMeasurable_const
        exact hc.mono (twoStepFiltration_zero Ω).ge
      · exact (hX.div_const (Real.exp (r * τ))).stronglyMeasurable.mono
          (twoStepFiltration_one Ω).ge
    · rcases Nat.le_one_iff_eq_zero_or_eq_one.mp ht with rfl | rfl
      · exact integrable_const s₀
      · exact hint.div_const (Real.exp (r * τ))
    · obtain rfl : t = 0 := Nat.lt_one_iff.mp ht
      rw [twoStepFiltration_zero, condExp_bot]
      refine Filter.Eventually.of_forall fun ω ↦ ?_
      change s₀ = ∫ x, X x / Real.exp (r * τ) ∂Q
      rw [integral_div, hmean, mul_div_assoc, div_self (Real.exp_pos _).ne', mul_one]
  refine .of_isEquivProbMeasure ⟨inferInstance, hQP, hPQ⟩ fun i ↦ ?_
  have e : (fun t ↦ (oneDate P hX s₀ r τ).deflated i (min t τ))
      = fun t ↦ (fun n ↦ deflatedStep X s₀ r τ (min n 1)) (dateStep τ t) :=
    funext fun t ↦ funext fun ω ↦ deflated_oneDate_min P hX s₀ r τ i t ω
  rw [e]
  exact hmart.comp (monotone_dateStep τ)

/-- **A pricing measure of the one-date market has the quoted mean.** For a date `τ > 0`, a
pricing measure `Q` of the one-date market makes `X` integrable with mean `s₀ e^{rτ}`: the deflated
asset is the constant `s₀` at `0` and `X e^{−rτ}` at `τ`, and a martingale keeps its mean
(`Martingale.setIntegral_eq`). This is the converse of `isPricingMeasure_oneDate`. For `τ = 0` the
quote `s₀` is never read, so no such constraint holds. -/
theorem integral_eq_of_isPricingMeasure_oneDate {Q : Measure Ω} (hτ : 0 < τ)
    (hQ : (oneDate P hX s₀ r τ).IsPricingMeasure τ Q) :
    Integrable X Q ∧ ∫ ω, X ω ∂Q = s₀ * Real.exp (r * τ) := by
  have := hQ.isProb
  have hm := hQ.martingale ()
  have h0 (ω : Ω) : (oneDate P hX s₀ r τ).deflated () (min 0 τ) ω = s₀ := by
    rw [deflated_oneDate_min, dateStep_of_lt hτ, Nat.zero_min]; rfl
  have hτ' (ω : Ω) :
      (oneDate P hX s₀ r τ).deflated () (min τ τ) ω = X ω / Real.exp (r * τ) := by
    rw [deflated_oneDate_min, dateStep_of_not_lt (lt_irrefl τ), min_self]; rfl
  have hi : Integrable (fun ω ↦ X ω / Real.exp (r * τ)) Q :=
    (hm.integrable τ).congr (.of_forall hτ')
  refine ⟨(hi.mul_const (Real.exp (r * τ))).congr (.of_forall fun ω ↦ ?_), ?_⟩
  · field_simp
  · have he : ∫ ω in Set.univ, (oneDate P hX s₀ r τ).deflated () (min 0 τ) ω ∂Q
        = ∫ ω in Set.univ, (oneDate P hX s₀ r τ).deflated () (min τ τ) ω ∂Q :=
      hm.setIntegral_eq (i := 0) (j := τ) (zero_le (a := τ)) (s := Set.univ) MeasurableSet.univ
    simp only [h0, hτ', Measure.restrict_univ] at he
    have e1 : ∫ _ : Ω, s₀ ∂Q = s₀ := by simp
    rw [e1, integral_div, eq_div_iff (Real.exp_pos _).ne'] at he
    exact he.symm

/-- **The claim paying the asset at `τ`** is worth the discounted expectation `𝔼_Q[e^{−rτ} X]`,
under any measure `Q`: the market's price is the contract value (`price`), and the asset at `τ` is
`X`. -/
theorem price_pay_obs_oneDate (Q : Measure Ω) :
    (oneDate P hX s₀ r τ).price Q (.pay τ (.obs () τ)) = ∫ ω, Real.exp (-r * τ) * X ω ∂Q := by
  rw [Market.price, Contract.value_pay]
  refine integral_congr_ae (.of_forall fun ω ↦ ?_)
  simp only [Payoff.eval, scenarioAt, asset_oneDate_self, deflator_oneDate]

/-- **The European call in the one-date market** is worth `𝔼_Q[e^{−rτ} (X − K)⁺]` under any
measure `Q`. -/
theorem price_europeanCall_oneDate (Q : Measure Ω) (K : ℝ) :
    (oneDate P hX s₀ r τ).price Q (europeanCall K τ)
      = ∫ ω, Real.exp (-r * τ) * max (X ω - K) 0 ∂Q := by
  rw [Market.price, europeanCall, Contract.value_pay]
  refine integral_congr_ae (.of_forall fun ω ↦ ?_)
  simp only [europeanCallPayoff, Payoff.eval, scenarioAt, asset_oneDate_self, deflator_oneDate]

end MathFin.Market
