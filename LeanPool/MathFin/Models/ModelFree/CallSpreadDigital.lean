/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Topology.Separation.CompletelyRegular
public import Mathlib.Topology.Algebra.Group.Order

/-!
# Call spreads tend to the digital, so call prices determine the law

A bull-call spread long `1/h` calls struck at `K` and short `1/h` calls struck at `K + h` pays
`((X − K)⁺ − (X − K − h)⁺)/h`. The payoff lies in `[0, 1]` (it is nonnegative because the call
payoff is antitone in the strike, `bull_call_spread_payoff_le`), and its absolute value is at most
`1` because the call payoff is `1`-Lipschitz in the strike (`abs_call_payoff_sub_le`). As `h ↓ 0`
it tends to the digital payoff `1_{X > K}`. So in any model, minus the right strike derivative of
the call price is the price of the event `X > K`, and the call prices at every strike determine
the law of the underlying. This is the first-order form of Breeden and Litzenberger (1978), for any
law with a finite mean, not only the lognormal one.

* `abs_call_payoff_sub_le`: `|(x − k₁)⁺ − (x − k₂)⁺| ≤ |k₁ − k₂|`, the bound that dominates every
  call spread and every strike difference quotient below.
* `tendsto_call_spread`: `(C(K) − C(K + h))/h → μ {X > K}` as `h ↓ 0`, where
  `C(k) = ∫ (X − k)⁺ dμ`, for a measurable, integrable `X` under a finite measure `μ` (dominated
  convergence).
* `measure_eq_of_integral_call_eq`: two probability laws of a log-return, each with `∫ eʸ < ∞`,
  that give the same undiscounted call price `∫ (Seʸ − K)⁺` at every strike `K > 0` (for one
  `S > 0`) are equal. The digital at the strike `Seᵃ` is the tail `P(Y > a)`.
* `hasDerivAt_integral_call`: where `X` has no atom at `K`, the call price is differentiable at
  `K` and `C'(K) = −μ {X > K}` (Mathlib's `hasDerivAt_integral_of_dominated_loc_of_lip`).
* `tendsto_call_spread_left`: the spread just below the strike, `(C(K − h) − C(K))/h`, tends to
  `μ {X ≥ K}`. So the left strike derivative is `−μ {X ≥ K}` and the right one `−μ {X > K}`.
* `differentiableAt_integral_call_iff`: the call price is differentiable at `K` iff `X` has no atom
  at `K`. At an atom the two one-sided derivatives differ by its mass, and the call price has a
  kink.

In Black–Scholes the strike derivative is `−e^{−rτ}Φ(d₂)` (`hasDerivAt_bsV_K`), from the closed
form. The digital price `e^{−rτ}Φ(d₂)` follows from it through `hasDerivAt_integral_call`
(`jumpDiffusionDigitalPrice_zero`), the same value that `bs_cash_or_nothing_formula` computes as a
Gaussian integral. The second-order form, the lognormal density as the second strike derivative of
`bsV`, is in `Models/ModelFree/BreedenLitzenberger.lean`.

## Main results

* `abs_call_payoff_sub_le`: `|(x − k₁)⁺ − (x − k₂)⁺| ≤ |k₁ − k₂|`.
* `tendsto_call_spread`: for a measurable integrable `X` under a finite measure, the bull-call
  spread `(C(K) − C(K + h))/h` tends to `μ {K < X}` as `h ↓ 0`.
* `tendsto_call_spread_left`: the spread `(C(K − h) − C(K))/h` tends to `μ {K ≤ X}` as `h ↓ 0`.
* `hasDerivAt_integral_call`: if `μ {X = K} = 0`, the call price `k ↦ ∫ (X − k)⁺` has derivative
  `−μ {K < X}` at `K`.
* `differentiableAt_integral_call_iff`: the call price is differentiable at `K` iff
  `μ {X = K} = 0`.
* `measure_eq_of_integral_call_eq`: two probability laws of a log-return, each with `∫ eʸ < ∞`,
  whose call prices `∫ (S·eʸ − K)⁺` agree at every strike `K > 0`, are equal.

## References

* [Breeden and Litzenberger, *Prices of state-contingent claims implicit in option
  prices*][BreedenLitzenberger1978]

## Tags

call spread, digital option, law from call prices, bull spread, strike derivative, MSC 91G20,
JEL G13
-/

@[expose] public section

namespace MathFin

open MeasureTheory Filter Set
open scoped Topology

/-- **The call payoff is `1`-Lipschitz in the strike**: `|(x − k₁)⁺ − (x − k₂)⁺| ≤ |k₁ − k₂|`
(Mathlib's `abs_max_sub_max_le_abs`). -/
lemma abs_call_payoff_sub_le (x k₁ k₂ : ℝ) :
    |max (x - k₁) 0 - max (x - k₂) 0| ≤ |k₁ - k₂| :=
  (abs_max_sub_max_le_abs _ _ _).trans_eq (by rw [sub_sub_sub_cancel_left, abs_sub_comm])

/-- **A digital is a limit of call spreads.** For a measurable, integrable `X` under a finite
measure `μ`, the bull-call spread `(C(K) − C(K + h))/h`, where `C(k) = ∫ (X − k)⁺ dμ`, tends to
`μ {X > K}` as `h ↓ 0`: minus the right strike derivative of the undiscounted call price is the
price of the event `X > K`. The spread payoff is at most `1` in absolute value (the call payoff is
`1`-Lipschitz in the strike) and tends to `1_{X > K}` pointwise, so dominated convergence
applies. -/
theorem tendsto_call_spread {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hXm : Measurable X) (hX : Integrable X μ) (K : ℝ) :
    Tendsto (fun h ↦ (∫ ω, max (X ω - K) 0 ∂μ - ∫ ω, max (X ω - (K + h)) 0 ∂μ) / h) (𝓝[>] 0)
      (𝓝 (μ.real {ω | K < X ω})) := by
  have hcall (k : ℝ) : Integrable (fun ω ↦ max (X ω - k) 0) μ :=
    (hX.sub (integrable_const k)).pos_part
  have hspread : (fun h ↦ (∫ ω, max (X ω - K) 0 ∂μ - ∫ ω, max (X ω - (K + h)) 0 ∂μ) / h)
      = fun h ↦ ∫ ω, (max (X ω - K) 0 - max (X ω - (K + h)) 0) / h ∂μ := by
    funext h
    rw [integral_div, integral_sub (hcall K) (hcall (K + h))]
  rw [hspread, ← integral_indicator_one (measurableSet_lt measurable_const hXm)]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 1)
    (Eventually.of_forall fun h ↦ ?_) ?_ (integrable_const 1) (ae_of_all _ fun ω ↦ ?_)
  · exact (by fun_prop : Measurable fun ω ↦
      (max (X ω - K) 0 - max (X ω - (K + h)) 0) / h).aestronglyMeasurable
  · -- the call payoff is `1`-Lipschitz in the strike, so the spread payoff is at most `1`
    filter_upwards [self_mem_nhdsWithin] with h hh
    refine ae_of_all _ fun ω ↦ ?_
    have hh : 0 < h := hh
    have hlip := abs_call_payoff_sub_le (X ω) K (K + h)
    rw [sub_add_cancel_left, abs_neg, abs_of_pos hh] at hlip
    change ‖(max (X ω - K) 0 - max (X ω - (K + h)) 0) / h‖ ≤ 1
    rwa [Real.norm_eq_abs, abs_div, abs_of_pos hh, div_le_one hh]
  · -- and tends to the digital payoff `1_{X > K}`
    by_cases hω : K < X ω
    · rw [indicator_of_mem (show ω ∈ {ω | K < X ω} from hω), Pi.one_apply]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 hω)] with h hh
      rw [max_eq_left (by linarith [hh.1, hh.2]), max_eq_left (by linarith [hh.1, hh.2]),
        show X ω - K - (X ω - (K + h)) = h by ring, div_self hh.1.ne']
    · rw [indicator_of_notMem (show ω ∉ {ω | K < X ω} from hω)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh : 0 < h := hh
      rw [max_eq_right (by linarith [not_lt.1 hω]), max_eq_right (by linarith [not_lt.1 hω]),
        sub_self, zero_div]

/-- **Call prices at every strike determine the law** (Breeden–Litzenberger, first order). Two
probability laws of a log-return, each with `∫ eʸ < ∞`, that give the same undiscounted call
price `∫ (Seʸ − K)⁺` at every strike `K > 0` (for one `S > 0`) are equal. The call spreads at the
strike `Seᵃ` tend to the tail `P(Y > a)` under each law (`tendsto_call_spread`), so the tails
agree, and the tails fix the law (Mathlib's `Measure.ext_of_Iic`). -/
theorem measure_eq_of_integral_call_eq {μ μ' : Measure ℝ} [IsProbabilityMeasure μ]
    [IsProbabilityMeasure μ'] {S : ℝ} (hS : 0 < S) (hμ : Integrable Real.exp μ)
    (hμ' : Integrable Real.exp μ')
    (h : ∀ K, 0 < K →
      ∫ y, max (S * Real.exp y - K) 0 ∂μ = ∫ y, max (S * Real.exp y - K) 0 ∂μ') :
    μ = μ' := by
  have hX : Measurable fun y ↦ S * Real.exp y := by fun_prop
  have htail (a : ℝ) : μ (Ioi a) = μ' (Ioi a) := by
    have hset : {y | S * Real.exp a < S * Real.exp y} = Ioi a := by
      ext y
      rw [mem_ofPred_eq, mem_Ioi, mul_lt_mul_iff_right₀ hS, Real.exp_lt_exp]
    have hlim := tendsto_call_spread hX (hμ.const_mul S) (S * Real.exp a)
    have hlim' := tendsto_call_spread hX (hμ'.const_mul S) (S * Real.exp a)
    rw [hset] at hlim hlim'
    have hK : 0 < S * Real.exp a := mul_pos hS (Real.exp_pos a)
    refine (ENNReal.toReal_eq_toReal_iff' (measure_ne_top μ _) (measure_ne_top μ' _)).1
      (tendsto_nhds_unique hlim (hlim'.congr' ?_))
    filter_upwards [self_mem_nhdsWithin] with k hk
    rw [h _ hK, h _ (add_pos hK hk)]
  refine Measure.ext_of_Iic μ μ' fun a ↦ ?_
  rw [← compl_Ioi, prob_compl_eq_one_sub measurableSet_Ioi,
    prob_compl_eq_one_sub measurableSet_Ioi, htail]

/-- **The call spread below the strike tends to the digital at or above it.** For a measurable,
integrable `X` under a finite measure `μ`, `(C(K − h) − C(K))/h → μ {X ≥ K}` as `h ↓ 0`, where
`C(k) = ∫ (X − k)⁺ dμ`: minus the left strike derivative of the call price is the price of the
event `X ≥ K`. As in `tendsto_call_spread`, the spread payoff is at most `1` in absolute value; it
is `1` when `X ≥ K` and `0` once `h < K − X`. -/
theorem tendsto_call_spread_left {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hXm : Measurable X) (hX : Integrable X μ) (K : ℝ) :
    Tendsto (fun h ↦ (∫ ω, max (X ω - (K - h)) 0 ∂μ - ∫ ω, max (X ω - K) 0 ∂μ) / h) (𝓝[>] 0)
      (𝓝 (μ.real {ω | K ≤ X ω})) := by
  have hcall (k : ℝ) : Integrable (fun ω ↦ max (X ω - k) 0) μ :=
    (hX.sub (integrable_const k)).pos_part
  have hspread : (fun h ↦ (∫ ω, max (X ω - (K - h)) 0 ∂μ - ∫ ω, max (X ω - K) 0 ∂μ) / h)
      = fun h ↦ ∫ ω, (max (X ω - (K - h)) 0 - max (X ω - K) 0) / h ∂μ := by
    funext h
    rw [integral_div, integral_sub (hcall (K - h)) (hcall K)]
  rw [hspread, ← integral_indicator_one (measurableSet_le measurable_const hXm)]
  refine tendsto_integral_filter_of_dominated_convergence (fun _ ↦ 1)
    (Eventually.of_forall fun h ↦ ?_) ?_ (integrable_const 1) (ae_of_all _ fun ω ↦ ?_)
  · exact (by fun_prop : Measurable fun ω ↦
      (max (X ω - (K - h)) 0 - max (X ω - K) 0) / h).aestronglyMeasurable
  · -- the call payoff is `1`-Lipschitz in the strike, so the spread payoff is at most `1`
    filter_upwards [self_mem_nhdsWithin] with h hh
    refine ae_of_all _ fun ω ↦ ?_
    have hh : 0 < h := hh
    have hlip := abs_call_payoff_sub_le (X ω) (K - h) K
    rw [sub_sub_cancel_left, abs_neg, abs_of_pos hh] at hlip
    change ‖(max (X ω - (K - h)) 0 - max (X ω - K) 0) / h‖ ≤ 1
    rwa [Real.norm_eq_abs, abs_div, abs_of_pos hh, div_le_one hh]
  · -- and tends to the digital payoff `1_{X ≥ K}`
    by_cases hω : K ≤ X ω
    · rw [indicator_of_mem (show ω ∈ {ω | K ≤ X ω} from hω), Pi.one_apply]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [self_mem_nhdsWithin] with h hh
      have hh : 0 < h := hh
      rw [max_eq_left (by linarith), max_eq_left (by linarith),
        show X ω - (K - h) - (X ω - K) = h by ring, div_self hh.ne']
    · rw [indicator_of_notMem (show ω ∉ {ω | K ≤ X ω} from hω)]
      refine tendsto_const_nhds.congr' ?_
      filter_upwards [Ioo_mem_nhdsGT (sub_pos.2 (not_le.1 hω))] with h hh
      rw [max_eq_right (by linarith [hh.2, not_le.1 hω]),
        max_eq_right (by linarith [hh.2, not_le.1 hω]), sub_self, zero_div]

/-- **The strike derivative of the call price is minus the digital.** For a measurable, integrable
`X` under a finite measure `μ` with no atom at `K` (`μ {X = K} = 0`), the undiscounted call price
`C(k) = ∫ (X − k)⁺ dμ` is differentiable at `K` and `C'(K) = −μ {X > K}`. The call payoff is
`1`-Lipschitz in the strike and, off the atom, differentiable at `K` with derivative `−1_{X > K}`,
so Mathlib's `hasDerivAt_integral_of_dominated_loc_of_lip` applies. -/
theorem hasDerivAt_integral_call {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hXm : Measurable X) (hX : Integrable X μ) {K : ℝ}
    (hK : μ {ω | X ω = K} = 0) :
    HasDerivAt (fun k ↦ ∫ ω, max (X ω - k) 0 ∂μ) (-μ.real {ω | K < X ω}) K := by
  have hset : MeasurableSet {ω | K < X ω} := measurableSet_lt measurable_const hXm
  have hae : ∀ᵐ ω ∂μ, X ω ≠ K := ae_iff.2 (by simpa using hK)
  rw [← integral_indicator_one hset, ← integral_neg]
  refine (hasDerivAt_integral_of_dominated_loc_of_lip (F := fun k ω ↦ max (X ω - k) 0)
    (F' := fun ω ↦ -{ω | K < X ω}.indicator 1 ω) (bound := fun _ ↦ 1) univ_mem
    (Eventually.of_forall fun k ↦ ?_) (hX.sub (integrable_const K)).pos_part
    (measurable_one.indicator hset).neg.aestronglyMeasurable
    (ae_of_all _ fun ω ↦ (LipschitzWith.of_dist_le_mul fun k₁ k₂ ↦ ?_).lipschitzOnWith)
    (integrable_const 1) ?_).2
  · exact (by fun_prop : Measurable fun ω ↦ max (X ω - k) 0).aestronglyMeasurable
  · -- the call payoff is `1`-Lipschitz in the strike
    simpa only [map_one, NNReal.coe_one, one_mul, Real.dist_eq] using
      abs_call_payoff_sub_le (X ω) k₁ k₂
  · -- and, off the atom, differentiable at `K` with derivative `−1_{X > K}`
    filter_upwards [hae] with ω hω
    rcases hω.lt_or_gt with h | h
    · rw [indicator_of_notMem (show ω ∉ {ω | K < X ω} from fun h' ↦ lt_asymm h h'), neg_zero]
      refine (hasDerivAt_const K (0 : ℝ)).congr_of_eventuallyEq ?_
      filter_upwards [Ioi_mem_nhds h] with k hk
      exact max_eq_right (by linarith [mem_Ioi.1 hk])
    · rw [indicator_of_mem (show ω ∈ {ω | K < X ω} from h), Pi.one_apply]
      refine ((hasDerivAt_id' K).const_sub (X ω)).congr_of_eventuallyEq ?_
      filter_upwards [Iio_mem_nhds h] with k hk
      exact max_eq_left (by linarith [mem_Iio.1 hk])

/-- **The call price is differentiable in the strike exactly off the atoms.** For a measurable,
integrable `X` under a finite measure `μ`, the call price `C(k) = ∫ (X − k)⁺ dμ` is
differentiable at `K` iff `X` has no atom at `K`. Off an atom this is `hasDerivAt_integral_call`.
Conversely the right slopes tend to `−μ {X > K}` (`tendsto_call_spread`) and the left ones to
`−μ {X ≥ K}` (`tendsto_call_spread_left`), so a derivative makes the two equal, and they differ by
`μ {X = K}`. -/
theorem differentiableAt_integral_call_iff {Ω : Type*} {mΩ : MeasurableSpace Ω} {μ : Measure Ω}
    [IsFiniteMeasure μ] {X : Ω → ℝ} (hXm : Measurable X) (hX : Integrable X μ) (K : ℝ) :
    DifferentiableAt ℝ (fun k ↦ ∫ ω, max (X ω - k) 0 ∂μ) K ↔ μ {ω | X ω = K} = 0 := by
  refine ⟨fun hd ↦ ?_, fun hK ↦ (hasDerivAt_integral_call hXm hX hK).differentiableAt⟩
  have h := hd.hasDerivAt
  have hneg : Tendsto (fun t : ℝ ↦ -t) (𝓝[>] 0) (𝓝[<] 0) := by
    simpa only [neg_zero] using tendsto_neg_nhdsGT (a := (0 : ℝ))
  -- the right slopes tend to `−μ {X > K}`, the left ones to `−μ {X ≥ K}`
  have hR := tendsto_nhds_unique h.tendsto_slope_zero_right
    ((tendsto_call_spread hXm hX K).neg.congr' (Eventually.of_forall fun t ↦ by
      simp only [smul_eq_mul]
      ring))
  have hL := tendsto_nhds_unique (h.tendsto_slope_zero_left.comp hneg)
    ((tendsto_call_spread_left hXm hX K).neg.congr' (Eventually.of_forall fun t ↦ by
      simp only [Function.comp_apply, smul_eq_mul, ← sub_eq_add_neg]
      ring))
  -- `{X ≥ K}` is `{X > K}` and the atom
  have hunion : {ω | K ≤ X ω} = {ω | K < X ω} ∪ {ω | X ω = K} :=
    Set.ext fun ω ↦ (le_iff_lt_or_eq (a := K) (b := X ω)).trans (or_congr_right eq_comm)
  have hsum := measureReal_union (μ := μ) (s₁ := {ω | K < X ω}) (s₂ := {ω | X ω = K})
    (Set.disjoint_left.2 fun ω (h₁ : K < X ω) (h₂ : X ω = K) ↦ h₁.ne' h₂)
    (hXm (measurableSet_singleton K))
  rw [← hunion] at hsum
  exact (measureReal_eq_zero_iff (measure_ne_top μ _)).1 (by linarith)

end MathFin
