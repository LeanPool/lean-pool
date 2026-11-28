/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import Mathlib.Analysis.Convex.Continuous
public import Mathlib.Analysis.Convex.Deriv
public import Mathlib.MeasureTheory.Integral.Layercake
public import LeanPool.MathFin.Models.ModelFree.MarketCallPrice
public import LeanPool.MathFin.Pricing.OneDateMarket

/-!
# Roper's converse: a market for every normalised call price function

Every normalised call price function (`IsNormalizedCallPrice`) is the call price function of a
market. The first half builds the law (Breeden–Litzenberger): the right derivative `C'₊` of a
convex `C` is monotone and right-continuous, so `K ↦ 1 + C'₊ K` on `(0, ∞)`, extended by `0`,
is, up to its right limit at `0`, the distribution function of a probability measure `μ` on
`[0, ∞)` with `μ (Ioi K) = -C'₊ K`. The layer-cake formula and the fundamental theorem of
calculus for the right derivative give `∫ (x - K)⁺ dμ = C K`, and monotone convergence as
`K ↓ 0` gives the mean `∫ x dμ = 1`. The second half puts `μ` in the one-date market
(`Market.oneDate`) with unit numéraire and the asset `max ω 0` at time one, priced by `μ` itself.

The asset is nonnegative, not positive: a call price function may carry an atom at `0` (for
`C K = max (1 - (1 - p) K) 0` with `p ∈ (0, 1)` the law has mass `p` at `0`), and no pricing
measure equivalent to the reference measure gives a strictly positive asset zero mass, so the
version with `0 < M.asset () 1 ω` is false. The forward direction, from a market with a positive
asset to a call price function, is `Market.IsPricingMeasure.isNormalizedCallPrice`.

## Main results

* `ConvexOn.continuousWithinAt_Ici_rightDeriv`: the right derivative of a convex function on an
  open set is right-continuous.
* `IsNormalizedCallPrice.exists_measure`: a normalised call price function is `K ↦ ∫ (x - K)⁺ dμ`
  for a probability measure `μ` on `[0, ∞)` of mean one.
* `exists_market_of_isNormalizedCallPrice`: **Roper's converse.** A market with unit numéraire,
  a nonnegative asset of forward one at time one and a pricing measure, under which the claim
  paying the asset is worth `1` and the call at every strike `K > 0` is worth `C K`.

## References

* [Roper, *Arbitrage free implied volatility surfaces*][Roper2010], Theorem 2.1
* [Breeden and Litzenberger, *Prices of state-contingent claims implicit in option
  prices*][BreedenLitzenberger1978]

## Tags

call price in strike, Breeden-Litzenberger, risk-neutral density, right derivative,
Stieltjes measure, MSC 91G20, JEL G13
-/

@[expose] public section

open Set Filter Topology MeasureTheory

namespace ConvexOn

variable {S : Set ℝ} {f : ℝ → ℝ}

/-- **The right derivative of a convex function on an open set is right-continuous.** Fix `b`
above `f'₊ x`: some slope `slope f x z` is below `b`, and `f'₊ y ≤ slope f y z`, which tends to
`slope f x z` as `y ↓ x`; the other bound is the monotonicity of `f'₊`. -/
theorem continuousWithinAt_Ici_rightDeriv (hfc : ConvexOn ℝ S f) (hS : IsOpen S) {x : ℝ}
    (hx : x ∈ S) : ContinuousWithinAt (fun y ↦ derivWithin f (Ioi y) y) (Ici x) x := by
  rw [← continuousWithinAt_Ioi_iff_Ici]
  have hxi : x ∈ interior S := hS.interior_eq.ge hx
  have hS' : ∀ᶠ y in 𝓝[>] x, y ∈ S := nhdsWithin_le_nhds (hS.mem_nhds hx)
  refine tendsto_order.2 ⟨fun a ha ↦ ?_, fun b hb ↦ ?_⟩
  · filter_upwards [self_mem_nhdsWithin, hS'] with y hy hyS
    exact ha.trans_le (hfc.monotoneOn_rightDeriv hxi (hS.interior_eq.ge hyS) hy.le)
  · obtain ⟨z₀, hz₀S, hz₀⟩ := (hS'.and self_mem_nhdsWithin).exists
    replace hb : derivWithin f (Ioi x) x < b := hb
    rw [hfc.rightDeriv_eq_sInf_slope_of_mem_interior hxi] at hb
    obtain ⟨_, ⟨z, ⟨hzS, hxz⟩, rfl⟩, hzb⟩ :=
      exists_lt_of_csInf_lt (s := slope f x '' {y | y ∈ S ∧ x < y})
        ⟨_, z₀, ⟨hz₀S, hz₀⟩, rfl⟩ hb
    have hlim : Tendsto (fun y ↦ slope f y z) (𝓝 x) (𝓝 (slope f x z)) := by
      simp only [slope_def_field]
      exact ((continuousAt_const.sub ((hfc.continuousOn hS).continuousAt (hS.mem_nhds hx))).div
        (continuousAt_const.sub continuousAt_id) (sub_ne_zero.2 hxz.ne')).tendsto
    filter_upwards [hlim.mono_left nhdsWithin_le_nhds |>.eventually (gt_mem_nhds hzb), hS',
      nhdsWithin_le_nhds (eventually_lt_nhds hxz)] with y hy hyS hyz
    exact (hfc.rightDeriv_le_slope_of_mem_interior (hS.interior_eq.ge hyS) hzS hyz).trans_lt hy

end ConvexOn

namespace MathFin.IsNormalizedCallPrice

variable {C : ℝ → ℝ} (hC : IsNormalizedCallPrice C)
include hC

/-- A secant slope of a normalised call price function is at most the right derivative at its
right end. -/
theorem slope_le_rightDeriv {a x : ℝ} (ha : 0 < a) (hax : a < x) :
    slope C a x ≤ derivWithin C (Ioi x) x :=
  (hC.convexOn.slope_le_leftDeriv_of_mem_interior ha (by simpa using ha.trans hax) hax).trans
    (hC.convexOn.leftDeriv_le_rightDeriv_of_mem_interior (by simpa using ha.trans hax))

/-- A normalised call price function has nonpositive right derivative: it is nonincreasing. -/
theorem rightDeriv_nonpos {x : ℝ} (hx : 0 < x) : derivWithin C (Ioi x) x ≤ 0 := by
  have hy : x + 1 ∈ Ioi (0 : ℝ) := by simp; linarith
  refine (hC.convexOn.rightDeriv_le_slope_of_mem_interior (by simpa using hx) hy
    (lt_add_one x)).trans ?_
  rw [slope_def_field]
  exact div_nonpos_of_nonpos_of_nonneg (sub_nonpos.2 (hC.antitoneOn hx hy (by simp)))
    (by simp)

/-- The right derivative of a normalised call price function is at least `-1`: the secant from
strike `0⁺`, where the price is `1`, to `x` has slope `(C x - 1) / x ≥ -1`. -/
theorem neg_one_le_rightDeriv {x : ℝ} (hx : 0 < x) : -1 ≤ derivWithin C (Ioi x) x := by
  have hlim : Tendsto (fun a ↦ slope C a x) (𝓝[>] 0) (𝓝 ((C x - 1) / (x - 0))) := by
    simp only [slope_def_field]
    exact (tendsto_const_nhds.sub hC.tendsto_one).div
      ((tendsto_const_nhds.sub tendsto_id).mono_left nhdsWithin_le_nhds) (by simpa using hx.ne')
  refine le_trans ?_ (le_of_tendsto hlim ?_)
  · rw [sub_zero, le_div_iff₀ hx]
    linarith [(le_max_left _ _).trans (hC.intrinsic_le x hx)]
  · filter_upwards [Ioo_mem_nhdsGT hx] with a ha using hC.slope_le_rightDeriv ha.1 ha.2

/-- The right derivative of a normalised call price function tends to `0` at infinity: it lies
between `0` and the secant slope from strike `1`, which is at least `-C 1 / (x - 1)`. -/
theorem tendsto_rightDeriv_atTop : Tendsto (fun x ↦ derivWithin C (Ioi x) x) atTop (𝓝 0) := by
  have hl : Tendsto (fun x : ℝ ↦ -C 1 / (x - 1)) atTop (𝓝 0) := by
    simpa [sub_eq_add_neg] using (tendsto_const_nhds (x := -C 1)).div_atTop
      (tendsto_atTop_add_const_right atTop (-1) tendsto_id)
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hl tendsto_const_nhds ?_ ?_
  · filter_upwards [eventually_gt_atTop 1] with x hx
    refine le_trans ?_ (hC.slope_le_rightDeriv one_pos hx)
    rw [slope_def_field]
    exact div_le_div_of_nonneg_right
      (by linarith [(le_max_right _ _).trans (hC.intrinsic_le x (by simp; linarith))])
      (by linarith)
  · filter_upwards [eventually_gt_atTop 0] with x hx using hC.rightDeriv_nonpos hx

/-- The right derivative of a normalised call price function is monotone on `(0, ∞)`. -/
theorem monotoneOn_rightDeriv : MonotoneOn (fun x ↦ derivWithin C (Ioi x) x) (Ioi 0) := by
  simpa using hC.convexOn.monotoneOn_rightDeriv

/-- The fundamental theorem of calculus for the right derivative of a normalised call price
function. -/
theorem intervalIntegral_rightDeriv {K b : ℝ} (hK : 0 < K) (hKb : K ≤ b) :
    ∫ y in K..b, derivWithin C (Ioi y) y = C b - C K := by
  refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hKb
    ((hC.convexOn.continuousOn isOpen_Ioi).mono fun y hy ↦ hK.trans_le hy.1)
    (fun x hx ↦ hC.convexOn.hasDerivWithinAt_rightDeriv_of_mem_interior
      (by simpa using hK.trans hx.1)) ?_
  refine MonotoneOn.intervalIntegrable ?_
  rw [uIcc_of_le hKb]
  exact hC.monotoneOn_rightDeriv.mono fun y hy ↦ hK.trans_le hy.1

/-- **The tail integral of the right derivative.** `-C'₊` is integrable on `(K, ∞)` with integral
`C K`, stated on `(0, ∞)` after the shift `t ↦ K + t`: the integral up to `b` is
`C K - C (K + b)`, and `C` tends to `0`. -/
theorem integral_neg_rightDeriv {K : ℝ} (hK : 0 < K) :
    IntegrableOn (fun t ↦ -derivWithin C (Ioi (K + t)) (K + t)) (Ioi 0) ∧
      ∫ t in Ioi 0, -derivWithin C (Ioi (K + t)) (K + t) = C K := by
  set g : ℝ → ℝ := fun t ↦ -derivWithin C (Ioi (K + t)) (K + t) with hg
  have hg0 {t : ℝ} (ht : 0 ≤ t) : 0 ≤ g t := neg_nonneg.2 (hC.rightDeriv_nonpos (by linarith))
  have hgint {b : ℝ} (hb : 0 ≤ b) : IntervalIntegrable g volume 0 b := by
    refine AntitoneOn.intervalIntegrable ?_
    rw [uIcc_of_le hb]
    intro s hs t ht hst
    exact neg_le_neg (hC.monotoneOn_rightDeriv (by simp only [mem_Ioi]; linarith [hs.1])
      (by simp only [mem_Ioi]; linarith [ht.1]) (by linarith))
  have hFTC {b : ℝ} (hb : 0 ≤ b) : ∫ t in (0 : ℝ)..b, g t = C K - C (K + b) := by
    have := intervalIntegral.integral_comp_add_left
      (fun y ↦ derivWithin C (Ioi y) y) (a := 0) (b := b) K
    simp only [hg, intervalIntegral.integral_neg, this, add_zero]
    rw [hC.intervalIntegral_rightDeriv hK (by linarith)]
    ring
  have hint : IntegrableOn g (Ioi 0) := by
    refine integrableOn_Ioi_of_intervalIntegral_norm_bounded (C K) 0
      (fun b ↦ ?_) (l := atTop) (b := id) tendsto_id ?_
    · change IntegrableOn g (Ioc 0 b)
      by_cases hb : 0 ≤ b
      · exact (intervalIntegrable_iff_integrableOn_Ioc_of_le hb).1 (hgint hb)
      · rw [Ioc_eq_empty (not_lt.2 (not_le.1 hb).le)]
        exact integrableOn_empty
    · filter_upwards [eventually_ge_atTop 0] with i hi
      change ∫ t in (0 : ℝ)..i, ‖g t‖ ≤ C K
      have : ∫ t in (0 : ℝ)..i, ‖g t‖ = ∫ t in (0 : ℝ)..i, g t :=
        intervalIntegral.integral_congr fun t ht ↦ by
          rw [uIcc_of_le hi] at ht
          exact Real.norm_of_nonneg (hg0 ht.1)
      rw [this, hFTC hi]
      have := (le_max_right _ _).trans (hC.intrinsic_le (K + i) (by simp only [mem_Ioi]; linarith))
      linarith
  refine ⟨hint, tendsto_nhds_unique
    (intervalIntegral_tendsto_integral_Ioi 0 hint (tendsto_id : Tendsto id atTop atTop)) ?_⟩
  have h := tendsto_const_nhds (x := C K) |>.sub
    (hC.tendsto_zero.comp (tendsto_atTop_add_const_left atTop K tendsto_id))
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [eventually_ge_atTop 0] with i hi
  exact (hFTC hi).symm

/-- **The Breeden–Litzenberger measure, by its tails.** A probability measure on `[0, ∞)` whose
upper tail at `y > 0` is `-C'₊ y`: the Stieltjes measure of the right limit of the monotone
function `K ↦ 1 + C'₊ K` on `(0, ∞)`, `0` elsewhere. -/
theorem exists_measure_tail :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Iio 0) = 0 ∧
      ∀ y > 0, μ (Ioi y) = ENNReal.ofReal (-derivWithin C (Ioi y) y) := by
  set f : ℝ → ℝ := fun K ↦ if 0 < K then 1 + derivWithin C (Ioi K) K else 0 with hf
  have hf0 (K : ℝ) : 0 ≤ f K := by
    by_cases hK : 0 < K
    · simp only [hf, hK, ↓reduceIte]; linarith [hC.neg_one_le_rightDeriv hK]
    · simp [hf, hK]
  have hmono : Monotone f := by
    intro a b hab
    by_cases ha : 0 < a
    · have hb : 0 < b := ha.trans_le hab
      simp only [hf, ha, hb, ↓reduceIte]
      linarith [hC.monotoneOn_rightDeriv ha hb hab]
    · rw [show f a = 0 by simp [hf, ha]]
      exact hf0 b
  set G := hmono.stieltjesFunction with hG
  have hGf (x : ℝ) : f x ≤ G x := hmono.le_rightLim le_rfl
  have hGpos {x : ℝ} (hx : 0 < x) : G x = 1 + derivWithin C (Ioi x) x := by
    have hcont : ContinuousWithinAt f (Ioi x) x := by
      refine (continuousWithinAt_const (b := (1 : ℝ)) |>.add
        ((hC.convexOn.continuousWithinAt_Ici_rightDeriv isOpen_Ioi hx).mono
          Ioi_subset_Ici_self)).congr_of_eventuallyEq ?_ (by simp [hf, hx])
      filter_upwards [eventually_gt_nhds hx |>.filter_mono nhdsWithin_le_nhds] with y hy
      simp [hf, hy]
    exact (hmono.continuousWithinAt_Ioi_iff_rightLim_eq.1 hcont).trans (by simp [hf, hx])
  have hGneg {x : ℝ} (hx : x < 0) : G x = 0 := by
    refine rightLim_eq_of_tendsto ?_
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_lt_nhds hx |>.filter_mono nhdsWithin_le_nhds] with y hy
    simp [hf, not_lt.2 hy.le]
  have hbot : Tendsto G atBot (𝓝 0) :=
    tendsto_const_nhds.congr' (by filter_upwards [eventually_lt_atBot 0] with x hx using
      (hGneg hx).symm)
  have htop : Tendsto G atTop (𝓝 1) := by
    have := (tendsto_const_nhds (x := (1 : ℝ))).add hC.tendsto_rightDeriv_atTop
    rw [add_zero] at this
    exact this.congr' (by filter_upwards [eventually_gt_atTop 0] with x hx using
      (hGpos hx).symm)
  have : IsProbabilityMeasure G.measure := G.isProbabilityMeasure hbot htop
  refine ⟨G.measure, this, ?_, fun y hy ↦ ?_⟩
  · have hleft : Function.leftLim G 0 = 0 :=
      leftLim_eq_of_tendsto (tendsto_const_nhds.congr'
        (by filter_upwards [self_mem_nhdsWithin] with x (hx : x < 0) using (hGneg hx).symm))
    rw [G.measure_Iio hbot, hleft]
    simp
  · rw [G.measure_Ioi htop, hGpos hy]
    congr 1
    ring

/-- **Layer cake for the call.** A measure with upper tail `-C'₊` prices the call at `K > 0` at
`C K`: `μ {t < (x - K)⁺} = μ (Ioi (K + t)) = -C'₊ (K + t)`, integrated over `t > 0`. -/
theorem lintegral_call_of_tail {μ : Measure ℝ}
    (htail : ∀ y > 0, μ (Ioi y) = ENNReal.ofReal (-derivWithin C (Ioi y) y)) {K : ℝ} (hK : 0 < K) :
    ∫⁻ x, ENNReal.ofReal (max (x - K) 0) ∂μ = ENNReal.ofReal (C K) := by
  rw [lintegral_eq_lintegral_meas_lt μ (f := fun x : ℝ ↦ max (x - K) 0)
    (ae_of_all _ fun x ↦ le_max_right _ _)
    (by fun_prop : Measurable fun x : ℝ ↦ max (x - K) 0).aemeasurable]
  have hset (t : ℝ) (ht : t ∈ Ioi (0 : ℝ)) : μ {a | t < max (a - K) 0}
      = ENNReal.ofReal (-derivWithin C (Ioi (K + t)) (K + t)) := by
    have ht' : 0 < t := ht
    have : {a : ℝ | t < max (a - K) 0} = Ioi (K + t) := by
      ext a
      simp only [mem_ofPred_eq, mem_Ioi, lt_max_iff]
      constructor
      · rintro (h | h) <;> linarith
      · intro h
        exact .inl (by linarith)
    rw [this, htail _ (by linarith)]
  rw [setLIntegral_congr_fun measurableSet_Ioi hset]
  obtain ⟨hint, hval⟩ := hC.integral_neg_rightDeriv hK
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))]
      fun t ↦ -derivWithin C (Ioi (K + t)) (K + t) :=
    (ae_restrict_iff' measurableSet_Ioi).2 (ae_of_all _ fun t ht ↦
      neg_nonneg.2 (hC.rightDeriv_nonpos (by have : 0 < t := ht; linarith)))
  rw [← ofReal_integral_eq_lintegral_ofReal hint hnn, hval]

/-- **Every normalised call price function is the call price function of a law.** There is a
probability measure `μ` on `[0, ∞)` with finite mean one such that `C K = ∫ (x - K)⁺ dμ` for
every `K > 0`. The mean is the limit of the calls at `K ↓ 0` (monotone convergence), and the law
need not be supported on `(0, ∞)`: it has an atom at `0` of mass `1 + C'₊ (0⁺)`. -/
theorem exists_measure :
    ∃ μ : Measure ℝ, IsProbabilityMeasure μ ∧ μ (Iio 0) = 0 ∧ Integrable id μ ∧
      ∫ x, x ∂μ = 1 ∧ ∀ K > 0, ∫ x, max (x - K) 0 ∂μ = C K := by
  obtain ⟨μ, hprob, hneg, htail⟩ := hC.exists_measure_tail
  have hae : 0 ≤ᵐ[μ] fun x : ℝ ↦ x :=
    (measure_eq_zero_iff_ae_notMem.1 hneg).mono fun x hx ↦ not_lt.1 hx
  have hCnn {K : ℝ} (hK : 0 < K) : 0 ≤ C K := (le_max_right _ _).trans (hC.intrinsic_le K hK)
  have hmean : ∫⁻ x, ENNReal.ofReal x ∂μ = 1 := by
    have hlim : Tendsto (fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (max (x - 1 / (n + 1)) 0) ∂μ) atTop
        (𝓝 (∫⁻ x, ENNReal.ofReal x ∂μ)) := by
      refine lintegral_tendsto_of_tendsto_of_monotone
        (fun n ↦ (by fun_prop : Measurable fun x : ℝ ↦
          ENNReal.ofReal (max (x - 1 / (n + 1)) 0)).aemeasurable) ?_ ?_
      · refine ae_of_all _ fun x n m hnm ↦ ENNReal.ofReal_le_ofReal (max_le_max
          (sub_le_sub_left (one_div_le_one_div_of_le (by positivity) ?_) x) le_rfl)
        exact_mod_cast Nat.add_le_add_right hnm 1
      · filter_upwards [hae] with x hx
        have := ENNReal.tendsto_ofReal ((tendsto_const_nhds (x := x)).sub
          tendsto_one_div_add_atTop_nhds_zero_nat |>.max (tendsto_const_nhds (x := (0 : ℝ))))
        simpa [max_eq_left (show 0 ≤ x from hx)] using this
    have hlim' : Tendsto (fun n : ℕ ↦ ∫⁻ x, ENNReal.ofReal (max (x - 1 / (n + 1)) 0) ∂μ) atTop
        (𝓝 (ENNReal.ofReal 1)) := by
      refine (ENNReal.tendsto_ofReal (hC.tendsto_one.comp (tendsto_nhdsWithin_iff.2
        ⟨tendsto_one_div_add_atTop_nhds_zero_nat, .of_forall fun n ↦ ?_⟩))).congr fun n ↦ ?_
      · exact (by positivity : (0 : ℝ) < 1 / (n + 1))
      · exact (hC.lintegral_call_of_tail htail (by positivity)).symm
    rw [tendsto_nhds_unique hlim hlim', ENNReal.ofReal_one]
  refine ⟨μ, hprob, hneg, ⟨aestronglyMeasurable_id,
    (hasFiniteIntegral_iff_ofReal (f := fun x : ℝ ↦ x) hae).2
      (by rw [hmean]; exact ENNReal.one_lt_top)⟩, ?_, fun K hK ↦ ?_⟩
  · rw [integral_eq_lintegral_of_nonneg_ae hae aestronglyMeasurable_id, hmean]
    simp
  · rw [integral_eq_lintegral_of_nonneg_ae (f := fun x : ℝ ↦ max (x - K) 0)
      (ae_of_all _ fun x ↦ le_max_right _ _)
      (by fun_prop : Measurable fun x : ℝ ↦ max (x - K) 0).aestronglyMeasurable,
      hC.lintegral_call_of_tail htail hK, ENNReal.toReal_ofReal (hCnn hK)]

end MathFin.IsNormalizedCallPrice

namespace MathFin

open MathFin.Contracts
open scoped NNReal

/-- **Roper's converse.** Every normalised call price function is the call price function of a
market with unit numéraire, a nonnegative asset of forward one at time one and a pricing measure:
the claim paying the asset is worth `1` and the call at every strike `k > 0` is worth `C k`. The
asset is `max ω 0` on `ℝ`, and the pricing measure is the law of
`IsNormalizedCallPrice.exists_measure`, which is also the reference measure. The asset can vanish:
the version with a strictly positive asset is false for a call price function with an atom
at `0`. -/
theorem exists_market_of_isNormalizedCallPrice {C : ℝ → ℝ} (hC : IsNormalizedCallPrice C) :
    ∃ (M : Market Unit ℝ) (Q : Measure ℝ), (∀ t ω, M.numeraire t ω = 1) ∧
      (∀ ω, 0 ≤ M.asset () 1 ω) ∧ M.IsPricingMeasure 1 Q ∧
      M.price Q (.pay 1 (.obs () 1)) = 1 ∧ ∀ k > 0, M.price Q (europeanCall k 1) = C k := by
  obtain ⟨μ, hprob, hneg, hint, hmean, hcall⟩ := hC.exists_measure
  have hX : Measurable fun ω : ℝ ↦ max ω 0 := by fun_prop
  have hae : ∀ᵐ ω ∂μ, max ω 0 = ω :=
    (measure_eq_zero_iff_ae_notMem.1 hneg).mono fun x hx ↦ max_eq_left (not_lt.1 hx)
  have hXint : Integrable (fun ω : ℝ ↦ max ω 0) μ := hint.pos_part
  have hXmean : ∫ ω, max ω 0 ∂μ = 1 := by
    rw [integral_congr_ae hae, hmean]
  set M := Market.oneDate μ hX 1 0 1 with hM
  have hnum : ∀ t ω, M.numeraire t ω = 1 := fun t ω ↦ by simp [hM, Market.oneDate]
  refine ⟨M, μ, hnum, fun ω ↦ ?_, ?_, ?_, fun k hk ↦ ?_⟩
  · rw [hM, Market.asset_oneDate_self]
    exact le_max_right _ _
  · exact Market.isPricingMeasure_oneDate Measure.AbsolutelyContinuous.rfl
      Measure.AbsolutelyContinuous.rfl hXint (by simpa using hXmean)
  · simpa [hM, Market.price_pay_obs_oneDate] using hXmean
  · rw [hM, Market.price_europeanCall_oneDate, ← hcall k hk]
    simp only [neg_zero, zero_mul, Real.exp_zero, one_mul]
    refine integral_congr_ae (.of_forall fun ω ↦ ?_)
    rcases le_total ω 0 with h | h
    · simp [max_eq_right h, hk.le, h.trans hk.le]
    · simp [max_eq_left h]

end MathFin
