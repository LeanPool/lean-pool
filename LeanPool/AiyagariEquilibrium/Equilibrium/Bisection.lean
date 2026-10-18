/-
Copyright (c) 2026 Robert Kirkby. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert Kirkby
-/

module
public import LeanPool.AiyagariEquilibrium.Equilibrium.AiyagariUniqueness


/-!
# Bisection finds the equilibrium rate, and the log Aiyagari instance

Aiyagari (1994) computed his equilibrium by bisection on the interest rate: evaluate excess
supply at the midpoint of a bracket and keep the half on which it still changes sign. Hajek and
Livesay (2019) ask, for mean field games, which equilibria are STABLE fixed points of the
best-response map; for the Bewley model the raw best-response iteration `r ↦ r_d(K_s(r))` has
negative slope and may oscillate, so the algorithm that is certified here is the bisection.

## The abstract statement

`bisect f a b n` is the bracket after `n` steps. If `f` is STRICTLY MONOTONE on `[a, b]` and
vanishes at `r ∈ [a, b]`, then every bracket contains `r` (`bisect_mem_of_strictMonoOn`), the
width halves each step (`bisect_width`), and the endpoints converge to `r`
(`tendsto_bisect_fst`). No continuity and no sign condition at the ends are used: strict
monotonicity alone decides which half the zero is in. The midpoint after `n` steps is within
`(b - a)/2^(n+1)` of `r` (`abs_bisect_mid_sub_le`).

## The instance

For Aiyagari's log calibration the supply schedule along any selection of stationary
distributions is monotone (`log_monotoneOn_capitalSupply`) and Cobb--Douglas demand is strictly
decreasing, so excess supply is strictly increasing. `aiyagari1994_log_bisection` therefore says:
whatever equilibrium rate there is on `[rlo, rhi] ⊂ (-δ, λ)`, the bisection on excess supply
brackets it at every step and converges to it — the numerical procedure is certified to find the
rate that `aiyagari1994_log_equilibriumRate_unique` says is the only one.
-/

@[expose] public section

open Set Filter Topology Function MeasureTheory

namespace LeanEconomics

/-! ### Bisection on the line -/

/-- One bisection step on a bracket `(a, b)`: if `f ≤ 0` at the midpoint the zero of an
increasing `f` is to the right, so keep `(mid, b)`; otherwise keep `(a, mid)`. -/
noncomputable def bisectStep (f : ℝ → ℝ) (p : ℝ × ℝ) : ℝ × ℝ :=
  if f ((p.1 + p.2) / 2) ≤ 0 then ((p.1 + p.2) / 2, p.2) else (p.1, (p.1 + p.2) / 2)

/-- The bracket after `n` bisection steps from `(a, b)`. -/
noncomputable def bisect (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) : ℝ × ℝ := (bisectStep f)^[n] (a, b)

theorem bisect_succ (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    bisect f a b (n + 1) = bisectStep f (bisect f a b n) :=
  iterate_succ_apply' _ _ _

theorem bisectStep_width (f : ℝ → ℝ) (p : ℝ × ℝ) :
    (bisectStep f p).2 - (bisectStep f p).1 = (p.2 - p.1) / 2 := by
  unfold bisectStep
  split_ifs <;> simp only <;> ring

/-- **The bracket halves at every step.** -/
theorem bisect_width (f : ℝ → ℝ) (a b : ℝ) (n : ℕ) :
    (bisect f a b n).2 - (bisect f a b n).1 = (b - a) / 2 ^ n := by
  induction n with
  | zero => simp [bisect]
  | succ k ih => rw [bisect_succ, bisectStep_width, ih, pow_succ, div_div]

/-- **Every bracket contains the zero of a strictly increasing function**, and stays inside the
initial bracket. -/
theorem bisect_mem_of_strictMonoOn {f : ℝ → ℝ} {a b r : ℝ} (hf : StrictMonoOn f (Icc a b))
    (hr : r ∈ Icc a b) (hfr : f r = 0) (n : ℕ) :
    a ≤ (bisect f a b n).1 ∧ (bisect f a b n).2 ≤ b ∧
      r ∈ Icc (bisect f a b n).1 (bisect f a b n).2 := by
  induction n with
  | zero => exact ⟨le_rfl, le_rfl, hr⟩
  | succ k ih =>
    obtain ⟨ha, hb, hr1, hr2⟩ := ih
    rw [bisect_succ]
    set p := bisect f a b k with hp
    have hm1 : p.1 ≤ (p.1 + p.2) / 2 := by linarith
    have hm2 : (p.1 + p.2) / 2 ≤ p.2 := by linarith
    have hmem : (p.1 + p.2) / 2 ∈ Icc a b := ⟨by linarith, by linarith⟩
    unfold bisectStep
    split_ifs with h
    · -- `f ≤ 0` at the midpoint: the zero is at or to the right of it
      refine ⟨by linarith, hb, ?_, hr2⟩
      by_contra hlt
      push Not at hlt
      have := hf hr hmem hlt
      linarith
    · -- `0 < f` at the midpoint: the zero is at or to the left of it
      push Not at h
      refine ⟨ha, by linarith, hr1, ?_⟩
      by_contra hlt
      push Not at hlt
      have := hf hmem hr hlt
      linarith

/-- **The midpoint after `n` steps is within `(b - a)/2^(n+1)` of the zero.** -/
theorem abs_bisect_mid_sub_le {f : ℝ → ℝ} {a b r : ℝ} (hf : StrictMonoOn f (Icc a b))
    (hr : r ∈ Icc a b) (hfr : f r = 0) (n : ℕ) :
    |((bisect f a b n).1 + (bisect f a b n).2) / 2 - r| ≤ (b - a) / 2 ^ (n + 1) := by
  obtain ⟨-, -, h1, h2⟩ := bisect_mem_of_strictMonoOn hf hr hfr n
  have hw := bisect_width f a b n
  rw [abs_le, pow_succ, ← div_div]
  constructor <;> linarith

/-- The bracket width tends to zero. -/
theorem tendsto_bisect_width (a b : ℝ) :
    Tendsto (fun n : ℕ => (b - a) / 2 ^ n) atTop (𝓝 0) := by
  have h := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
    (by norm_num : (1 / 2 : ℝ) < 1)).const_mul (b - a)
  rw [mul_zero] at h
  refine h.congr fun n => ?_
  rw [one_div_pow, div_eq_mul_one_div (b - a)]

/-- **The left endpoints converge to the zero.** -/
theorem tendsto_bisect_fst {f : ℝ → ℝ} {a b r : ℝ} (hf : StrictMonoOn f (Icc a b))
    (hr : r ∈ Icc a b) (hfr : f r = 0) :
    Tendsto (fun n => (bisect f a b n).1) atTop (𝓝 r) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (tendsto_bisect_width a b)
  obtain ⟨-, -, h1, h2⟩ := bisect_mem_of_strictMonoOn hf hr hfr n
  have hw := bisect_width f a b n
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- **The right endpoints converge to the zero.** -/
theorem tendsto_bisect_snd {f : ℝ → ℝ} {a b r : ℝ} (hf : StrictMonoOn f (Icc a b))
    (hr : r ∈ Icc a b) (hfr : f r = 0) :
    Tendsto (fun n => (bisect f a b n).2) atTop (𝓝 r) := by
  rw [tendsto_iff_dist_tendsto_zero]
  refine squeeze_zero (fun n => dist_nonneg) (fun n => ?_) (tendsto_bisect_width a b)
  obtain ⟨-, -, h1, h2⟩ := bisect_mem_of_strictMonoOn hf hr hfr n
  have hw := bisect_width f a b n
  rw [Real.dist_eq, abs_le]
  constructor <;> linarith

/-- Monotone supply minus strictly decreasing demand is strictly increasing. -/
theorem strictMonoOn_sub_of_monotoneOn_of_strictAntiOn {S D : ℝ → ℝ} {s : Set ℝ}
    (hS : MonotoneOn S s) (hD : StrictAntiOn D s) : StrictMonoOn (fun r => S r - D r) s :=
  fun x hx y hy hxy => by
  have := hS hx hy hxy.le
  have := hD hx hy hxy
  simp only
  linarith

/-! ### The log Aiyagari instance -/

namespace IncomeFluctuation

variable {Z : Type*} [Fintype Z] [Nonempty Z] [TopologicalSpace Z] [DiscreteTopology Z]
variable [MeasurableSpace Z] [BorelSpace Z]
variable {assetCap : ℝ} (P : IncomeFluctuation Z 0 assetCap)

/-- **Excess supply along a selection of stationary distributions**: capital supplied under
`ν r` minus capital demanded at `r`. -/
noncomputable def excessSupply (ν : ℝ → ProbabilityMeasure P.State) (D : ℝ → ℝ) (r : ℝ) : ℝ :=
  P.aggregateCapital (ν r) - D r

/-- The two facts about a selection that the bisection needs, from one inequality on the cap:
supply along it is monotone, and it is the ONLY stationary distribution at each rate. The
constants are chosen as in `log_equilibriumRate_unique_of_cap`. -/
theorem log_selection_of_cap {rlo rhi : ℝ}
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβ : 0 < (P.discount : ℝ)) (hβ1 : (P.discount : ℝ) < 1) (hrlo : 0 < 1 + rlo)
    (hlohi : rlo ≤ rhi) (hβR : (P.discount : ℝ) * (1 + rhi) < 1)
    (hcap : 2 * (P.discount : ℝ) * P.maxIncome < (1 - (P.discount : ℝ) * (1 + rhi)) * assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hmin : P.income z₀ = P.minIncome) (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    (ν : ℝ → ProbabilityMeasure P.State)
    (hν : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).IsStationary (ν r)) :
    MonotoneOn (fun r => P.aggregateCapital (ν r)) (Icc rlo rhi) ∧
      ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, ∀ μ : ProbabilityMeasure P.State,
        (P.withRate r hrr).IsStationary μ → μ = ν r := by
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
  set ε : ℝ := (1 - β * R) / 2 with hεdef
  have hε : 0 < ε := by rw [hεdef]; linarith
  set A : ℝ := P.minIncome * (1 - β * R) / (2 * β * R ^ 2) with hAdef
  have hA : 0 < A := by rw [hAdef]; positivity
  set a₀ : ℝ := min assetCap A with ha₀def
  have ha₀ : 0 < a₀ := lt_min hcap0 hA
  have hle : a₀ ≤ assetCap := min_le_left _ _
  have ha₀A : a₀ ≤ A := min_le_right _ _
  have hcapε : β * P.maxIncome + (β * R + ε) * assetCap < assetCap := by
    rw [hεdef]
    nlinarith [hcap]
  have hcap' : β * (P.maxIncome + R * assetCap) < assetCap := by
    nlinarith [hcap, mul_pos hβ hmaxpos]
  have hcorn : β * R * (P.income z₀ + R * a₀) < P.minIncome := by
    rw [hmin]
    have hkey : β * R * (R * A) = P.minIncome * (1 - β * R) / 2 := by
      rw [hAdef]; field_simp; try ring
    have hmono : β * R * (R * a₀) ≤ β * R * (R * A) :=
      mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left ha₀A hR.le) (by positivity)
    have : β * R * (P.minIncome + R * a₀) = β * R * P.minIncome + β * R * (R * a₀) := by ring
    rw [this]
    nlinarith [hkey, hmono, hroom, hminpos]
  refine ⟨P.log_monotoneOn_capitalSupply hu hunb hβ hβ1 hrlo hlohi hβR hε hcapε hmono hz₀ hreach
    ha₀ hle hcorn ν hν, fun r hr hrr μ hμ => ?_⟩
  exact (P.log_existsUnique_isStationary hu hunb hβ hβ1 hβR hcap' hmono hz₀ hreach ha₀ hle hcorn
    hr hrr).unique hμ (hν r hr hrr)

/-- **Bisection on excess supply brackets and converges to the equilibrium rate of the log
economy**, along any selection of stationary distributions. -/
theorem log_bisection_of_cap {rlo rhi α δ : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (hδ : 0 < rlo + δ)
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded)
    (hβ : 0 < (P.discount : ℝ)) (hβ1 : (P.discount : ℝ) < 1) (hrlo : 0 < 1 + rlo)
    (hlohi : rlo ≤ rhi) (hβR : (P.discount : ℝ) * (1 + rhi) < 1)
    (hcap : 2 * (P.discount : ℝ) * P.maxIncome < (1 - (P.discount : ℝ) * (1 + rhi)) * assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hmin : P.income z₀ = P.minIncome) (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    (ν : ℝ → ProbabilityMeasure P.State)
    (hν : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).IsStationary (ν r))
    {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r) {μ : ProbabilityMeasure P.State}
    (hμ : (P.withRate r hrr).IsStationary μ)
    (he : P.aggregateCapital μ = normalisedDemand α δ r) :
    (∀ n, r ∈ Icc (bisect (P.excessSupply ν (normalisedDemand α δ)) rlo rhi n).1
      (bisect (P.excessSupply ν (normalisedDemand α δ)) rlo rhi n).2) ∧
    (∀ n, |((bisect (P.excessSupply ν (normalisedDemand α δ)) rlo rhi n).1
      + (bisect (P.excessSupply ν (normalisedDemand α δ)) rlo rhi n).2) / 2 - r|
        ≤ (rhi - rlo) / 2 ^ (n + 1)) ∧
    Tendsto (fun n => (bisect (P.excessSupply ν (normalisedDemand α δ)) rlo rhi n).1) atTop
      (𝓝 r) := by
  obtain ⟨hS, hid⟩ := P.log_selection_of_cap hu hunb hβ hβ1 hrlo hlohi hβR hcap hmono hz₀ hmin
    hreach ν hν
  have hE : StrictMonoOn (P.excessSupply ν (normalisedDemand α δ)) (Icc rlo rhi) :=
    strictMonoOn_sub_of_monotoneOn_of_strictAntiOn hS (normalisedDemand_strictAntiOn hα0 hα1 hδ)
  have hzero : P.excessSupply ν (normalisedDemand α δ) r = 0 := by
    unfold excessSupply
    rw [← hid r hr hrr μ hμ, he, sub_self]
  exact ⟨fun n => (bisect_mem_of_strictMonoOn hE hr hzero n).2.2,
    abs_bisect_mid_sub_le hE hr hzero, tendsto_bisect_fst hE hr hzero⟩

/-- **Aiyagari (1994) at `μ = 1`: his bisection finds his equilibrium rate.** On any
`[rlo, rhi] ⊂ (-δ, λ)` with the cap clearing `(48/25)·maxIncome/(1 - (24/25)(1+rhi))`, and along
any selection of stationary distributions, the bisection on excess supply brackets the
equilibrium rate at every step, its midpoint is within `(rhi - rlo)/2^(n+1)` after `n` steps,
and its endpoints converge to the rate. -/
theorem aiyagari1994_log_bisection {rlo rhi : ℝ}
    (hu : P.u = crraUtility 1) (hunb : P.Unbounded) (hβ : (P.discount : ℝ) = 24 / 25)
    (hrlo : -2 / 25 < rlo) (hlohi : rlo ≤ rhi) (hlam : rhi < 1 / 24)
    (hcap : 2 * (24 / 25) * P.maxIncome < (1 - 24 / 25 * (1 + rhi)) * assetCap)
    (hmono : P.MonotoneTransitions) {z₀ : Z} (hz₀ : ∀ z : Z, P.income z₀ ≤ P.income z)
    (hmin : P.income z₀ = P.minIncome) (hreach : ∀ z, 0 < P.transitionMatrix z z₀)
    (ν : ℝ → ProbabilityMeasure P.State)
    (hν : ∀ r ∈ Icc rlo rhi, ∀ hrr : P.RateOK r, (P.withRate r hrr).IsStationary (ν r))
    {r : ℝ} (hr : r ∈ Icc rlo rhi) (hrr : P.RateOK r) {μ : ProbabilityMeasure P.State}
    (hμ : (P.withRate r hrr).IsStationary μ)
    (he : P.aggregateCapital μ = normalisedDemand (9 / 25) (2 / 25) r) :
    (∀ n, r ∈ Icc (bisect (P.excessSupply ν (normalisedDemand (9 / 25) (2 / 25))) rlo rhi n).1
      (bisect (P.excessSupply ν (normalisedDemand (9 / 25) (2 / 25))) rlo rhi n).2) ∧
    (∀ n, |((bisect (P.excessSupply ν (normalisedDemand (9 / 25) (2 / 25))) rlo rhi n).1
      + (bisect (P.excessSupply ν (normalisedDemand (9 / 25) (2 / 25))) rlo rhi n).2) / 2 - r|
        ≤ (rhi - rlo) / 2 ^ (n + 1)) ∧
    Tendsto (fun n => (bisect (P.excessSupply ν (normalisedDemand (9 / 25) (2 / 25))) rlo rhi n).1)
      atTop (𝓝 r) :=
  P.log_bisection_of_cap (by norm_num) (by norm_num) (by linarith) hu hunb
    (by rw [hβ]; norm_num) (by rw [hβ]; norm_num) (by linarith) hlohi (by rw [hβ]; linarith)
    (by rw [hβ]; exact hcap) hmono hz₀ hmin hreach ν hν hr hrr hμ he

end IncomeFluctuation

end LeanEconomics
