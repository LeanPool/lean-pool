/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.SpecialFunctions.Complex.LogBounds
public import Mathlib.Probability.Distributions.Exponential

/-!
# Extreme value theory: the GEV family and maximum domains of attraction

The maximum `Mₙ = max(X₁, …, Xₙ)` of `n` iid losses with distribution function `F` has
distribution function `Fⁿ`. Extreme value theory asks for normalizing constants `cₙ > 0`, `dₙ`
with `Fⁿ(cₙ x + dₙ) → H(x)`. The Fisher–Tippett–Gnedenko theorem says the only possible
non-degenerate limits are, up to location and scale, the **generalized extreme value**
distribution functions (McNeil–Frey–Embrechts, *Quantitative Risk Management* (2015),
Definition 5.1)

  `H_ξ(x) = exp(−(1 + ξx)^{−1/ξ})` on `1 + ξx > 0`,   `H_0(x) = exp(−e^{−x})`.

This file sets up the family and the notion of maximum domain of attraction (`InMDA`). The
Fisher–Tippett–Gnedenko theorem itself is not formalized here.

* **The Poisson approximation.** `Fⁿ(uₙ) → e^{−τ}` if and only if `n F_bar(uₙ) → τ` (MFE
  Exercise 5.23(a), `tendsto_pow_iff_tendsto_nat_mul_tail`). A maximum of `n` draws stays below
  `uₙ` exactly when none of the `n` draws exceeds it, and the number of exceedances is
  asymptotically Poisson with mean `n F_bar(uₙ)`. All the domain-of-attraction computations below
  go through this equivalence. The `⇐` direction is Mathlib's
  `Real.tendsto_one_add_pow_exp_of_tendsto`; the `⇒` direction is a squeeze of `n (1 − aₙ)`
  between `n log aₙ` and `aₙ · n log aₙ`.
* **Max-stability.** For every `ξ` and `n ≥ 1`,
  `H_ξ(nᶻ x + (nᶻ − 1)/ξ)ⁿ = H_ξ(x)` with `z = ξ` (and `H_0(x + log n)ⁿ = H_0(x)`),
  so the maximum of `n` iid GEV variables is again GEV of the same shape (`gevCDF_max_stable`,
  MFE Exercise 5.10 in the Fréchet case). In particular every GEV lies in its own domain of
  attraction.
* **The exponential law** lies in the Gumbel domain of attraction with `cₙ = 1/λ`,
  `dₙ = log n / λ` (MFE Exercise 5.23(b), `tendsto_cdf_expMeasure_pow_gumbel`).

The generalized Pareto family and its domain of attraction are in
`Probability/Laws/GeneralizedPareto.lean`, and the Poisson–GPD–GEV link is in
`Probability/Jumps/PoissonMaxima.lean`.

## Main definitions

* `gevCDF`: the standard generalized extreme value distribution function `H_ξ`, with the Gumbel
  case `exp(−e^{−x})` at `ξ = 0`.
* `InMDA`: `F` lies in the maximum domain of attraction of `H`, i.e. `F(cₙ x + dₙ)ⁿ → H(x)` for
  some constants `cₙ > 0` and `dₙ`.
* `gevNormScale`, `gevNormLoc`: the max-stability normalizing constants `nᶻ` and `(nᶻ − 1)/ξ`
  (`log n` at `ξ = 0`), with `z = ξ`.

## Main results

* `tendsto_pow_iff_tendsto_mul_one_sub`: `aₙⁿ → e^{−τ} ↔ n (1 − aₙ) → τ` for `aₙ ≥ 0`.
* `tendsto_pow_iff_tendsto_nat_mul_tail`: MFE Exercise 5.23(a) for a distribution function.
* `gevNormScale`, `gevNormLoc`, `one_add_mul_gevNorm`: the max-stability normalization.
* `gevCDF_max_stable`, `gevCDF_inMDA`: max-stability of the GEV family.
* `tendsto_cdf_expMeasure_pow_gumbel`, `cdf_expMeasure_inMDA`: exponential ∈ MDA(Gumbel).

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Section 5.1; Section 5.1.1
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 5.10; Ex. 5.23(a); Ex. 5.23(b)

## Tags

extreme value theory, generalized extreme value, Gumbel, Fréchet,
domain of attraction, block maxima, MSC 62G30, MSC 60E05, JEL G32
-/

@[expose] public section

namespace MathFin

open Real Filter Topology MeasureTheory ProbabilityTheory

/-- The standard **generalized extreme value** distribution function `H_ξ`:
`H_ξ(x) = exp(−(1 + ξx)^{−1/ξ})` where `1 + ξx > 0`, with the value `0` below the support
(`ξ > 0`, Fréchet case) and `1` above it (`ξ < 0`, Weibull case), and the Gumbel distribution
function `H_0(x) = exp(−e^{−x})` for `ξ = 0`. -/
noncomputable def gevCDF (ξ x : ℝ) : ℝ :=
  if ξ = 0 then exp (-exp (-x))
  else if 0 < 1 + ξ * x then exp (-(1 + ξ * x) ^ (-1 / ξ))
  else if 0 < ξ then 0 else 1

/-- A distribution function `F` lies in the **maximum domain of attraction** of `H` if there
are normalizing constants `cₙ > 0` and `dₙ` with `F(cₙ x + dₙ)ⁿ → H(x)` for every `x`
(MFE Definition 5.3). -/
def InMDA (F H : ℝ → ℝ) : Prop :=
  ∃ c d : ℕ → ℝ, (∀ n, 0 < c n) ∧
    ∀ x, Tendsto (fun n : ℕ ↦ F (c n * x + d n) ^ n) atTop (𝓝 (H x))

/-- The Gumbel case of the GEV. -/
lemma gevCDF_zero (x : ℝ) : gevCDF 0 x = exp (-exp (-x)) :=
  ite_eq_left rfl

lemma gevCDF_of_pos {ξ x : ℝ} (hξ : ξ ≠ 0) (hx : 0 < 1 + ξ * x) :
    gevCDF ξ x = exp (-(1 + ξ * x) ^ (-1 / ξ)) := by
  rw [gevCDF, ite_eq_right hξ, ite_eq_left hx]

lemma gevCDF_of_nonpos {ξ x : ℝ} (hξ : ξ ≠ 0) (hx : 1 + ξ * x ≤ 0) :
    gevCDF ξ x = if 0 < ξ then 0 else 1 := by
  rw [gevCDF, ite_eq_right hξ, ite_eq_right hx.not_gt]

/-! ### The Poisson approximation -/

/-- **Poisson approximation of powers.** For a nonnegative sequence `a`,
`aₙⁿ → e^{−τ}` if and only if `n (1 − aₙ) → τ`. -/
theorem tendsto_pow_iff_tendsto_mul_one_sub {a : ℕ → ℝ} (ha : ∀ n, 0 ≤ a n) (τ : ℝ) :
    Tendsto (fun n ↦ a n ^ n) atTop (𝓝 (exp (-τ))) ↔
      Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - a n)) atTop (𝓝 τ) := by
  refine ⟨fun h ↦ ?_, fun h ↦ ?_⟩
  · -- a positive limit keeps `aₙ` away from `0`
    have hpos : ∀ᶠ n in atTop, 0 < a n := by
      filter_upwards [h.eventually (lt_mem_nhds (exp_pos (-τ))), eventually_ge_atTop 1]
        with n hn hn1
      refine (ha n).lt_of_ne fun h0 ↦ ?_
      rw [← h0, zero_pow (by omega)] at hn
      exact hn.false
    -- taking logarithms: `n log aₙ → −τ`
    have hlog : Tendsto (fun n : ℕ ↦ (n : ℝ) * log (a n)) atTop (𝓝 (-τ)) := by
      have := h.log (exp_pos _).ne'
      rw [log_exp] at this
      exact this.congr fun n ↦ log_pow (a n) n
    -- so `log aₙ → 0` and `aₙ → 1`
    have ha1 : Tendsto a atTop (𝓝 1) := by
      have h0 : Tendsto (fun n : ℕ ↦ log (a n)) atTop (𝓝 0) := by
        have := hlog.mul (tendsto_inv_atTop_zero.comp tendsto_natCast_atTop_atTop)
        rw [mul_zero] at this
        refine this.congr' ?_
        filter_upwards [eventually_ge_atTop 1] with n hn
        have hn0 : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
        simp only [Function.comp_apply]
        field_simp
      have := (continuous_exp.tendsto 0).comp h0
      rw [exp_zero] at this
      exact this.congr' (hpos.mono fun n hn ↦ exp_log hn)
    -- squeeze `n (aₙ − 1)` between `n log aₙ` and `aₙ · (n log aₙ)`
    have hsq : Tendsto (fun n : ℕ ↦ (n : ℝ) * (a n - 1)) atTop (𝓝 (-τ)) := by
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlog (by simpa using ha1.mul hlog)
        (hpos.mono fun n hn ↦ mul_le_mul_of_nonneg_left (log_le_sub_one_of_pos hn)
          n.cast_nonneg) (hpos.mono fun n hn ↦ ?_)
      calc (n : ℝ) * (a n - 1) = n * a n * (1 - (a n)⁻¹) := by field_simp
        _ ≤ n * a n * log (a n) :=
            mul_le_mul_of_nonneg_left (one_sub_inv_le_log_of_pos hn) (by positivity)
        _ = a n * (n * log (a n)) := by ring
    have := hsq.neg
    rw [neg_neg] at this
    exact this.congr fun n ↦ by ring
  · have h' : Tendsto (fun n : ℕ ↦ (n : ℝ) * (a n - 1)) atTop (𝓝 (-τ)) :=
      h.neg.congr fun n ↦ by ring
    exact (Real.tendsto_one_add_pow_exp_of_tendsto h').congr fun n ↦ by ring

/-- **The Poisson approximation for maxima** (MFE Exercise 5.23(a)): for a distribution
function `F`, levels `uₙ` and `h > 0`,
`F(uₙ)ⁿ → h ↔ n (1 − F(uₙ)) → −log h`. With `uₙ = cₙ x + dₙ` this says
`Fⁿ(cₙ x + dₙ) → H(x)` exactly when `n F_bar(cₙ x + dₙ) → −log H(x)`. -/
theorem tendsto_pow_iff_tendsto_nat_mul_tail {F : ℝ → ℝ} (hF : ∀ x, 0 ≤ F x) (u : ℕ → ℝ)
    {h : ℝ} (hh : 0 < h) :
    Tendsto (fun n ↦ F (u n) ^ n) atTop (𝓝 h) ↔
      Tendsto (fun n : ℕ ↦ (n : ℝ) * (1 - F (u n))) atTop (𝓝 (-log h)) := by
  have := tendsto_pow_iff_tendsto_mul_one_sub (fun n ↦ hF (u n)) (-log h)
  rwa [neg_neg, exp_log hh] at this

/-! ### Max-stability of the GEV family -/

/-- The scale normalization `nᶻ` of max-stability, with `z = ξ` (kept positive at `n = 0`). -/
noncomputable def gevNormScale (ξ : ℝ) (n : ℕ) : ℝ :=
  max (n : ℝ) 1 ^ ξ

/-- The location normalization of max-stability: `(nᶻ − 1)/ξ` with `z = ξ`, and its limit
`log n` when `ξ = 0`. -/
noncomputable def gevNormLoc (ξ : ℝ) (n : ℕ) : ℝ :=
  if ξ = 0 then log n else (gevNormScale ξ n - 1) / ξ

lemma gevNormScale_pos (ξ : ℝ) (n : ℕ) : 0 < gevNormScale ξ n :=
  rpow_pos_of_pos (lt_max_of_lt_right one_pos) ξ

/-- The max-stability normalization moves the GEV support by a factor: for `ξ ≠ 0`,
`1 + ξ (cₙ x + dₙ) = cₙ (1 + ξ x)`. -/
lemma one_add_mul_gevNorm {ξ : ℝ} (hξ : ξ ≠ 0) (n : ℕ) (x : ℝ) :
    1 + ξ * (gevNormScale ξ n * x + gevNormLoc ξ n) = gevNormScale ξ n * (1 + ξ * x) := by
  rw [gevNormLoc, ite_eq_right hξ]
  field_simp
  ring

/-- **Max-stability of the GEV family** (MFE Exercise 5.10 for the Fréchet case): for every
shape `ξ` and every `n ≥ 1`, `H_ξ(nᶻ x + dₙ)ⁿ = H_ξ(x)` with `z = ξ` and `dₙ = (nᶻ − 1)/ξ`
(`dₙ = log n` for `ξ = 0`). The maximum of `n` iid `H_ξ` variables, rescaled, is again `H_ξ`. -/
theorem gevCDF_max_stable (ξ x : ℝ) {n : ℕ} (hn : n ≠ 0) :
    gevCDF ξ (gevNormScale ξ n * x + gevNormLoc ξ n) ^ n = gevCDF ξ x := by
  have hn1 : (1 : ℝ) ≤ n := Nat.one_le_cast.2 (Nat.pos_of_ne_zero hn)
  have hnpos : (0 : ℝ) < n := one_pos.trans_le hn1
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  by_cases hξ : ξ = 0
  · subst hξ
    rw [gevNormLoc, ite_eq_left rfl, gevNormScale, rpow_zero, one_mul, gevCDF_zero, gevCDF_zero,
      ← exp_nat_mul, neg_add, exp_add, exp_neg (log n), exp_log hnpos]
    congr 1
    field_simp
  · have hc : 0 < gevNormScale ξ n := gevNormScale_pos ξ n
    have hcn : gevNormScale ξ n = (n : ℝ) ^ ξ := by rw [gevNormScale, max_eq_left hn1]
    have hkey := one_add_mul_gevNorm hξ n x
    by_cases hx : 0 < 1 + ξ * x
    · have hpos : 0 < 1 + ξ * (gevNormScale ξ n * x + gevNormLoc ξ n) := hkey ▸ mul_pos hc hx
      rw [gevCDF_of_pos hξ hpos, gevCDF_of_pos hξ hx, hkey, ← exp_nat_mul,
        mul_rpow hc.le hx.le, hcn, ← rpow_mul hnpos.le, show ξ * (-1 / ξ) = -1 by field_simp,
        rpow_neg_one]
      congr 1
      field_simp
    · have hx' : 1 + ξ * x ≤ 0 := not_lt.1 hx
      have hnp : 1 + ξ * (gevNormScale ξ n * x + gevNormLoc ξ n) ≤ 0 :=
        hkey ▸ mul_nonpos_of_nonneg_of_nonpos hc.le hx'
      rw [gevCDF_of_nonpos hξ hnp, gevCDF_of_nonpos hξ hx']
      split_ifs <;> simp [hn]

/-- Every GEV distribution function lies in its own maximum domain of attraction: the
normalized maxima are exactly `H_ξ` from `n = 1` on. -/
theorem gevCDF_inMDA (ξ : ℝ) : InMDA (gevCDF ξ) (gevCDF ξ) :=
  ⟨gevNormScale ξ, gevNormLoc ξ, gevNormScale_pos ξ, fun x ↦ tendsto_const_nhds.congr' <|
    (eventually_ge_atTop 1).mono fun _ hn ↦ (gevCDF_max_stable ξ x (by omega)).symm⟩

/-! ### The exponential law is in the Gumbel domain of attraction -/

/-- **MFE Exercise 5.23(b).** For the exponential law with rate `λ > 0`,
`F(x/λ + log n/λ)ⁿ → exp(−e^{−x}) = H_0(x)`: the maximum of `n` iid exponentials, recentred
by `log n / λ` and rescaled by `λ`, converges to the Gumbel law. -/
theorem tendsto_cdf_expMeasure_pow_gumbel {r : ℝ} (hr : 0 < r) (x : ℝ) :
    Tendsto (fun n : ℕ ↦ cdf (expMeasure r) (r⁻¹ * x + log n / r) ^ n) atTop
      (𝓝 (gevCDF 0 x)) := by
  rw [gevCDF_zero, tendsto_pow_iff_tendsto_nat_mul_tail (cdf_nonneg _) _ (exp_pos _), log_exp,
    neg_neg]
  refine tendsto_const_nhds.congr' ?_
  filter_upwards [eventually_ge_atTop 1,
    (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (-x)]
    with n hn hlog
  have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
  have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
  have hr0 : r ≠ 0 := hr.ne'
  have hlog' : 0 ≤ x + log n := by simp only [Function.comp_apply] at hlog; linarith
  have harg : r⁻¹ * x + log n / r = (x + log n) / r := by field_simp
  rw [harg, cdf_expMeasure_eq hr, ite_eq_left (div_nonneg hlog' hr.le),
    show r * ((x + log n) / r) = x + log n by field_simp, neg_add, exp_add, exp_neg (log n),
    exp_log hnpos]
  field_simp
  ring

/-- The exponential law lies in the maximum domain of attraction of the Gumbel distribution. -/
theorem cdf_expMeasure_inMDA {r : ℝ} (hr : 0 < r) : InMDA (cdf (expMeasure r)) (gevCDF 0) :=
  ⟨fun _ ↦ r⁻¹, fun n ↦ log n / r, fun _ ↦ inv_pos.2 hr, tendsto_cdf_expMeasure_pow_gumbel hr⟩

end MathFin
