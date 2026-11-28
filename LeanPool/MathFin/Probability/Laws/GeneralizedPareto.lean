/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Probability.Laws.ExtremeValue
public import LeanPool.MathFin.Probability.Laws.Quantile
public import Mathlib.Algebra.Order.Star.Real

/-!
# The generalized Pareto distribution

The **generalized Pareto distribution** `GPD(ξ, β)` has tail function

  `Gbar_{ξ,β}(x) = (1 + ξx/β)^{−1/ξ}`   (`e^{−x/β}` when `ξ = 0`),

on `x ≥ 0` (and `x ≤ −β/ξ` when `ξ < 0`). It is the model of the peaks-over-threshold method
(McNeil–Frey–Embrechts, *Quantitative Risk Management* (2015), §5.2). The Pickands–Balkema–de
Haan theorem, which makes it the limit law of excesses over high thresholds, is not formalized
here. This file proves the properties that make the GPD a consistent model for excesses.

* **Domain of attraction** (MFE Exercise 5.16). `G_{ξ,β} ∈ MDA(H_ξ)` for every shape `ξ`, with
  the normalizing constants of GEV max-stability scaled by `β` (`tendsto_gpdCDF_pow`,
  `gpdCDF_inMDA`). The Pareto (Lomax) tail `(κ/(κ + x))^α` is the GPD tail with `ξ = 1/α`,
  `β = κ/α` (`gpdTail_inv_shape`), so the Pareto law lies in the Fréchet domain `MDA(H_{1/α})`.
* **Threshold stability.** Excesses of a GPD over a threshold `u` in its support are again GPD,
  with the same shape and scale `β + ξu`: `Gbar_{ξ,β}(u + x) = Gbar_{ξ,β}(u) · Gbar_{ξ,β+ξu}(x)`
  (`gpdTail_add`). As laws, `(X − u | X > u) ∼ GPD(ξ, β + ξu)` (`map_cond_gpdMeasure`).
* **The GPD law.** `gpdMeasure ξ β` is the law of `β (e^{ξE} − 1)/ξ` (`β E` for `ξ = 0`) for a
  standard exponential `E`. Its distribution function is `G_{ξ,β}` (`cdf_gpdMeasure`), and its
  quantile function, the value-at-risk of a GPD loss, is `β((1 − p)^{−ξ} − 1)/ξ`
  (`quantile_gpdMeasure_of_ne_zero`), or `−β log(1 − p)` when `ξ = 0`.
* **Tail averages.** For `ξ < 1` the average of the quantile function over `(α, 1)` is
  `(q(α) + β)/(1 − ξ)` (`setIntegral_quantile_gpdMeasure`). This is the expected shortfall
  formula `ES_α = (VaR_α + β)/(1 − ξ)` of MFE eq. (5.19) at threshold `0`. The mean is
  `β/(1 − ξ)` (`integral_id_gpdMeasure`). The **mean excess function** is linear,
  `e(u) = E[X − u | X > u] = (β + ξu)/(1 − ξ)` (`integral_sub_cond_gpdMeasure`, MFE
  Exercise 5.19(b)), which is what a sample mean-excess plot is inspected for.

## Main definitions

* `gpdTail`: the tail function `Gbar_{ξ,β}(x) = (1 + ξx/β)^{−1/ξ}` (`e^{−x/β}` for `ξ = 0`),
  equal to   `1` for `x ≤ 0` and to `0` beyond the right endpoint `−β/ξ` when `ξ < 0`.
* `gpdCDF`: the distribution function `G_{ξ,β} = 1 − Gbar_{ξ,β}`.
* `gpdMeasure`: the law `GPD(ξ, β)` of `β(e^{ξE} − 1)/ξ` (`β E` for `ξ = 0`) for a standard
  exponential variable `E`.

## Main results

* `tendsto_gpdCDF_pow`, `gpdCDF_inMDA`: `G_{ξ,β} ∈ MDA(H_ξ)`.
* `gpdTail_add`, `gpdCDF_excess`: threshold stability for distribution functions.
* `gpdMeasure`, `cdf_gpdMeasure`, `quantile_gpdMeasure`: the GPD law and its quantiles.
* `setIntegral_quantile_gpdMeasure`, `integral_id_gpdMeasure`: tail averages and the mean.
* `map_cond_gpdMeasure`, `integral_sub_cond_gpdMeasure`: excesses of the GPD law and the
  mean excess function.

## References

* [A. J. McNeil, R. Frey and P. Embrechts, *Quantitative Risk Management: Concepts, Techniques and
  Tools*][McNeilFreyEmbrechts], Section 5.2.1
* [*QRM Exercise Book*][QRMExerciseBook], Ex. 5.16; Ex. 5.19(b)

## Tags

generalized Pareto distribution, peaks over threshold, mean excess function, expected shortfall,
tail risk, MSC 62G30, MSC 91G70, JEL G32
-/

@[expose] public section

namespace MathFin

open Real Filter Topology MeasureTheory ProbabilityTheory Set

variable {ξ β x : ℝ}

/-! ### The tail and distribution functions -/

/-- The **generalized Pareto tail function** `Gbar_{ξ,β}(x) = (1 + ξx/β)^{−1/ξ}` on the support,
and `e^{−x/β}` when `ξ = 0`. It equals `1` for `x ≤ 0` and `0` beyond the right endpoint
`−β/ξ` when `ξ < 0`. -/
noncomputable def gpdTail (ξ β x : ℝ) : ℝ :=
  if ξ = 0 then exp (-(max x 0 / β)) else max (1 + ξ * (max x 0 / β)) 0 ^ (-1 / ξ)

/-- The **generalized Pareto distribution function** `G_{ξ,β} = 1 − Gbar_{ξ,β}`
(MFE Definition 5.14). -/
noncomputable def gpdCDF (ξ β x : ℝ) : ℝ :=
  1 - gpdTail ξ β x

lemma gpdTail_of_nonpos (hx : x ≤ 0) : gpdTail ξ β x = 1 := by
  rw [gpdTail, max_eq_right hx, zero_div, neg_zero, exp_zero, mul_zero, add_zero,
    max_eq_left zero_le_one, one_rpow, ite_self]

lemma gpdTail_zero_shape (hx : 0 ≤ x) : gpdTail 0 β x = exp (-(x / β)) := by
  rw [gpdTail, ite_eq_left rfl, max_eq_left hx]

lemma gpdTail_of_nonneg (hξ : ξ ≠ 0) (hx : 0 ≤ x) (h : 0 ≤ 1 + ξ * (x / β)) :
    gpdTail ξ β x = (1 + ξ * (x / β)) ^ (-1 / ξ) := by
  rw [gpdTail, ite_eq_right hξ, max_eq_left hx, max_eq_left h]

/-- Beyond the right endpoint `−β/ξ` (only possible for `ξ < 0`) the tail vanishes. -/
lemma gpdTail_of_endpoint_le (hξ : ξ ≠ 0) (hx : 0 ≤ x) (h : 1 + ξ * (x / β) ≤ 0) :
    gpdTail ξ β x = 0 := by
  rw [gpdTail, ite_eq_right hξ, max_eq_left hx, max_eq_right h,
    zero_rpow (div_ne_zero (by norm_num) hξ)]

/-- The tail is positive inside the support. -/
lemma gpdTail_pos (hx : 0 < 1 + ξ * (max x 0 / β)) : 0 < gpdTail ξ β x := by
  unfold gpdTail
  split_ifs
  · exact exp_pos _
  · rw [max_eq_left hx.le]
    exact rpow_pos_of_pos hx _

/-- The tail is at most `1`. -/
lemma gpdTail_le_one (hβ : 0 < β) : gpdTail ξ β x ≤ 1 := by
  have hm : 0 ≤ max x 0 / β := div_nonneg (le_max_right _ _) hβ.le
  unfold gpdTail
  split_ifs with hξ
  · exact exp_le_one_iff.2 (neg_nonpos.2 hm)
  · rcases lt_or_gt_of_ne hξ with hneg | hpos
    · refine rpow_le_one (le_max_right _ _) (max_le ?_ zero_le_one)
        (div_nonneg_of_nonpos (by norm_num) hneg.le)
      nlinarith [mul_nonneg (neg_nonneg.2 hneg.le) hm]
    · exact rpow_le_one_of_one_le_of_nonpos
        (le_max_of_le_left (by nlinarith [mul_nonneg hpos.le hm]))
        (by rw [neg_div]; exact neg_nonpos.2 (one_div_pos.2 hpos).le)

/-- The Pareto (Lomax) tail `(κ/(κ + x))^α` is the GPD tail with shape `1/α` and scale `κ/α`. -/
lemma gpdTail_inv_shape {α κ : ℝ} (hα : 0 < α) (hκ : 0 < κ) (hx : 0 ≤ x) :
    gpdTail α⁻¹ (κ / α) x = (κ / (κ + x)) ^ α := by
  have hα0 : α ≠ 0 := hα.ne'
  have hκ0 : κ ≠ 0 := hκ.ne'
  have hbase : 1 + α⁻¹ * (x / (κ / α)) = (κ + x) / κ := by field_simp
  rw [gpdTail_of_nonneg (inv_ne_zero hα.ne') hx (by rw [hbase]; positivity), hbase,
    show -1 / α⁻¹ = -α by field_simp, rpow_neg (by positivity), ← inv_rpow (by positivity),
    inv_div]

/-! ### The domain of attraction of the GPD -/

/-- **MFE Exercise 5.16.** The GPD lies in the domain of attraction of the GEV of the same
shape: with `cₙ = β nᶻ` and `dₙ = β (nᶻ − 1)/ξ` (`z = ξ`; `dₙ = β log n` for `ξ = 0`),
`G_{ξ,β}(cₙ x + dₙ)ⁿ → H_ξ(x)` for every `x`. -/
theorem tendsto_gpdCDF_pow (hβ : 0 < β) (ξ x : ℝ) :
    Tendsto (fun n : ℕ ↦ gpdCDF ξ β (β * (gevNormScale ξ n * x + gevNormLoc ξ n)) ^ n)
      atTop (𝓝 (gevCDF ξ x)) := by
  have hF (y : ℝ) : 0 ≤ gpdCDF ξ β y := sub_nonneg.2 (gpdTail_le_one hβ)
  have hβ0 : β ≠ 0 := hβ.ne'
  -- the levels, divided by `β`, are the GEV max-stability levels
  have hlev (n : ℕ) : β * (gevNormScale ξ n * x + gevNormLoc ξ n) / β =
      gevNormScale ξ n * x + gevNormLoc ξ n := mul_div_cancel_left₀ _ hβ0
  by_cases hξ : ξ = 0
  · subst hξ
    rw [gevCDF_zero, tendsto_pow_iff_tendsto_nat_mul_tail hF _ (exp_pos _), log_exp, neg_neg]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1,
      (tendsto_log_atTop.comp tendsto_natCast_atTop_atTop).eventually_ge_atTop (-x)]
      with n hn hlog
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    have hlog' : 0 ≤ x + log n := by simp only [Function.comp_apply] at hlog; linarith
    have hv : gevNormScale 0 n * x + gevNormLoc 0 n = x + log n := by
      rw [gevNormScale, rpow_zero, one_mul, gevNormLoc, ite_eq_left rfl]
    rw [gpdCDF, sub_sub_cancel, gpdTail_zero_shape (mul_nonneg hβ.le (hv ▸ hlog')), hlev, hv,
      neg_add, exp_add, exp_neg (log n), exp_log hnpos]
    field_simp
  have hkey (n : ℕ) : 1 + ξ * (β * (gevNormScale ξ n * x + gevNormLoc ξ n) / β) =
      gevNormScale ξ n * (1 + ξ * x) := by
    rw [hlev, one_add_mul_gevNorm hξ]
  by_cases hx : 0 < 1 + ξ * x
  · -- inside the support: `n Gbar(uₙ) = (1 + ξx)^{−1/ξ}` as soon as `uₙ ≥ 0`
    rw [gevCDF_of_pos hξ hx, tendsto_pow_iff_tendsto_nat_mul_tail hF _ (exp_pos _), log_exp,
      neg_neg]
    -- the normalized levels `vₙ = cₙ x + dₙ` are eventually nonnegative
    have hev : ∀ᶠ n : ℕ in atTop, 0 ≤ gevNormScale ξ n * x + gevNormLoc ξ n := by
      rcases lt_or_gt_of_ne hξ with hneg | hpos
      · have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ξ) atTop (𝓝 0) := by
          have := (tendsto_rpow_neg_atTop (neg_pos.2 hneg)).comp tendsto_natCast_atTop_atTop
          simpa only [neg_neg, Function.comp_def] using this
        filter_upwards [eventually_ge_atTop 1,
          ht.eventually (ge_mem_nhds (one_div_pos.2 hx))] with n hn hle
        have hcn : gevNormScale ξ n = (n : ℝ) ^ ξ := by
          rw [gevNormScale, max_eq_left (Nat.one_le_cast.2 hn)]
        have h1 : gevNormScale ξ n * (1 + ξ * x) ≤ 1 := by
          rw [hcn]
          calc (n : ℝ) ^ ξ * (1 + ξ * x) ≤ 1 / (1 + ξ * x) * (1 + ξ * x) :=
                mul_le_mul_of_nonneg_right hle hx.le
            _ = 1 := by field_simp
        have h2 := one_add_mul_gevNorm hξ n x
        by_contra! h3
        nlinarith [mul_pos_of_neg_of_neg hneg h3]
      · have ht : Tendsto (fun n : ℕ ↦ (n : ℝ) ^ ξ) atTop atTop :=
          (tendsto_rpow_atTop hpos).comp tendsto_natCast_atTop_atTop
        filter_upwards [eventually_ge_atTop 1, ht.eventually_ge_atTop (1 / (1 + ξ * x))]
          with n hn hge
        have hcn : gevNormScale ξ n = (n : ℝ) ^ ξ := by
          rw [gevNormScale, max_eq_left (Nat.one_le_cast.2 hn)]
        have h1 : 1 ≤ gevNormScale ξ n * (1 + ξ * x) := by
          rw [hcn]
          calc 1 = 1 / (1 + ξ * x) * (1 + ξ * x) := by field_simp
            _ ≤ (n : ℝ) ^ ξ * (1 + ξ * x) := mul_le_mul_of_nonneg_right hge hx.le
        have h2 := one_add_mul_gevNorm hξ n x
        by_contra! h3
        nlinarith [mul_neg_of_pos_of_neg hpos h3]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [eventually_ge_atTop 1, hev] with n hn hv
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.2 hn
    have hn0 : (n : ℝ) ≠ 0 := hnpos.ne'
    have hcn : gevNormScale ξ n = (n : ℝ) ^ ξ := by
      rw [gevNormScale, max_eq_left (Nat.one_le_cast.2 hn)]
    have hsupp : 0 ≤ 1 + ξ * (β * (gevNormScale ξ n * x + gevNormLoc ξ n) / β) := by
      rw [hkey]
      exact (mul_pos (gevNormScale_pos ξ n) hx).le
    rw [gpdCDF, sub_sub_cancel, gpdTail_of_nonneg hξ (mul_nonneg hβ.le hv) hsupp, hkey,
      mul_rpow (gevNormScale_pos ξ n).le hx.le, hcn, ← rpow_mul hnpos.le,
      show ξ * (-1 / ξ) = -1 by field_simp, rpow_neg_one]
    field_simp
  · -- outside the support the powers are eventually constant
    have hx' : 1 + ξ * x ≤ 0 := not_lt.1 hx
    rw [gevCDF_of_nonpos hξ hx']
    refine tendsto_const_nhds.congr' ((eventually_ge_atTop 1).mono fun n hn ↦ ?_)
    dsimp only
    have hle : 1 + ξ * (β * (gevNormScale ξ n * x + gevNormLoc ξ n) / β) ≤ 0 := by
      rw [hkey]
      exact mul_nonpos_of_nonneg_of_nonpos (gevNormScale_pos ξ n).le hx'
    rw [hlev] at hle
    rcases lt_or_gt_of_ne hξ with hneg | hpos
    · -- `ξ < 0`: beyond the right endpoint, `G = 1`
      have hv : 0 ≤ gevNormScale ξ n * x + gevNormLoc ξ n := by
        by_contra! h3
        nlinarith [mul_pos_of_neg_of_neg hneg h3]
      have hle' : 1 + ξ * (β * (gevNormScale ξ n * x + gevNormLoc ξ n) / β) ≤ 0 := by
        rwa [hlev]
      rw [ite_eq_right (not_lt.2 hneg.le), gpdCDF,
        gpdTail_of_endpoint_le hξ (mul_nonneg hβ.le hv) hle', sub_zero, one_pow]
    · -- `ξ > 0`: below the left endpoint, `G = 0`
      have hv : gevNormScale ξ n * x + gevNormLoc ξ n ≤ 0 := by
        by_contra! h3
        nlinarith [mul_pos hpos h3]
      rw [ite_eq_left hpos, gpdCDF, gpdTail_of_nonpos (mul_nonpos_of_nonneg_of_nonpos hβ.le hv),
        sub_self, zero_pow (by omega)]

/-- **The GPD is in the maximum domain of attraction of the GEV of the same shape**
(MFE Exercise 5.16). -/
theorem gpdCDF_inMDA (hβ : 0 < β) (ξ : ℝ) : InMDA (gpdCDF ξ β) (gevCDF ξ) :=
  ⟨fun n ↦ β * gevNormScale ξ n, fun n ↦ β * gevNormLoc ξ n,
    fun n ↦ mul_pos hβ (gevNormScale_pos ξ n), fun x ↦ by
      simpa only [mul_add, mul_assoc] using tendsto_gpdCDF_pow hβ ξ x⟩

/-! ### Threshold stability -/

/-- **Threshold stability of the GPD**: for a threshold `u ≥ 0` inside the support and `x ≥ 0`,
`Gbar_{ξ,β}(u + x) = Gbar_{ξ,β}(u) · Gbar_{ξ,β+ξu}(x)`. -/
theorem gpdTail_add (hβ : 0 < β) {u : ℝ} (hu : 0 ≤ u) (hsupp : 0 < 1 + ξ * (u / β))
    (hx : 0 ≤ x) : gpdTail ξ β (u + x) = gpdTail ξ β u * gpdTail ξ (β + ξ * u) x := by
  have hβ0 : β ≠ 0 := hβ.ne'
  have hβ' : 0 < β + ξ * u := by
    have : β + ξ * u = β * (1 + ξ * (u / β)) := by field_simp
    rw [this]
    exact mul_pos hβ hsupp
  have hβ'0 : β + ξ * u ≠ 0 := hβ'.ne'
  by_cases hξ : ξ = 0
  · subst hξ
    rw [gpdTail_zero_shape (add_nonneg hu hx), gpdTail_zero_shape hu, zero_mul, add_zero,
      gpdTail_zero_shape hx, ← exp_add]
    congr 1
    ring
  · -- the support factorizes: `1 + ξ(u + x)/β = (1 + ξu/β)(1 + ξx/(β + ξu))`
    have hfac : 1 + ξ * ((u + x) / β) =
        (1 + ξ * (u / β)) * (1 + ξ * (x / (β + ξ * u))) := by
      field_simp
      ring
    rw [gpdTail_of_nonneg hξ hu hsupp.le]
    by_cases hB : 0 ≤ 1 + ξ * (x / (β + ξ * u))
    · rw [gpdTail_of_nonneg hξ (add_nonneg hu hx) (hfac ▸ mul_nonneg hsupp.le hB), hfac,
        gpdTail_of_nonneg hξ hx hB, mul_rpow hsupp.le hB]
    · push Not at hB
      rw [gpdTail_of_endpoint_le hξ (add_nonneg hu hx)
          (hfac ▸ (mul_neg_of_pos_of_neg hsupp hB).le),
        gpdTail_of_endpoint_le hξ hx hB.le, mul_zero]

/-- **The excess distribution of a GPD is a GPD**: over a threshold `u ≥ 0` inside the support,
`(G(u + x) − G(u))/(1 − G(u)) = G_{ξ,β+ξu}(x)` for `x ≥ 0`. -/
theorem gpdCDF_excess (hβ : 0 < β) {u : ℝ} (hu : 0 ≤ u) (hsupp : 0 < 1 + ξ * (u / β))
    (hx : 0 ≤ x) :
    (gpdCDF ξ β (u + x) - gpdCDF ξ β u) / (1 - gpdCDF ξ β u) = gpdCDF ξ (β + ξ * u) x := by
  have hpos : 0 < gpdTail ξ β u := gpdTail_pos (by rwa [max_eq_left hu])
  have hpos0 : gpdTail ξ β u ≠ 0 := hpos.ne'
  simp only [gpdCDF, sub_sub_sub_cancel_left, sub_sub_cancel]
  rw [gpdTail_add hβ hu hsupp hx, ← mul_one_sub, mul_div_cancel_left₀ _ hpos0]

/-! ### The GPD law -/

/-- The transform `e ↦ β(e^{ξe} − 1)/ξ` (`β e` for `ξ = 0`) that turns a standard exponential
variable into a generalized Pareto one. -/
noncomputable def gpdOfExp (ξ β e : ℝ) : ℝ :=
  if ξ = 0 then β * e else β * (exp (ξ * e) - 1) / ξ

/-- The **generalized Pareto law** `GPD(ξ, β)`: the law of `β(e^{ξE} − 1)/ξ` for a standard
exponential variable `E` (`β E` when `ξ = 0`). -/
noncomputable def gpdMeasure (ξ β : ℝ) : Measure ℝ :=
  (expMeasure 1).map (gpdOfExp ξ β)

lemma continuous_gpdOfExp : Continuous (gpdOfExp ξ β) :=
  continuous_if_const _ (fun _ ↦ by fun_prop) fun _ ↦ by fun_prop

lemma gpdOfExp_zero : gpdOfExp ξ β 0 = 0 := by
  unfold gpdOfExp
  split_ifs <;> simp

lemma strictMono_gpdOfExp (hβ : 0 < β) : StrictMono (gpdOfExp ξ β) := by
  intro a b hab
  unfold gpdOfExp
  split_ifs with hξ
  · exact mul_lt_mul_of_pos_left hab hβ
  · have key (e : ℝ) : β * (exp (ξ * e) - 1) / ξ = β / ξ * (exp (ξ * e) - 1) := by ring
    rw [key, key]
    rcases lt_or_gt_of_ne hξ with hneg | hpos
    · exact mul_lt_mul_of_neg_left
        (sub_lt_sub_right (exp_lt_exp.2 (mul_lt_mul_of_neg_left hab hneg)) 1)
        (div_neg_of_pos_of_neg hβ hneg)
    · exact mul_lt_mul_of_pos_left
        (sub_lt_sub_right (exp_lt_exp.2 (mul_lt_mul_of_pos_left hab hpos)) 1)
        (div_pos hβ hpos)

instance isProbabilityMeasure_gpdMeasure : IsProbabilityMeasure (gpdMeasure ξ β) :=
  haveI := isProbabilityMeasure_expMeasure (r := 1) one_pos
  inferInstanceAs (IsProbabilityMeasure ((expMeasure 1).map (gpdOfExp ξ β)))

/-- **The distribution function of the GPD law** is `G_{ξ,β}`. -/
theorem cdf_gpdMeasure (hβ : 0 < β) (x : ℝ) : cdf (gpdMeasure ξ β) x = gpdCDF ξ β x := by
  have := isProbabilityMeasure_expMeasure (r := 1) one_pos
  have hβ0 : β ≠ 0 := hβ.ne'
  have hmeas : Measurable (gpdOfExp ξ β) := continuous_gpdOfExp.measurable
  have hsm : StrictMono (gpdOfExp ξ β) := strictMono_gpdOfExp hβ
  have hexp (t : ℝ) (ht : 0 ≤ t) : (expMeasure 1).real (Iic t) = 1 - exp (-t) := by
    rw [← cdf_eq_real, cdf_expMeasure_eq one_pos, ite_eq_left ht, one_mul]
  rw [cdf_eq_real, gpdMeasure, map_measureReal_apply hmeas measurableSet_Iic, gpdCDF]
  rcases lt_or_ge x 0 with hx | hx
  · -- below the support
    rw [gpdTail_of_nonpos hx.le, sub_self]
    have hsub : gpdOfExp ξ β ⁻¹' Iic x ⊆ Iic 0 := fun e he ↦
      (hsm.lt_iff_lt.1 (by rw [gpdOfExp_zero]; exact lt_of_le_of_lt he hx)).le
    refine le_antisymm ?_ measureReal_nonneg
    calc (expMeasure 1).real (gpdOfExp ξ β ⁻¹' Iic x) ≤ (expMeasure 1).real (Iic 0) :=
          measureReal_mono hsub
      _ = 0 := by rw [hexp 0 le_rfl, neg_zero, exp_zero, sub_self]
  by_cases hend : ξ ≠ 0 ∧ 1 + ξ * (x / β) ≤ 0
  · -- beyond the right endpoint every value of the transform lies below `x`
    obtain ⟨hξ, hle⟩ := hend
    have hneg : ξ < 0 := by
      by_contra! h
      have : 0 ≤ ξ * (x / β) := mul_nonneg h (div_nonneg hx hβ.le)
      linarith
    have hx' : -β / ξ ≤ x := by
      rw [div_le_iff_of_neg hneg]
      have h1 : x * ξ = β * (ξ * (x / β)) := by field_simp
      nlinarith [mul_le_mul_of_nonneg_left hle hβ.le]
    have hall : gpdOfExp ξ β ⁻¹' Iic x = univ := by
      ext e
      simp only [mem_preimage, mem_Iic, mem_univ, iff_true]
      rw [gpdOfExp, ite_eq_right hξ]
      have h2 : β * exp (ξ * e) / ξ < 0 := div_neg_of_pos_of_neg (mul_pos hβ (exp_pos _)) hneg
      calc β * (exp (ξ * e) - 1) / ξ = β * exp (ξ * e) / ξ + -β / ξ := by ring
        _ ≤ x := by linarith
    rw [hall, probReal_univ, gpdTail_of_endpoint_le hξ hx hle, sub_zero]
  -- inside the support the preimage is `Iic t` with `t = −log Gbar(x)`
  push Not at hend
  have hsupp' : 0 < 1 + ξ * (max x 0 / β) := by
    rw [max_eq_left hx]
    by_cases hξ : ξ = 0
    · simp [hξ]
    · exact hend hξ
  have hpos : 0 < gpdTail ξ β x := gpdTail_pos hsupp'
  obtain ⟨t, ht⟩ : ∃ t, t = -log (gpdTail ξ β x) := ⟨_, rfl⟩
  have ht0 : 0 ≤ t := ht ▸ neg_nonneg.2 (log_nonpos hpos.le (gpdTail_le_one hβ))
  have hinv : gpdOfExp ξ β t = x := by
    by_cases hξ : ξ = 0
    · subst hξ
      rw [ht, gpdTail_zero_shape hx, log_exp, neg_neg, gpdOfExp, ite_eq_left rfl]
      field_simp
    · have hs := hend hξ
      rw [ht, gpdTail_of_nonneg hξ hx hs.le, log_rpow hs, gpdOfExp, ite_eq_right hξ,
        show ξ * -(-1 / ξ * log (1 + ξ * (x / β))) = log (1 + ξ * (x / β)) by field_simp,
        exp_log hs]
      field_simp
      ring
  have hpre : gpdOfExp ξ β ⁻¹' Iic x = Iic t := by
    ext e
    simp only [mem_preimage, mem_Iic]
    rw [← hinv, hsm.le_iff_le]
  rw [hpre, hexp t ht0, ht, neg_neg, exp_log hpos]

/-- **The quantile function of the GPD law** is the transform of the exponential quantile:
`q(p) = gpdOfExp ξ β (−log(1 − p))`. -/
theorem quantile_gpdMeasure (hβ : 0 < β) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    quantile (gpdMeasure ξ β) p = gpdOfExp ξ β (-log (1 - p)) := by
  have := isProbabilityMeasure_expMeasure (r := 1) one_pos
  rw [gpdMeasure, quantile_map (strictMono_gpdOfExp hβ).monotone
    continuous_gpdOfExp.lowerSemicontinuous hp, quantile_expMeasure one_pos hp, div_one]

/-- **Value-at-risk of a GPD loss** (`ξ ≠ 0`): `q(p) = β((1 − p)^{−ξ} − 1)/ξ`. -/
theorem quantile_gpdMeasure_of_ne_zero (hβ : 0 < β) (hξ : ξ ≠ 0) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    quantile (gpdMeasure ξ β) p = β * ((1 - p) ^ (-ξ) - 1) / ξ := by
  rw [quantile_gpdMeasure hβ hp, gpdOfExp, ite_eq_right hξ, rpow_def_of_pos (sub_pos.2 hp.2)]
  ring_nf

/-- **Value-at-risk of an exponential GPD loss** (`ξ = 0`): `q(p) = −β log(1 − p)`. -/
theorem quantile_gpdMeasure_zero (hβ : 0 < β) {p : ℝ} (hp : p ∈ Ioo 0 1) :
    quantile (gpdMeasure 0 β) p = -(β * log (1 - p)) := by
  rw [quantile_gpdMeasure hβ hp, gpdOfExp, ite_eq_left rfl, mul_neg]

/-! ### Tail averages, the mean, and the mean excess function -/

/-- **Tail integral of the GPD quantile.** For `ξ < 1` and `α < 1`,
`∫_α^1 q(u) du = (1 − α)(q(α) + β)/(1 − ξ)`, where `q(u) = gpdOfExp ξ β (−log(1 − u))`. -/
theorem setIntegral_gpdOfExp_Ioo (hβ : 0 < β) (hξ1 : ξ < 1) {α : ℝ} (hα1 : α < 1) :
    ∫ u in Ioo α 1, gpdOfExp ξ β (-log (1 - u)) =
      (1 - α) * (gpdOfExp ξ β (-log (1 - α)) + β) / (1 - ξ) := by
  have hs : 0 < 1 - α := sub_pos.2 hα1
  have hs0 : 1 - α ≠ 0 := hs.ne'
  have h1ξ : 1 - ξ ≠ 0 := (sub_pos.2 hξ1).ne'
  have hβ0 : β ≠ 0 := hβ.ne'
  -- move to an interval integral and substitute `t = 1 − u`
  rw [← integral_Ioc_eq_integral_Ioo, ← intervalIntegral.integral_of_le hα1.le,
    intervalIntegral.integral_comp_sub_left (fun t ↦ gpdOfExp ξ β (-log t)) 1, sub_self]
  by_cases hξ : ξ = 0
  · subst hξ
    simp only [gpdOfExp, ite_true]
    rw [intervalIntegral.integral_const_mul, intervalIntegral.integral_neg, integral_log]
    simp only [log_zero, mul_zero, sub_zero, add_zero]
    ring
  · -- on `(0, 1 − α]` the integrand is `(β/ξ)(t^{−ξ} − 1)`
    have hcongr : ∫ t in (0 : ℝ)..1 - α, gpdOfExp ξ β (-log t) =
        ∫ t in (0 : ℝ)..1 - α, β / ξ * (t ^ (-ξ) - 1) := by
      refine intervalIntegral.integral_congr_ae (ae_of_all _ fun t ht ↦ ?_)
      rw [uIoc_of_le hs.le] at ht
      rw [gpdOfExp, ite_eq_right hξ, rpow_def_of_pos ht.1]
      ring_nf
    have hint : IntervalIntegrable (fun t : ℝ ↦ t ^ (-ξ)) volume 0 (1 - α) :=
      intervalIntegral.intervalIntegrable_rpow' (by linarith)
    have h1ξ' : -ξ + 1 ≠ 0 := (by linarith : (0 : ℝ) < -ξ + 1).ne'
    rw [hcongr, intervalIntegral.integral_const_mul, intervalIntegral.integral_sub hint
      intervalIntegrable_const, integral_rpow (Or.inl (by linarith)),
      intervalIntegral.integral_const, zero_rpow h1ξ', rpow_add_one hs0, smul_eq_mul, mul_one,
      sub_zero, sub_zero, gpdOfExp, ite_eq_right hξ,
      show ξ * -log (1 - α) = log (1 - α) * -ξ by ring, ← rpow_def_of_pos hs]
    field_simp
    ring

/-- **Expected shortfall of a GPD loss** (MFE eq. (5.19) at threshold `0`): for `ξ < 1`, the
average of the quantile function over `(α, 1)` is `(q(α) + β)/(1 − ξ)`, i.e.
`ES_α = (VaR_α + β)/(1 − ξ)`. -/
theorem setIntegral_quantile_gpdMeasure (hβ : 0 < β) (hξ1 : ξ < 1) {α : ℝ}
    (hα : α ∈ Ioo 0 1) :
    (1 - α)⁻¹ * ∫ u in Ioo α 1, quantile (gpdMeasure ξ β) u =
      (quantile (gpdMeasure ξ β) α + β) / (1 - ξ) := by
  have hs0 : 1 - α ≠ 0 := (sub_pos.2 hα.2).ne'
  rw [setIntegral_congr_fun measurableSet_Ioo fun u hu ↦
      quantile_gpdMeasure hβ ⟨hα.1.trans hu.1, hu.2⟩,
    setIntegral_gpdOfExp_Ioo hβ hξ1 hα.2, quantile_gpdMeasure hβ hα]
  field_simp

/-- **The mean of the GPD** is `β/(1 − ξ)` for `ξ < 1`. -/
theorem integral_id_gpdMeasure (hβ : 0 < β) (hξ1 : ξ < 1) :
    ∫ x, x ∂(gpdMeasure ξ β) = β / (1 - ξ) := by
  rw [integral_eq_setIntegral_quantile (f := fun x ↦ x) aestronglyMeasurable_id,
    setIntegral_congr_fun measurableSet_Ioo fun u hu ↦ quantile_gpdMeasure hβ hu,
    setIntegral_gpdOfExp_Ioo hβ hξ1 one_pos, sub_zero, log_one, neg_zero, gpdOfExp_zero,
    one_mul, zero_add]

/-- **Excesses of the GPD law are GPD**: for a threshold `u ≥ 0` inside the support, the law of
`X − u` given `X > u` is `GPD(ξ, β + ξu)`. -/
theorem map_cond_gpdMeasure (hβ : 0 < β) {u : ℝ} (hu : 0 ≤ u) (hsupp : 0 < 1 + ξ * (u / β)) :
    ((gpdMeasure ξ β)[|Ioi u]).map (· - u) = gpdMeasure ξ (β + ξ * u) := by
  have hβ' : 0 < β + ξ * u := by
    have : β + ξ * u = β * (1 + ξ * (u / β)) := by field_simp
    rw [this]
    exact mul_pos hβ hsupp
  have htail : 0 < gpdTail ξ β u := gpdTail_pos (by rwa [max_eq_left hu])
  have hIoi : gpdMeasure ξ β (Ioi u) = ENNReal.ofReal (gpdTail ξ β u) := by
    rw [← measure_cdf (gpdMeasure ξ β),
      StieltjesFunction.measure_Ioi _ (tendsto_cdf_atTop (gpdMeasure ξ β)),
      cdf_gpdMeasure hβ, gpdCDF, sub_sub_cancel]
  have hne : gpdMeasure ξ β (Ioi u) ≠ 0 := by
    rw [hIoi]
    exact (ENNReal.ofReal_pos.2 htail).ne'
  have : IsProbabilityMeasure ((gpdMeasure ξ β)[|Ioi u]) := cond_isProbabilityMeasure hne
  have hmeas : Measurable fun x : ℝ ↦ x - u := measurable_sub_const u
  refine Measure.ext_of_Iic _ _ fun a ↦ ?_
  have hpre : Ioi u ∩ (fun x ↦ x - u) ⁻¹' Iic a = Ioc u (a + u) := by
    ext y
    simp
  have hIoc : gpdMeasure ξ β (Ioc u (a + u)) =
      ENNReal.ofReal (gpdCDF ξ β (a + u) - gpdCDF ξ β u) := by
    rw [← measure_cdf (gpdMeasure ξ β), StieltjesFunction.measure_Ioc, cdf_gpdMeasure hβ,
      cdf_gpdMeasure hβ]
  rw [Measure.map_apply hmeas measurableSet_Iic, cond_apply measurableSet_Ioi, hpre, hIoc, hIoi,
    ← ofReal_cdf, cdf_gpdMeasure hβ']
  rcases lt_or_ge a 0 with ha | ha
  · -- a negative excess level has no mass on either side
    have hmono : gpdCDF ξ β (a + u) ≤ gpdCDF ξ β u := by
      rw [← cdf_gpdMeasure hβ, ← cdf_gpdMeasure hβ]
      exact monotone_cdf _ (by linarith)
    rw [ENNReal.ofReal_of_nonpos (sub_nonpos.2 hmono), mul_zero, gpdCDF,
      gpdTail_of_nonpos ha.le, sub_self, ENNReal.ofReal_zero]
  · rw [add_comm a u, show gpdCDF ξ β (u + a) - gpdCDF ξ β u =
        gpdTail ξ β u * gpdCDF ξ (β + ξ * u) a by
      rw [gpdCDF, gpdCDF, gpdCDF, gpdTail_add hβ hu hsupp ha]
      ring,
      ENNReal.ofReal_mul htail.le, ← mul_assoc,
      ENNReal.inv_mul_cancel (ENNReal.ofReal_pos.2 htail).ne' ENNReal.ofReal_ne_top, one_mul]

/-- **The mean excess function of the GPD is linear** (MFE Exercise 5.19(b)): for `ξ < 1` and a
threshold `u ≥ 0` inside the support, `e(u) = E[X − u | X > u] = (β + ξu)/(1 − ξ)`. -/
theorem integral_sub_cond_gpdMeasure (hβ : 0 < β) (hξ1 : ξ < 1) {u : ℝ} (hu : 0 ≤ u)
    (hsupp : 0 < 1 + ξ * (u / β)) :
    ∫ x, (x - u) ∂((gpdMeasure ξ β)[|Ioi u]) = (β + ξ * u) / (1 - ξ) := by
  have hβ' : 0 < β + ξ * u := by
    have : β + ξ * u = β * (1 + ξ * (u / β)) := by field_simp
    rw [this]
    exact mul_pos hβ hsupp
  have hmap := integral_map (μ := (gpdMeasure ξ β)[|Ioi u]) (φ := fun x ↦ x - u) (f := id)
    (measurable_sub_const u).aemeasurable aestronglyMeasurable_id
  rw [map_cond_gpdMeasure hβ hu hsupp] at hmap
  simp only [id] at hmap
  rw [← hmap, integral_id_gpdMeasure hβ' hξ1]

end MathFin
