/-
Copyright (c) 2026 rainrzk. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: rainrzk
-/
module

public import LeanPool.PolylogIntegrals.Defs
public import Mathlib.Analysis.Calculus.SmoothSeries
public import Mathlib.NumberTheory.ZetaValues
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
public import Mathlib.Analysis.SpecialFunctions.Log.NegMulLog

/-!
# The dilogarithm

Mathlib has no polylogarithms, so this file collects the facts about `Li_s` that the proofs use,
with the dilogarithm `Li_2` as the main case. `Lir s` and `Li s` both unfold to the series
`∑_{n ≥ 0} z^(n+1)/(n+1)^s`, so its basic properties are proved once, over `𝕜 = ℝ` or `ℂ`
(`RCLike`). The complex counterparts are in `LeanPolyLog.Lemmas.DilogComplex`.

## Main results

The series over `𝕜 = ℝ` or `ℂ`:
* `LeanPolyLog.Dilog.summable_pow_div_pow`, `LeanPolyLog.Dilog.continuousOn_tsum_pow_div_pow`:
  for `s ≥ 2` it converges absolutely, and is continuous, on the closed unit disk (M-test).
* `LeanPolyLog.Dilog.hasDerivAt_tsum_pow_div_pow`: termwise differentiation on the open disk.
* `LeanPolyLog.Dilog.tsum_pow_div_pow_sq`: the duplication formula.

The real polylogarithm `Lir`:
* `LeanPolyLog.Dilog.Lir_one`: `Li_1(x) = -log(1 - x)` for `|x| < 1`.
* `LeanPolyLog.Dilog.Lir_two_one`, `LeanPolyLog.Dilog.Lir_two_neg_one`,
  `LeanPolyLog.Dilog.Lir_two_one_half`: `Li_2(1) = π²/6`, `Li_2(-1) = -π²/12` and
  `Li_2(1/2) = π²/12 - log²2/2`.
* `LeanPolyLog.Dilog.continuousOn_Lir`: for `s ≥ 2`, `Li_s` is continuous on `[-1, 1]`.
* `LeanPolyLog.Dilog.hasDerivAt_Lir_succ`, `LeanPolyLog.Dilog.hasDerivAt_Lir_two`: for
  `0 < |x| < 1`, `Li_(s+1)'(x) = Li_s(x)/x`; in particular `Li_2'(x) = -log(1 - x)/x`.
* `LeanPolyLog.Dilog.Lir_sq`, `LeanPolyLog.Dilog.Lir_two_sq`: the duplication formula
  `Li_s(x²) = 2^(s-1) (Li_s(x) + Li_s(-x))` for `|x| ≤ 1`.
* `LeanPolyLog.Dilog.Lir_two_add_Lir_two_one_sub`: Euler's reflection formula
  `Li_2(x) + Li_2(1 - x) = π²/6 - log x · log(1 - x)` for `0 < x < 1`.
* `LeanPolyLog.Dilog.Lir_two_neg_add_Lir_two_div`: Landen's identity
  `Li_2(-y) + Li_2(y/(1+y)) = -½ log²(1+y)` for `0 ≤ y ≤ 1`.

## Proof sketch

The derivative comes from termwise differentiation on a ball of radius `r < 1`, where the
derivatives of the terms are bounded by `rⁿ`; the derivative series `∑ xⁿ/(n+1)^s` equals
`Li_s(x)/x`, and `Li_1(x) = -log(1 - x)` is Mathlib's `Real.hasSum_pow_div_log_of_abs_lt_one`.
The duplication formula splits the series into even and odd terms. Reflection and Landen are
proved by showing that the difference of the two sides is continuous on a closed interval with
derivative `0` inside (`LeanPolyLog.Dilog.eq_of_hasDerivAt_eq_zero`, from the mean value theorem),
and evaluating it at `0`. For reflection this needs the continuity of `log t · log(1 - t)` at `0`
(`LeanPolyLog.Dilog.continuous_log_mul_log_one_sub`).
-/

open Real Set

namespace LeanPolyLog.Dilog

/-! ### The polylog series over `ℝ` or `ℂ` -/

section RCLike

variable {𝕜 : Type*} [RCLike 𝕜]

/-- The norm of the `n`-th term of the polylog series. -/
public theorem norm_pow_div_pow (s n : ℕ) (z : 𝕜) :
    ‖z ^ (n + 1) / ((n + 1 : 𝕜) ^ s)‖ = ‖z‖ ^ (n + 1) / ((n : ℝ) + 1) ^ s := by
  have hn : ‖(n + 1 : 𝕜)‖ = (n : ℝ) + 1 := by exact_mod_cast RCLike.norm_natCast (K := 𝕜) (n + 1)
  rw [norm_div, norm_pow, norm_pow, hn]

/-- `∑_{n ≥ 0} 1/(n+1)^s` converges for `s ≥ 2`. -/
public theorem summable_one_div_succ_pow {s : ℕ} (hs : 2 ≤ s) :
    Summable fun n : ℕ => (1 : ℝ) / ((n : ℝ) + 1) ^ s := by
  have h := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < s))
  exact h.congr fun n => by push_cast; rfl

/-- On the closed unit disk, the `n`-th term of the polylog series is bounded by `1/(n+1)^s`. -/
public theorem norm_pow_div_pow_le {s : ℕ} {z : 𝕜} (hz : ‖z‖ ≤ 1) (n : ℕ) :
    ‖z ^ (n + 1) / ((n + 1 : 𝕜) ^ s)‖ ≤ 1 / ((n : ℝ) + 1) ^ s := by
  rw [norm_pow_div_pow]
  gcongr
  exact pow_le_one₀ (norm_nonneg z) hz

/-- For `s ≥ 2` the polylog series converges (absolutely) on the closed unit disk. -/
public theorem summable_pow_div_pow {s : ℕ} (hs : 2 ≤ s) {z : 𝕜} (hz : ‖z‖ ≤ 1) :
    Summable fun n : ℕ => z ^ (n + 1) / ((n + 1 : 𝕜) ^ s) :=
  (summable_one_div_succ_pow hs).of_norm_bounded (norm_pow_div_pow_le hz)

/-- For `s ≥ 2` the polylog series is continuous on the closed unit disk (Weierstrass M-test). -/
public theorem continuousOn_tsum_pow_div_pow {s : ℕ} (hs : 2 ≤ s) :
    ContinuousOn (fun z : 𝕜 => ∑' n : ℕ, z ^ (n + 1) / ((n + 1 : 𝕜) ^ s))
      (Metric.closedBall 0 1) :=
  continuousOn_tsum (fun n => by fun_prop) (summable_one_div_succ_pow hs)
    fun n _ hz => norm_pow_div_pow_le (mem_closedBall_zero_iff.1 hz) n

/-- Termwise differentiation of the polylog series on the open unit disk:
`d/dz ∑ z^(n+1)/(n+1)^(s+1) = ∑ z^n/(n+1)^s`. -/
public theorem hasDerivAt_tsum_pow_div_pow (s : ℕ) {z : 𝕜} (hz : ‖z‖ < 1) :
    HasDerivAt (fun w : 𝕜 => ∑' n : ℕ, w ^ (n + 1) / ((n + 1 : 𝕜) ^ (s + 1)))
      (∑' n : ℕ, z ^ n / ((n + 1 : 𝕜) ^ s)) z := by
  obtain ⟨r, hzr, hr1⟩ := exists_between hz
  have hr0 : 0 < r := (norm_nonneg z).trans_lt hzr
  refine hasDerivAt_tsum_of_isPreconnected (u := fun n : ℕ => r ^ n)
    (g' := fun n w => w ^ n / ((n + 1 : 𝕜) ^ s))
    (summable_geometric_of_lt_one hr0.le hr1) Metric.isOpen_ball
    (convex_ball (0 : 𝕜) r).isPreconnected (fun n w _ => ?_) (fun n w hw => ?_)
    (Metric.mem_ball_self hr0) (by simp) (mem_ball_zero_iff.2 hzr)
  · have h := (hasDerivAt_pow (n + 1) w).div_const ((n + 1 : 𝕜) ^ (s + 1))
    convert h using 1
    have hn : (n + 1 : 𝕜) ≠ 0 := by exact_mod_cast n.succ_ne_zero
    rw [Nat.add_sub_cancel]
    push_cast
    field_simp
    ring
  · have hw' : ‖w‖ ≤ r := (mem_ball_zero_iff.1 hw).le
    have hn : ‖(n + 1 : 𝕜)‖ = (n : ℝ) + 1 := by
      exact_mod_cast RCLike.norm_natCast (K := 𝕜) (n + 1)
    rw [norm_div, norm_pow, norm_pow, hn]
    calc ‖w‖ ^ n / ((n : ℝ) + 1) ^ s ≤ ‖w‖ ^ n :=
          div_le_self (by positivity) (one_le_pow₀ (by linarith [n.cast_nonneg (α := ℝ)]))
      _ ≤ r ^ n := pow_le_pow_left₀ (norm_nonneg w) hw' n

/-- Away from `0`, `∑ z^n/(n+1)^s = (∑ z^(n+1)/(n+1)^s) / z`. -/
public theorem tsum_pow_div_pow_eq_div (s : ℕ) {z : 𝕜} (hz : z ≠ 0) :
    ∑' n : ℕ, z ^ n / ((n + 1 : 𝕜) ^ s) = (∑' n : ℕ, z ^ (n + 1) / ((n + 1 : 𝕜) ^ s)) / z := by
  rw [eq_div_iff hz, mul_comm, ← tsum_mul_left]
  congr 1
  funext n
  ring

/-- The duplication formula for the polylog series:
`∑ (z²)^(n+1)/(n+1)^s = 2^(s-1) (∑ z^(n+1)/(n+1)^s + ∑ (-z)^(n+1)/(n+1)^s)`.
Only even powers survive in the sum on the right. -/
public theorem tsum_pow_div_pow_sq {s : ℕ} (hs : 2 ≤ s) {z : 𝕜} (hz : ‖z‖ ≤ 1) :
    ∑' n : ℕ, (z ^ 2) ^ (n + 1) / ((n + 1 : 𝕜) ^ s) = 2 ^ (s - 1) *
      (∑' n : ℕ, z ^ (n + 1) / ((n + 1 : 𝕜) ^ s)
        + ∑' n : ℕ, (-z) ^ (n + 1) / ((n + 1 : 𝕜) ^ s)) := by
  set a : ℕ → 𝕜 := fun n => z ^ (n + 1) / ((n + 1 : 𝕜) ^ s) + (-z) ^ (n + 1) / ((n + 1 : 𝕜) ^ s)
  have hz' : ‖-z‖ ≤ 1 := by rwa [norm_neg]
  have hz2 : ‖z ^ 2‖ ≤ 1 := by rw [norm_pow]; exact pow_le_one₀ (norm_nonneg z) hz
  have ha : HasSum a (∑' n : ℕ, z ^ (n + 1) / ((n + 1 : 𝕜) ^ s)
      + ∑' n : ℕ, (-z) ^ (n + 1) / ((n + 1 : 𝕜) ^ s)) :=
    (summable_pow_div_pow hs hz).hasSum.add (summable_pow_div_pow hs hz').hasSum
  have he : HasSum (fun k => a (2 * k)) 0 := by
    convert hasSum_zero with k
    simp only [a]
    rw [Odd.neg_pow ⟨k, rfl⟩ z]
    ring
  have ho : HasSum (fun k => a (2 * k + 1))
      (2 / 2 ^ s * ∑' n : ℕ, (z ^ 2) ^ (n + 1) / ((n + 1 : 𝕜) ^ s)) := by
    convert (summable_pow_div_pow hs hz2).hasSum.mul_left (2 / 2 ^ s) using 1
    funext k
    simp only [a]
    rw [Even.neg_pow ⟨k + 1, by ring⟩ z, ← pow_mul]
    push_cast
    have hk : (2 * (k : 𝕜) + 1 + 1) = 2 * ((k : 𝕜) + 1) := by ring
    have hk0 : (k : 𝕜) + 1 ≠ 0 := by exact_mod_cast k.succ_ne_zero
    rw [hk, mul_pow]
    field_simp
    ring
  have h := ha.unique (he.even_add_odd ho)
  obtain ⟨t, rfl⟩ : ∃ t, s = t + 1 := ⟨s - 1, by omega⟩
  rw [h, Nat.add_sub_cancel, pow_succ]
  field_simp
  ring

end RCLike

/-! ### Constancy from a vanishing derivative -/

/-- A real function that is continuous on `[a, b]` and has derivative `0` on `(a, b)` takes the
same value at `a` and `b`. -/
public theorem eq_of_hasDerivAt_eq_zero {f : ℝ → ℝ} {a b : ℝ} (hab : a ≤ b)
    (hc : ContinuousOn f (Icc a b)) (hd : ∀ x ∈ Ioo a b, HasDerivAt f 0 x) : f a = f b := by
  rcases hab.eq_or_lt with rfl | hlt
  · rfl
  obtain ⟨c, -, hc'⟩ := exists_hasDerivAt_eq_slope f (fun _ => 0) hlt hc hd
  rcases div_eq_zero_iff.1 hc'.symm with h | h <;> linarith

/-! ### The real polylogarithm `Lir` -/

/-- `Li_s(0) = 0`. -/
@[simp]
public theorem Lir_zero (s : ℕ) : Lir s 0 = 0 := by
  simp [Lir]

/-- For `s ≥ 2` the series of `Li_s(x)` converges for `|x| ≤ 1`. -/
public theorem hasSum_Lir {s : ℕ} (hs : 2 ≤ s) {x : ℝ} (hx : |x| ≤ 1) :
    HasSum (fun n : ℕ => x ^ (n + 1) / ((n + 1 : ℝ) ^ s)) (Lir s x) :=
  (summable_pow_div_pow hs (by rwa [Real.norm_eq_abs])).hasSum

/-- For `s ≥ 2`, `Li_s` is continuous on `[-1, 1]`. -/
public theorem continuousOn_Lir {s : ℕ} (hs : 2 ≤ s) : ContinuousOn (Lir s) (Icc (-1) 1) := by
  have h := continuousOn_tsum_pow_div_pow (𝕜 := ℝ) hs
  rw [Real.closedBall_eq_Icc, zero_sub, zero_add] at h
  exact h

/-- `Li_1(x) = -log(1 - x)` for `|x| < 1`. -/
public theorem Lir_one {x : ℝ} (hx : |x| < 1) : Lir 1 x = -log (1 - x) := by
  unfold Lir
  simp only [pow_one]
  exact (Real.hasSum_pow_div_log_of_abs_lt_one hx).tsum_eq

/-- `Li_2(1) = ζ(2) = π²/6`. -/
public theorem Lir_two_one : Lir 2 1 = π ^ 2 / 6 := by
  have h := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
  simp only [Finset.range_one, Finset.sum_singleton, Nat.cast_zero, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow, div_zero, sub_zero, Nat.cast_add, Nat.cast_one] at h
  unfold Lir
  simpa only [one_pow] using h.tsum_eq

/-- `d/dx Li_(s+1)(x) = Li_s(x)/x` for `0 < |x| < 1`. -/
public theorem hasDerivAt_Lir_succ (s : ℕ) {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt (Lir (s + 1)) (Lir s x / x) x := by
  have h := hasDerivAt_tsum_pow_div_pow (𝕜 := ℝ) s (by rwa [Real.norm_eq_abs])
  rw [tsum_pow_div_pow_eq_div s hx0] at h
  exact h

/-- `d/dx Li_2(x) = -log(1 - x)/x` for `0 < |x| < 1`. -/
public theorem hasDerivAt_Lir_two {x : ℝ} (hx : |x| < 1) (hx0 : x ≠ 0) :
    HasDerivAt (Lir 2) (-log (1 - x) / x) x := by
  have h := hasDerivAt_Lir_succ 1 hx hx0
  rwa [Lir_one hx] at h

/-- The duplication formula `Li_s(x²) = 2^(s-1) (Li_s(x) + Li_s(-x))` for `|x| ≤ 1`, `s ≥ 2`. -/
public theorem Lir_sq {s : ℕ} (hs : 2 ≤ s) {x : ℝ} (hx : |x| ≤ 1) :
    Lir s (x ^ 2) = 2 ^ (s - 1) * (Lir s x + Lir s (-x)) :=
  tsum_pow_div_pow_sq hs (by rwa [Real.norm_eq_abs])

/-- The duplication formula `Li_2(x²) = 2 (Li_2(x) + Li_2(-x))` for `|x| ≤ 1`. -/
public theorem Lir_two_sq {x : ℝ} (hx : |x| ≤ 1) : Lir 2 (x ^ 2) = 2 * (Lir 2 x + Lir 2 (-x)) := by
  simpa using Lir_sq le_rfl hx

/-- `Li_2(-1) = -η(2) = -π²/12`, from the duplication formula at `x = 1`. -/
public theorem Lir_two_neg_one : Lir 2 (-1) = -(π ^ 2 / 12) := by
  have h := Lir_two_sq (x := 1) (by norm_num)
  rw [one_pow, Lir_two_one] at h
  linarith

/-! ### Euler's reflection formula -/

/-- `log t · log(1 - t)` is continuous at `0` (Lean's `log 0 = 0`): near `0` it is bounded by
`2 |t log t|`, since `|log(1 - t)| ≤ |t|/(1 - |t|)`. -/
public theorem continuousAt_log_mul_log_one_sub_zero :
    ContinuousAt (fun t : ℝ => log t * log (1 - t)) 0 := by
  rw [ContinuousAt, log_zero, zero_mul]
  refine squeeze_zero_norm' (a := fun t => 2 * |t * log t|) ?_ ?_
  · filter_upwards [Ioo_mem_nhds (by norm_num : (-1 / 2 : ℝ) < 0) (by norm_num : (0 : ℝ) < 1 / 2)]
      with t ht
    have ht' : |t| < 1 / 2 := abs_lt.2 ⟨by linarith [ht.1], ht.2⟩
    have h := Real.abs_log_sub_add_sum_range_le (by linarith : |t| < 1) 0
    simp only [Finset.range_zero, Finset.sum_empty, zero_add, pow_one] at h
    have h2 : |log (1 - t)| ≤ 2 * |t| := by
      refine h.trans ?_
      rw [div_le_iff₀ (by linarith)]
      nlinarith [abs_nonneg t]
    rw [Real.norm_eq_abs, abs_mul, abs_mul]
    nlinarith [abs_nonneg (log t)]
  · have h := ((continuous_mul_log.abs).const_mul 2).tendsto 0
    simpa using h

/-- `t ↦ log t · log(1 - t)` is continuous on `ℝ` (with Lean's `log 0 = 0`). -/
public theorem continuous_log_mul_log_one_sub : Continuous fun t : ℝ => log t * log (1 - t) := by
  refine continuous_iff_continuousAt.2 fun t => ?_
  rcases eq_or_ne t 0 with rfl | h0
  · exact continuousAt_log_mul_log_one_sub_zero
  rcases eq_or_ne t 1 with rfl | h1
  · have h := continuousAt_log_mul_log_one_sub_zero.comp_of_eq
      (continuous_sub_left (1 : ℝ)).continuousAt (sub_self 1)
    convert h using 1
    funext u
    simp only [Function.comp_apply, sub_sub_cancel]
    ring
  exact (continuousAt_log h0).mul
    ((continuous_sub_left 1).continuousAt.log (sub_ne_zero.2 h1.symm))

/-- Euler's reflection formula: `Li_2(x) + Li_2(1 - x) = π²/6 - log x · log(1 - x)` for
`0 < x < 1`. -/
public theorem Lir_two_add_Lir_two_one_sub {x : ℝ} (hx0 : 0 < x) (hx1 : x < 1) :
    Lir 2 x + Lir 2 (1 - x) = π ^ 2 / 6 - log x * log (1 - x) := by
  have hderiv : ∀ t ∈ Ioo 0 x,
      HasDerivAt (fun t => Lir 2 t + Lir 2 (1 - t) + log t * log (1 - t)) 0 t := by
    rintro t ⟨ht0, htx⟩
    have ht1 : t < 1 := htx.trans hx1
    have h1 : HasDerivAt (Lir 2) (-log (1 - t) / t) t :=
      hasDerivAt_Lir_two (abs_lt.2 ⟨by linarith, ht1⟩) ht0.ne'
    have h2 : HasDerivAt (fun t => Lir 2 (1 - t)) (-log (1 - (1 - t)) / (1 - t) * (-1)) t :=
      (hasDerivAt_Lir_two (abs_lt.2 ⟨by linarith, by linarith⟩) (by linarith)).comp t
        ((hasDerivAt_id' t).const_sub 1)
    have h3 : HasDerivAt (fun t => log t * log (1 - t))
        (t⁻¹ * log (1 - t) + log t * (-1 / (1 - t))) t :=
      (Real.hasDerivAt_log ht0.ne').mul
        (((hasDerivAt_id' t).const_sub 1).log (by linarith))
    refine ((h1.add h2).add h3).congr_deriv ?_
    rw [sub_sub_cancel]
    have : 1 - t ≠ 0 := by linarith
    field_simp
    ring
  have hcont : ContinuousOn (fun t => Lir 2 t + Lir 2 (1 - t) + log t * log (1 - t))
      (Icc 0 x) := by
    refine (((continuousOn_Lir le_rfl).mono (Icc_subset_Icc (by norm_num) hx1.le)).add
      ((continuousOn_Lir le_rfl).comp (continuous_sub_left 1).continuousOn ?_)).add
      continuous_log_mul_log_one_sub.continuousOn
    rintro t ⟨ht0, htx⟩
    exact ⟨by linarith, by linarith⟩
  have h := eq_of_hasDerivAt_eq_zero hx0.le hcont hderiv
  simp only [Lir_zero, sub_zero, Lir_two_one, log_zero, zero_mul, add_zero, zero_add] at h
  linarith

/-- `Li_2(1/2) = π²/12 - log²2/2`, from the reflection formula at `x = 1/2`. -/
public theorem Lir_two_one_half : Lir 2 (1 / 2) = π ^ 2 / 12 - log 2 ^ 2 / 2 := by
  have h := Lir_two_add_Lir_two_one_sub (x := 1 / 2) (by norm_num) (by norm_num)
  rw [show (1 : ℝ) - 1 / 2 = 1 / 2 by norm_num, one_div, Real.log_inv] at h
  rw [one_div]
  linear_combination h / 2

/-! ### Landen's identity -/

/-- Landen's identity on `[0, 1]`: `Li_2(-y) + Li_2(y/(1+y)) = -½ log²(1+y)`. -/
public theorem Lir_two_neg_add_Lir_two_div {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    Lir 2 (-y) + Lir 2 (y / (1 + y)) = -(log (1 + y) ^ 2 / 2) := by
  have hderiv : ∀ t ∈ Ioo 0 y,
      HasDerivAt (fun t => Lir 2 (-t) + Lir 2 (t / (1 + t)) + log (1 + t) ^ 2 / 2) 0 t := by
    rintro t ⟨ht0, hty⟩
    have ht1 : t < 1 := hty.trans_le hy1
    have hpos : 0 < 1 + t := by linarith
    have h1 : HasDerivAt (fun t => Lir 2 (-t)) (-log (1 - -t) / -t * (-1)) t :=
      (hasDerivAt_Lir_two (x := -t) (by rw [abs_neg, abs_of_pos ht0]; exact ht1)
        (by linarith)).comp t (hasDerivAt_neg t)
    have hu : HasDerivAt (fun t => t / (1 + t)) ((1 * (1 + t) - t * 1) / (1 + t) ^ 2) t :=
      (hasDerivAt_id' t).div ((hasDerivAt_id' t).const_add 1) hpos.ne'
    have hu0 : t / (1 + t) ≠ 0 := div_ne_zero ht0.ne' hpos.ne'
    have hu1 : |t / (1 + t)| < 1 := by
      rw [abs_of_pos (div_pos ht0 hpos), div_lt_one hpos]
      linarith
    have h2 := (hasDerivAt_Lir_two hu1 hu0).comp t hu
    have h3 : HasDerivAt (fun t => log (1 + t) ^ 2 / 2)
        (↑2 * log (1 + t) ^ (2 - 1) * (1 / (1 + t)) / 2) t :=
      ((((hasDerivAt_id' t).const_add 1).log hpos.ne').pow 2).div_const 2
    refine ((h1.add h2).add h3).congr_deriv ?_
    have hlog : log (1 - t / (1 + t)) = -log (1 + t) := by
      rw [show 1 - t / (1 + t) = (1 + t)⁻¹ by field_simp; ring, Real.log_inv]
    rw [hlog, sub_neg_eq_add]
    field_simp
    ring
  have hcont : ContinuousOn (fun t => Lir 2 (-t) + Lir 2 (t / (1 + t)) + log (1 + t) ^ 2 / 2)
      (Icc 0 y) := by
    have hne : ∀ t ∈ Icc (0 : ℝ) y, 1 + t ≠ 0 := fun t ht => by linarith [ht.1]
    have hmaps1 : MapsTo (fun t : ℝ => -t) (Icc 0 y) (Icc (-1) 1) := by
      rintro t ⟨ht0, hty⟩
      exact ⟨by linarith, by linarith⟩
    have hmaps2 : MapsTo (fun t : ℝ => t / (1 + t)) (Icc 0 y) (Icc (-1) 1) := by
      rintro t ⟨ht0, hty⟩
      have hpos : 0 < 1 + t := by linarith
      refine ⟨by linarith [div_nonneg ht0 hpos.le], ?_⟩
      rw [div_le_one hpos]
      linarith
    have hc1 : ContinuousOn (fun t : ℝ => Lir 2 (-t)) (Icc 0 y) :=
      (continuousOn_Lir le_rfl).comp continuousOn_neg hmaps1
    have hc2 : ContinuousOn (fun t : ℝ => Lir 2 (t / (1 + t))) (Icc 0 y) :=
      (continuousOn_Lir le_rfl).comp
        ((continuousOn_id' _).div (continuousOn_const.add (continuousOn_id' _)) hne) hmaps2
    have hc3 : ContinuousOn (fun t : ℝ => log (1 + t) ^ 2 / 2) (Icc 0 y) :=
      (((continuousOn_const.add (continuousOn_id' _)).log hne).pow 2).div_const 2
    exact (hc1.add hc2).add hc3
  have h := eq_of_hasDerivAt_eq_zero hy0 hcont hderiv
  simp only [neg_zero, Lir_zero, zero_div, add_zero, log_one, ne_eq, OfNat.ofNat_ne_zero,
    not_false_eq_true, zero_pow] at h
  linarith

end LeanPolyLog.Dilog
