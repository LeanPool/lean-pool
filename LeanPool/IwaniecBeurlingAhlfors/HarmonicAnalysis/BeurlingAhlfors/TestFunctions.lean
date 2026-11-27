/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.TestFunctions.Approx
public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.Complex.RadialIntegral
import Mathlib.Analysis.SpecialFunctions.Gaussian.GaussianIntegral
import Mathlib.MeasureTheory.Integral.Lebesgue.DominatedConvergence
import Mathlib.MeasureTheory.Measure.Lebesgue.EqHaar

/-!
# Dragičević's test functions

For `n ∈ ℕ` and `α ∈ ℝ`, Dragičević's test functions (2011 article, p. 465) are
`f_{n,α} (z) = z^n |z|^{−2α} g_n (|z|)` (`HarmonicAnalysis.BeurlingAhlfors.testFun`), where
`g_n (x) = 1` for `x ≤ 1` and `g_n (x) = exp (−(x − 1)^n)` for `x > 1`
(`HarmonicAnalysis.BeurlingAhlfors.testCutoff`; the source's example of a sufficiently smooth,
rapidly decaying `g_n` equal to `1` on `[0, 1]`). Only `n = 2` is used below; `n = 1`, with the
cutoff `g₂`, is in `HarmonicAnalysis.BeurlingAhlfors.TestFunctions.One`. The derivatives are
the pointwise Wirtinger derivatives `HarmonicAnalysis.dz`, `HarmonicAnalysis.dzbar`. A remark, not
used or proved here: for `α < 1` they agree almost everywhere with the weak ones, since `f_{2,α}`
is `C¹` off `0` (`g₂` is `C¹` at `1`) and `C²` off `0` and the unit circle, and near `0`,
`f = O (|z|^{2−2α})`, `∇f = O (|z|^{1−2α})` (for `α = 1`, `f = z / (conj z)` and the distribution
`∂²f`
has a Dirac mass at `0`). The article takes `p > 2` and `α < 1/p`; the statements below hold for
every `p` and `α` in the range given.

## Main results, for `n = 2`

* On the punctured unit disc (proof of Theorem 1.1, pp. 466–467):
  `∂²f = (2 − α)(1 − α) |z|^{−2α}` and `∂_zbar²f = (−α)(−α − 1) (z / (conj z))² |z|^{−2α}`
  (`dz_dz_testFun_of_norm_lt_one`, `dzbar_dzbar_testFun_of_norm_lt_one`), so that, for
  `0 < α < 1/p`, `∫_Δ |∂²f|^p = π / (1 − αp) ((2 − α)(1 − α))^p` and
  `∫_Δ |∂_zbar²f|^p = π / (1 − αp) (α (α + 1))^p` (`lintegral_dz_dz_testFun_ball`,
  `lintegral_dzbar_dzbar_testFun_ball`).
* Outside the disc, the integrals of `|∂²f|^p` and `|∂_zbar²f|^p` stay bounded for `α ∈ [0, 1]`
  (`exists_bound_testFun_compl_ball`; the article, p. 467:
  `|Dⁿ f (z)| ≤ P (n, α) |z|^M e^{−(|z| − 1)^n}`).
* `f_{2,α} ∈ W^{2,p}` for `1 ≤ p`, `0 < α < 1/p` (asserted without proof in the article, p. 465,
  for `p > 2`; Exercise 4.1 of the lecture notes), in the form used: Schwartz functions `φ_k` with
  `∂_zbar²φ_k → ∂_zbar²f` and `∂²φ_k → ∂²f` in `L^p` (`exists_schwartz_tendsto_testFun`).

## Proofs

Near a point `z` with `|z| < 1`, resp. `|z| > 1`, `f_{2,α} (w) = w² K (|w|²)` with
`K (t) = t^{−α}`, resp. `K (t) = t^{−α} E (t)`, `E (t) = exp (−(√t − 1)²)`
(`testFun_eventuallyEq_of_norm_lt_one`, `testFun_eventuallyEq_of_one_lt_norm`), so that
`∂²f = 2 K + 4 t K' + t² K''` and `∂_zbar²f = z⁴ K''` at `t = |z|²`
(`HarmonicAnalysis.dz_dz_sq_mul_ofReal_radial`; outside the disc,
`dz_dz_testFun_of_one_lt_norm`, `dzbar_dzbar_testFun_of_one_lt_norm`). Outside the disc,
`|K^{(j)} (t)| ≤ 16 E (t)` for `α ∈ [0, 1]`, so that
`|∂²f|, |∂_zbar²f| ≤ 32 (1 + |z|²)² e^{−(|z| − 1)²}` (`norm_testFun_le_of_one_lt_norm`), whose
`p`-th
power is integrable on `|z| ≥ 1` (`lintegral_compl_ball_majorant_lt_top`, by polar coordinates
and a Gamma-type integral). The approximation of `f_{2,α}` is in
`HarmonicAnalysis.BeurlingAhlfors.TestFunctions.Approx`.

## References

* O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471: p. 465 and the proof of Theorem 1.1, pp. 466–467.
* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), §4.1 (Exercise 4.1, Proposition 4.2).
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped SchwartzMap ENNReal Real ComplexConjugate

namespace HarmonicAnalysis.BeurlingAhlfors

/-! ### Local forms: `f_{2,α} (z) = z² K (|z|²)` -/

/-- Locality of `∂²`: functions that agree near `z` have the same `∂²` at `z`. -/
theorem dz_dz_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) : dz (dz f) z = dz (dz g) z :=
  Filter.EventuallyEq.dz_eq (h.eventuallyEq_nhds.mono fun _ hw => hw.dz_eq)

/-- Locality of `∂_zbar²`: functions that agree near `z` have the same `∂_zbar²` at `z`. -/
theorem dzbar_dzbar_congr {f g : ℂ → ℂ} {z : ℂ} (h : f =ᶠ[𝓝 z] g) :
    dzbar (dzbar f) z = dzbar (dzbar g) z :=
  Filter.EventuallyEq.dzbar_eq (h.eventuallyEq_nhds.mono fun _ hw => hw.dzbar_eq)

/-- On the unit disc, `f_{2,α} (w) = w² K₀ (|w|²)`, `K₀ (t) = t^{−α}`. -/
theorem testFun_eventuallyEq_of_norm_lt_one (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    testFun 2 α =ᶠ[𝓝 z] fun w => w ^ 2 * ((Complex.normSq w ^ (-α) : ℝ) : ℂ) := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w
    (hw : ‖w‖ < 1)
  rw [testFun, testCutoff, ite_eq_left hw.le, mul_one, normSq_rpow_neg]

/-- Outside the closed unit disc, `f_{2,α} (w) = w² K₁ (|w|²)`, `K₁ (t) = t^{−α} E (t)`,
`E (t) = exp (−(√t − 1)²)`. -/
theorem testFun_eventuallyEq_of_one_lt_norm (α : ℝ) {z : ℂ} (hz : 1 < ‖z‖) :
    testFun 2 α =ᶠ[𝓝 z] fun w =>
      w ^ 2 * ((Complex.normSq w ^ (-α) * expCutoff (Complex.normSq w) : ℝ) : ℂ) := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w
    (hw : 1 < ‖w‖)
  rw [testFun, testCutoff, ite_eq_right (not_le.2 hw), normSq_rpow_neg, expCutoff_normSq]

/-! ### The punctured unit disc -/

/-- On the punctured unit disc, `∂²f_{2,α} (z) = (2 − α)(1 − α) |z|^{−2α}`. -/
theorem dz_dz_testFun_of_norm_lt_one (α : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    dz (dz (testFun 2 α)) z = (((2 - α) * (1 - α) * ‖z‖ ^ (-2 * α) : ℝ) : ℂ) := by
  have ht : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  have h := dz_dz_sq_mul_ofReal_radial
    (Real.contDiffAt_rpow_const_of_ne (p := -α) (n := 2) ht.ne')
  beta_reduce at h
  rw [dz_dz_congr (testFun_eventuallyEq_of_norm_lt_one α hz), h, deriv_deriv_rpow_neg,
    deriv_rpow_neg]
  beta_reduce
  rw [Real.rpow_sub_one ht.ne', Real.rpow_sub ht, Real.rpow_two, normSq_rpow_neg]
  congr 1
  field_simp
  ring

/-- On the punctured unit disc, `∂_zbar²f_{2,α} (z) = (−α)(−α − 1) (z / (conj z))² |z|^{−2α}`. -/
theorem dzbar_dzbar_testFun_of_norm_lt_one (α : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    dzbar (dzbar (testFun 2 α)) z =
      (((-α) * (-α - 1) : ℝ) : ℂ) * (z / conj z) ^ 2 * ((‖z‖ ^ (-2 * α) : ℝ) : ℂ) := by
  have ht : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  have h := dzbar_dzbar_sq_mul_ofReal_radial
    (Real.contDiffAt_rpow_const_of_ne (p := -α) (n := 2) ht.ne')
  beta_reduce at h
  rw [dzbar_dzbar_congr (testFun_eventuallyEq_of_norm_lt_one α hz), h, deriv_deriv_rpow_neg]
  beta_reduce
  rw [Real.rpow_sub ht, Real.rpow_two, normSq_rpow_neg]
  have hc : (conj z : ℂ) ≠ 0 := (map_ne_zero _).2 hz0
  have hn : ((Complex.normSq z : ℝ) : ℂ) = z * conj z := (Complex.mul_conj z).symm
  push_cast
  rw [hn]
  field_simp
  ring

/-- `∫_Δ |∂²f_{2,α}|^p = π / (1 − αp) ((2 − α)(1 − α))^p` for `0 < α < 1/p`. -/
theorem lintegral_dz_dz_testFun_ball {p α : ℝ} (hp : 1 < p) (hα0 : 0 < α) (hα : α * p < 1) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ‖dz (dz (testFun 2 α)) z‖ₑ ^ p =
      ENNReal.ofReal (π / (1 - α * p) * ((2 - α) * (1 - α)) ^ p) := by
  have hp0 : 0 < p := by linarith
  have hα1 : α < 1 := by nlinarith
  have hc : 0 < (2 - α) * (1 - α) := by nlinarith
  have h : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Metric.ball (0 : ℂ) 1 →
      ‖dz (dz (testFun 2 α)) z‖ₑ ^ p =
        ENNReal.ofReal (((2 - α) * (1 - α)) ^ p) * ENNReal.ofReal (‖z‖ ^ (-(2 * α * p))) := by
    filter_upwards [Measure.ae_ne volume 0] with z hz0 hz
    rw [mem_ball_zero_iff] at hz
    rw [dz_dz_testFun_of_norm_lt_one α hz0 hz, ← ofReal_norm, Complex.norm_real,
      Real.norm_eq_abs, abs_of_nonneg (by positivity),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, ← ENNReal.ofReal_mul (by positivity),
      Real.mul_rpow hc.le (by positivity), ← Real.rpow_mul (norm_nonneg z)]
    congr 3
    ring
  rw [setLIntegral_congr_fun_ae Metric.isOpen_ball.measurableSet h,
    lintegral_const_mul _ (by fun_prop), lintegral_ball_norm_rpow (by linarith),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : 1 - α * p ≠ 0 := by linarith
  have : 2 - 2 * α * p ≠ 0 := by linarith
  field_simp

/-- `∫_Δ |∂_zbar²f_{2,α}|^p = π / (1 − αp) (α (α + 1))^p` for `0 < α < 1/p`. -/
theorem lintegral_dzbar_dzbar_testFun_ball {p α : ℝ} (hp : 1 < p) (hα0 : 0 < α)
    (hα : α * p < 1) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ‖dzbar (dzbar (testFun 2 α)) z‖ₑ ^ p =
      ENNReal.ofReal (π / (1 - α * p) * (α * (α + 1)) ^ p) := by
  have hp0 : 0 < p := by linarith
  have hc : 0 < α * (α + 1) := by positivity
  have h : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Metric.ball (0 : ℂ) 1 →
      ‖dzbar (dzbar (testFun 2 α)) z‖ₑ ^ p =
        ENNReal.ofReal ((α * (α + 1)) ^ p) * ENNReal.ofReal (‖z‖ ^ (-(2 * α * p))) := by
    filter_upwards [Measure.ae_ne volume 0] with z hz0 hz
    rw [mem_ball_zero_iff] at hz
    rw [dzbar_dzbar_testFun_of_norm_lt_one α hz0 hz, ← ofReal_norm, norm_mul, norm_mul,
      norm_pow, norm_div, Complex.norm_conj, div_self (norm_ne_zero_iff.2 hz0), one_pow, mul_one,
      Complex.norm_real, Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (show 0 ≤ (-α) * (-α - 1) by nlinarith), abs_of_nonneg (by positivity),
      show (-α) * (-α - 1) = α * (α + 1) by ring,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, ← ENNReal.ofReal_mul (by positivity),
      Real.mul_rpow hc.le (by positivity), ← Real.rpow_mul (norm_nonneg z)]
    congr 3
    ring
  rw [setLIntegral_congr_fun_ae Metric.isOpen_ball.measurableSet h,
    lintegral_const_mul _ (by fun_prop), lintegral_ball_norm_rpow (by linarith),
    ← ENNReal.ofReal_mul (by positivity)]
  congr 1
  have : 1 - α * p ≠ 0 := by linarith
  have : 2 - 2 * α * p ≠ 0 := by linarith
  field_simp

/-! ### Outside the unit disc -/

theorem contDiffAt_rpow_neg_mul_expCutoff (α : ℝ) {t : ℝ} (ht : 0 < t) :
    ContDiffAt ℝ 2 (fun s : ℝ => s ^ (-α) * expCutoff s) t :=
  (Real.contDiffAt_rpow_const_of_ne ht.ne').mul (contDiffAt_expCutoff ht.ne')

/-- For `|z| > 1`: `∂²f_{2,α} (z) = 2 K₁ (t) + 4 t K₁' (t) + t² K₁'' (t)`, with
`K₁ (t) = t^{−α} E (t)` and `t = |z|²`. -/
theorem dz_dz_testFun_of_one_lt_norm (α : ℝ) {z : ℂ} (hz : 1 < ‖z‖) :
    dz (dz (testFun 2 α)) z =
      ((2 * (Complex.normSq z ^ (-α) * expCutoff (Complex.normSq z)) +
          4 * Complex.normSq z *
            deriv (fun s : ℝ => s ^ (-α) * expCutoff s) (Complex.normSq z) +
          Complex.normSq z ^ 2 *
            deriv (deriv fun s : ℝ => s ^ (-α) * expCutoff s) (Complex.normSq z) : ℝ) : ℂ) := by
  have ht : 0 < Complex.normSq z := by rw [Complex.normSq_eq_norm_sq]; nlinarith
  have h := dz_dz_sq_mul_ofReal_radial (contDiffAt_rpow_neg_mul_expCutoff α ht)
  beta_reduce at h
  rw [dz_dz_congr (testFun_eventuallyEq_of_one_lt_norm α hz), h]

/-- For `|z| > 1`: `∂_zbar²f_{2,α} (z) = z⁴ K₁'' (|z|²)`, with `K₁ (t) = t^{−α} E (t)`. -/
theorem dzbar_dzbar_testFun_of_one_lt_norm (α : ℝ) {z : ℂ} (hz : 1 < ‖z‖) :
    dzbar (dzbar (testFun 2 α)) z =
      z ^ 4 * ((deriv (deriv fun s : ℝ => s ^ (-α) * expCutoff s) (Complex.normSq z) : ℝ) :
        ℂ) := by
  have ht : 0 < Complex.normSq z := by rw [Complex.normSq_eq_norm_sq]; nlinarith
  have h := dzbar_dzbar_sq_mul_ofReal_radial (contDiffAt_rpow_neg_mul_expCutoff α ht)
  beta_reduce at h
  rw [dzbar_dzbar_congr (testFun_eventuallyEq_of_one_lt_norm α hz), h]

/-- For `t ≥ 1` and `α ∈ [0, 1]`: `|K₁^{(j)} (t)| ≤ 16 E (t)`, `j ≤ 2`, with
`K₁ (t) = t^{−α} E (t)`. -/
theorem derivBoundTwo_rpow_neg_mul_expCutoff {α t : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) (ht : 1 ≤ t) :
    DerivBoundTwo (fun s : ℝ => s ^ (-α) * expCutoff s) t (16 * expCutoff t) :=
  ((derivBoundTwo_rpow_neg hα.1 hα.2 ht).mul (Real.contDiffAt_rpow_const_of_ne (by linarith))
    (contDiffAt_expCutoff (by linarith)) (derivBoundTwo_expCutoff ht)).mono
    (le_of_eq (by ring))

/-- For `|z| > 1` and `α ∈ [0, 1]`:
`|∂²f_{2,α} (z)|, |∂_zbar²f_{2,α} (z)| ≤ 32 (1 + |z|²)² e^{−(|z| − 1)²}`. -/
theorem norm_testFun_le_of_one_lt_norm {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : 1 < ‖z‖) :
    ‖dz (dz (testFun 2 α)) z‖ ≤ 32 * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) ∧
      ‖dzbar (dzbar (testFun 2 α)) z‖ ≤
        32 * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) := by
  have ht : 1 < Complex.normSq z := by rw [Complex.normSq_eq_norm_sq]; nlinarith
  have h := norm_dz_dz_sq_mul_ofReal_radial_le
    (contDiffAt_rpow_neg_mul_expCutoff α (by linarith))
    (derivBoundTwo_rpow_neg_mul_expCutoff hα ht.le)
  beta_reduce at h
  rw [expCutoff_normSq] at h
  rw [dz_dz_congr (testFun_eventuallyEq_of_one_lt_norm α hz),
    dzbar_dzbar_congr (testFun_eventuallyEq_of_one_lt_norm α hz)]
  exact ⟨h.1.trans_eq (by ring), h.2.trans_eq (by ring)⟩

/-- `(1 + r²)² e^{−(r − 1)²} ≤ 4 e^{5/4} r⁴ e^{−r}` for `r ≥ 1`, since
`(r − 1)² ≥ r − 5/4`. -/
theorem one_add_sq_sq_mul_exp_le {r : ℝ} (hr : 1 ≤ r) :
    (1 + r ^ 2) ^ 2 * Real.exp (-(r - 1) ^ 2) ≤
      4 * Real.exp (5 / 4) * (r ^ 4 * Real.exp (-r)) := by
  have h1 : (1 + r ^ 2) ^ 2 ≤ 4 * r ^ 4 := by
    have : 1 + r ^ 2 ≤ 2 * r ^ 2 := by nlinarith
    calc (1 + r ^ 2) ^ 2 ≤ (2 * r ^ 2) ^ 2 := pow_le_pow_left₀ (by positivity) this 2
      _ = 4 * r ^ 4 := by ring
  have h2 : Real.exp (-(r - 1) ^ 2) ≤ Real.exp (5 / 4) * Real.exp (-r) := by
    rw [← Real.exp_add]
    exact Real.exp_le_exp.2 (by nlinarith [sq_nonneg (r - 3 / 2)])
  calc (1 + r ^ 2) ^ 2 * Real.exp (-(r - 1) ^ 2) ≤
        (4 * r ^ 4) * (Real.exp (5 / 4) * Real.exp (-r)) :=
        mul_le_mul h1 h2 (Real.exp_pos _).le (by positivity)
    _ = _ := by ring

/-- The majorant `(c (1 + |z|²)² e^{−(|z| − 1)²})^p` is integrable outside the unit disc: by
polar coordinates and `r (1 + r²)^{2p} e^{−p (r − 1)²} ≤ C r^{4p + 1} e^{−p r}`. -/
theorem lintegral_compl_ball_majorant_lt_top {p : ℝ} (hp : 0 < p) {c : ℝ} (hc : 0 ≤ c) :
    ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ,
      ENNReal.ofReal (c * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2))) ^ p < ∞ := by
  set g : ℝ → ℝ≥0∞ := (Ici (1 : ℝ)).indicator
    fun r => ENNReal.ofReal (c * ((1 + r ^ 2) ^ 2 * Real.exp (-(r - 1) ^ 2))) ^ p with hg_def
  have hg : Measurable g := (by fun_prop : Measurable fun r : ℝ =>
    ENNReal.ofReal (c * ((1 + r ^ 2) ^ 2 * Real.exp (-(r - 1) ^ 2))) ^ p).indicator
      measurableSet_Ici
  have hind : (Metric.ball (0 : ℂ) 1)ᶜ.indicator (fun z =>
      ENNReal.ofReal (c * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2))) ^ p) =
      fun z => g ‖z‖ := by
    funext z
    by_cases hz : 1 ≤ ‖z‖
    · rw [hg_def, indicator_of_mem (by simpa using hz), indicator_of_mem (mem_Ici.2 hz)]
    · rw [hg_def, indicator_of_notMem (by simpa using hz), indicator_of_notMem (by simpa using hz)]
  rw [← lintegral_indicator Metric.isOpen_ball.measurableSet.compl, hind, lintegral_comp_norm hg]
  refine ENNReal.mul_lt_top ENNReal.ofReal_lt_top ?_
  set K := (4 * c * Real.exp (5 / 4)) ^ p with hK
  have hint : IntegrableOn (fun r : ℝ => K * (r ^ (4 * p + 1) * Real.exp (-p * r ^ (1 : ℝ))))
      (Ioi 0) :=
    (integrableOn_rpow_mul_exp_neg_mul_rpow (by linarith) one_pos hp).const_mul K
  refine lt_of_le_of_lt (setLIntegral_mono' measurableSet_Ioi fun r (hr : 0 < r) => ?_)
    hint.lintegral_lt_top
  by_cases h1 : 1 ≤ r
  · rw [hg_def, indicator_of_mem (mem_Ici.2 h1),
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp.le, ← ENNReal.ofReal_mul hr.le]
    apply ENNReal.ofReal_le_ofReal
    have hm := mul_le_mul_of_nonneg_left (one_add_sq_sq_mul_exp_le h1) hc
    calc r * (c * ((1 + r ^ 2) ^ 2 * Real.exp (-(r - 1) ^ 2))) ^ p ≤
          r * (4 * c * Real.exp (5 / 4) * (r ^ 4 * Real.exp (-r))) ^ p :=
          mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity)
            (hm.trans_eq (by ring)) hp.le) hr.le
      _ = K * (r ^ (4 * p + 1) * Real.exp (-p * r ^ (1 : ℝ))) := by
        rw [Real.mul_rpow (x := 4 * c * Real.exp (5 / 4)) (by positivity) (by positivity),
          Real.mul_rpow (x := r ^ 4) (by positivity) (by positivity),
          ← Real.rpow_natCast_mul hr.le,
          ← Real.exp_mul, Real.rpow_add_one hr.ne', Real.rpow_one,
          show -r * p = -p * r by ring, hK]
        push_cast
        ring
  · rw [hg_def, indicator_of_notMem (by simpa using h1), mul_zero]
    exact zero_le

/-- The unit circle is a null set. -/
theorem ae_norm_ne_one : ∀ᵐ z ∂(volume : Measure ℂ), ‖z‖ ≠ 1 := by
  filter_upwards [measure_eq_zero_iff_ae_notMem.1
    (Measure.addHaar_sphere (volume : Measure ℂ) 0 1)] with z hz
  rwa [mem_sphere_zero_iff_norm] at hz

/-- Outside the unit disc, `∫ |∂²f_{2,α}|^p` and `∫ |∂_zbar²f_{2,α}|^p` are bounded uniformly in
`α ∈ [0, 1]`. -/
theorem exists_bound_testFun_compl_ball {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖dz (dz (testFun 2 α)) z‖ₑ ^ p ≤ ENNReal.ofReal C ∧
        ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖dzbar (dzbar (testFun 2 α)) z‖ₑ ^ p ≤
          ENNReal.ofReal C := by
  set I := ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ,
    ENNReal.ofReal (32 * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2))) ^ p with hI_def
  have hI : I < ∞ := lintegral_compl_ball_majorant_lt_top hp (by norm_num)
  refine ⟨I.toReal, fun α hα => ?_⟩
  rw [ENNReal.ofReal_toReal hI.ne]
  have hae : ∀ᵐ z ∂(volume.restrict (Metric.ball (0 : ℂ) 1)ᶜ), 1 < ‖z‖ := by
    filter_upwards [ae_restrict_of_ae ae_norm_ne_one,
      ae_restrict_mem Metric.isOpen_ball.measurableSet.compl] with z hz1 hz2
    rw [mem_compl_iff, mem_ball_zero_iff, not_lt] at hz2
    exact lt_of_le_of_ne hz2 (Ne.symm hz1)
  constructor
  · refine lintegral_mono_ae (hae.mono fun z hz => ?_)
    rw [← ofReal_norm]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (norm_testFun_le_of_one_lt_norm hα hz).1)
      hp.le
  · refine lintegral_mono_ae (hae.mono fun z hz => ?_)
    rw [← ofReal_norm]
    exact ENNReal.rpow_le_rpow (ENNReal.ofReal_le_ofReal (norm_testFun_le_of_one_lt_norm hα hz).2)
      hp.le

/-! ### Approximation in `W^{2,p}` -/

/-- Dominated convergence in `L^p`: if `F_k → G` a.e., `|F_k| ≤ D` a.e. and `∫ (2 D)^p < ∞`,
then `‖F_k − G‖_p → 0`. -/
theorem tendsto_eLpNorm_sub_of_dominated {p : ℝ} (hp : 0 < p) {F : ℕ → ℂ → ℂ} {G : ℂ → ℂ}
    {D : ℂ → ℝ} (hF : ∀ k, Measurable (F k)) (hG : Measurable G)
    (hFD : ∀ k, ∀ᵐ z ∂(volume : Measure ℂ), ‖F k z‖ ≤ D z)
    (hD : ∫⁻ z, ENNReal.ofReal (2 * D z) ^ p ≠ ∞)
    (hlim : ∀ᵐ z ∂(volume : Measure ℂ), Tendsto (fun k => F k z) atTop (𝓝 (G z))) :
    Tendsto (fun k => eLpNorm (fun z => F k z - G z) (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hGD : ∀ᵐ z ∂(volume : Measure ℂ), ‖G z‖ ≤ D z := by
    filter_upwards [hlim, ae_all_iff.2 hFD] with z hz hzD
    exact le_of_tendsto' hz.norm hzD
  have hint := tendsto_lintegral_of_dominated_convergence (μ := volume)
    (F := fun k z => ‖F k z - G z‖ₑ ^ p) (f := fun _ => 0)
    (fun z => ENNReal.ofReal (2 * D z) ^ p) (fun k => ((hF k).sub hG).eNorm.pow_const p)
    (fun k => by
      filter_upwards [hFD k, hGD] with z h1 h2
      rw [← ofReal_norm]
      exact ENNReal.rpow_le_rpow
        (ENNReal.ofReal_le_ofReal ((norm_sub_le _ _).trans (by linarith))) hp.le)
    hD (by
      filter_upwards [hlim] with z hz
      have h0 : Tendsto (fun k => F k z - G z) atTop (𝓝 0) := by
        simpa using hz.sub_const (G z)
      have := (ENNReal.continuous_rpow_const (y := p)).tendsto _ |>.comp
        ((continuous_eNorm.tendsto _).comp h0)
      simpa [Function.comp_def, ENNReal.zero_rpow_of_pos hp] using this)
  rw [lintegral_zero] at hint
  have h := (ENNReal.continuous_rpow_const (y := 1 / p)).tendsto _ |>.comp hint
  rw [ENNReal.zero_rpow_of_pos (by positivity)] at h
  refine h.congr fun k => ?_
  rw [eLpNorm_eq_lintegral_rpow_eNorm_toReal (by simpa using hp) ENNReal.ofReal_ne_top
    (show Measurable fun z => F k z - G z from (hF k).sub hG).aestronglyMeasurable,
    ENNReal.toReal_ofReal hp.le]
  rfl

/-- `f_{2,α} ∈ W^{2,p}` for `1 ≤ p < ∞`, `0 < α < 1/p` (Dragičević 2011, p. 465, where `p > 2`), in
the form used: there are Schwartz functions `φ_k` with `∂_zbar²φ_k → ∂_zbar²f_{2,α}` and
`∂²φ_k → ∂²f_{2,α}` in `L^p`.

The article asserts this without proof, and the lecture notes leave it as an exercise (Exercise
4.1); the proof is the standard approximation argument:
`φ_k (z) = z² K_k (|z|²)` (`HarmonicAnalysis.BeurlingAhlfors.approxSchwartz`) regularises the
singularity at `0` (`|z|^{−2α}` becomes `(|z|² + ε_k)^{−α}`), smooths the cutoff `g₂` at `|z| = 1`,
where it is only `C¹`, and truncates at infinity. Off `0` and the unit circle, `∂²φ_k → ∂²f` and
`∂_zbar²φ_k → ∂_zbar²f` pointwise, with a domination uniform in `k`, by `8 |z|^{−2α}` on the disc
and by
`C (1 + |z|²)² e^{−(|z| − 1)²}` outside it, whose `p`-th power is integrable; dominated convergence
concludes. -/
theorem exists_schwartz_tendsto_testFun {p α : ℝ} (hp : 1 ≤ p) (hα0 : 0 < α) (hα : α * p < 1) :
    ∃ φ : ℕ → 𝓢(ℂ, ℂ),
      Tendsto (fun k => eLpNorm (fun z => (dzbarCLM ^ 2) (φ k) z - dzbar (dzbar (testFun 2 α)) z)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (fun z => (dzCLM ^ 2) (φ k) z - dz (dz (testFun 2 α)) z)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hα1 : α < 1 := by nlinarith
  obtain ⟨C, hC⟩ := exists_norm_approxSchwartz_le_of_one_lt hα0.le hα1.le
  set c := max C 0 with hc_def
  have hc : 0 ≤ c := le_max_right _ _
  set D : ℂ → ℝ := fun z => if ‖z‖ < 1 then 8 * ‖z‖ ^ (-2 * α) else
    c * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) with hD_def
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 ∧ ‖z‖ ≠ 1 :=
    (Measure.ae_ne volume 0).and ae_norm_ne_one
  -- the domination, uniform in `k`
  have hdom : ∀ k z, z ≠ 0 → ‖z‖ ≠ 1 → ‖(dzbarCLM ^ 2) (approxSchwartz α k) z‖ ≤ D z ∧
      ‖(dzCLM ^ 2) (approxSchwartz α k) z‖ ≤ D z := by
    intro k z hz0 hz1
    rcases lt_or_gt_of_ne hz1 with h | h
    · rw [hD_def]
      simp only [ite_eq_left h]
      obtain ⟨h1, h2⟩ := norm_approxSchwartz_le_of_lt_one hα0 hα1 k hz0 h
      exact ⟨h2.trans (by nlinarith [Real.rpow_nonneg (norm_nonneg z) (-2 * α)]), h1⟩
    · rw [hD_def]
      simp only [ite_eq_right (not_lt.2 h.le)]
      obtain ⟨h1, h2⟩ := hC k z h
      have hm : 0 ≤ (1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2) := by positivity
      exact ⟨h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hm),
        h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hm)⟩
  -- the pointwise limits
  have hlim : ∀ z, z ≠ 0 → ‖z‖ ≠ 1 →
      Tendsto (fun k => (dzCLM ^ 2) (approxSchwartz α k) z) atTop
          (𝓝 (dz (dz (testFun 2 α)) z)) ∧
        Tendsto (fun k => (dzbarCLM ^ 2) (approxSchwartz α k) z) atTop
          (𝓝 (dzbar (dzbar (testFun 2 α)) z)) := by
    intro z hz0 hz1
    simp only [dzCLM_sq_approxSchwartz, dzbarCLM_sq_approxSchwartz]
    have ht0 : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
    rcases lt_or_gt_of_ne hz1 with h | h
    · have ht1 : Complex.normSq z < 1 := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
      have := tendsto_dz_dz_sq_mul_ofReal_radial (fun k => contDiffAt_two_approxProfile α k z)
        (Real.contDiffAt_rpow_const_of_ne (p := -α) (n := 2) ht0.ne')
        (tendstoTwo_approxProfile_of_lt_one α ht0 ht1)
      beta_reduce at this
      rwa [dz_dz_congr (testFun_eventuallyEq_of_norm_lt_one α h),
        dzbar_dzbar_congr (testFun_eventuallyEq_of_norm_lt_one α h)]
    · have ht1 : 1 < Complex.normSq z := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith
      have := tendsto_dz_dz_sq_mul_ofReal_radial (fun k => contDiffAt_two_approxProfile α k z)
        (contDiffAt_rpow_neg_mul_expCutoff α ht0) (tendstoTwo_approxProfile_of_one_lt α ht1)
      beta_reduce at this
      rwa [dz_dz_congr (testFun_eventuallyEq_of_one_lt_norm α h),
        dzbar_dzbar_congr (testFun_eventuallyEq_of_one_lt_norm α h)]
  -- the integrability of the majorant
  have hfin : ∫⁻ z, ENNReal.ofReal (2 * D z) ^ p ≠ ∞ := by
    rw [← lintegral_add_compl _ (Metric.isOpen_ball (x := (0 : ℂ)) (ε := 1)).measurableSet]
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · rw [setLIntegral_congr_fun Metric.isOpen_ball.measurableSet
        (g := fun z => ENNReal.ofReal (16 ^ p) * ENNReal.ofReal (‖z‖ ^ (-(2 * α * p))))
        (fun z hz => ?_)]
      · rw [lintegral_const_mul _ (by fun_prop), lintegral_ball_norm_rpow (by linarith)]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      · rw [mem_ball_zero_iff] at hz
        rw [hD_def]
        simp only [ite_eq_left hz]
        rw [← mul_assoc, show (2 : ℝ) * 8 = 16 by norm_num,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le,
          Real.mul_rpow (by norm_num) (by positivity), ← Real.rpow_mul (norm_nonneg _),
          ENNReal.ofReal_mul (by positivity)]
        congr 3
        ring
    · refine ne_of_lt (lt_of_le_of_lt (setLIntegral_mono'
        Metric.isOpen_ball.measurableSet.compl fun z hz => ?_)
        (lintegral_compl_ball_majorant_lt_top hp0 (c := 2 * c) (by positivity)))
      rw [mem_compl_iff, mem_ball_zero_iff, not_lt] at hz
      rw [hD_def]
      simp only [ite_eq_right (not_lt.2 hz)]
      rw [← mul_assoc]
  refine ⟨approxSchwartz α, ?_, ?_⟩
  · exact tendsto_eLpNorm_sub_of_dominated hp0 (fun k => (SchwartzMap.continuous _).measurable)
      (measurable_dzbar _) (fun k => hae.mono fun z hz => (hdom k z hz.1 hz.2).1) hfin
      (hae.mono fun z hz => (hlim z hz.1 hz.2).2)
  · exact tendsto_eLpNorm_sub_of_dominated hp0 (fun k => (SchwartzMap.continuous _).measurable)
      (measurable_dz _) (fun k => hae.mono fun z hz => (hdom k z hz.1 hz.2).2) hfin
      (hae.mono fun z hz => (hlim z hz.1 hz.2).1)

end HarmonicAnalysis.BeurlingAhlfors
