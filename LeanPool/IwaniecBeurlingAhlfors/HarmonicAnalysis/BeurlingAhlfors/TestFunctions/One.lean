/-
Copyright (c) 2026 The-Anh Vu-Le. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: The-Anh Vu-Le
-/
module

-- Modified for Lean Pool. See the project entry module for upstream attribution.

public import LeanPool.IwaniecBeurlingAhlfors.HarmonicAnalysis.BeurlingAhlfors.TestFunctions
import Mathlib.Analysis.InnerProductSpace.Calculus

/-!
# Dragičević's test functions for `n = 1`

Dragičević's test functions (2011 article, p. 465) are `f_{n,α} (z) = z^n |z|^{−2α} g_n (|z|)`,
with a sufficiently smooth, rapidly decaying cutoff `g_n` equal to `1` on `[0, 1]`. The article's
example for `n = 1`, `g₁ (x) = exp (−(x − 1))` for `x > 1`, is not `C¹` at `1`. The cutoff here is
that of `n = 2`, `g₂ (x) = exp (−(x − 1)²)` for `x > 1`
(`HarmonicAnalysis.BeurlingAhlfors.testCutoff 2`), which is `C¹`:
`f_{1,α} (z) = z |z|^{−2α} g₂ (|z|)` (`HarmonicAnalysis.BeurlingAhlfors.testFunOne`). The choice
changes no limit, since the integrals outside the unit disc stay bounded while those on the disc
grow like `(1 − αp)⁻¹`, and the smooth approximations of `f_{2,α}`
(`HarmonicAnalysis.BeurlingAhlfors.approxProfile`) serve for `f_{1,α}` as they are.

On the unit disc, `f_{1,α} (z) = z |z|^{−2α}`: these are the functions `f_α` of
Baernstein–Montgomery-Smith (1999, §1), who continue them by `1/(conj z)` outside the disc and
compute
that `∫ |∂f_α|^p / ∫ |∂_zbar f_α|^p → (p − 1)^p` as `α → 1/p`.

With `t = |z|²` and `f (z) = z k (t)` for a real profile `k`, `∂f = k (t) + t k' (t)` and
`∂_zbar f = z² k' (t)` (`HarmonicAnalysis.dz_mul_ofReal_radial`,
`HarmonicAnalysis.dzbar_mul_ofReal_radial`, from `HarmonicAnalysis.dz_monomial_mul_radial` and
`HarmonicAnalysis.dzbar_monomial_mul_radial`).

## Main results, for `n = 1`

* On the punctured unit disc (Dragičević's proof of Theorem 1.1, pp. 466–467):
  `∂f = (1 − α) |z|^{−2α}` and `|∂_zbar f| = α |z|^{−2α}`, so that, for `0 < α < 1/p`,
  `∫_Δ |∂f|^p = π / (1 − αp) (1 − α)^p` and `∫_Δ |∂_zbar f|^p = π / (1 − αp) α^p`
  (`lintegral_dz_testFunOne_ball`, `lintegral_dzbar_testFunOne_ball`).
* Outside the disc, the integrals of `|∂f|^p` and `|∂_zbar f|^p` stay bounded for `α ∈ [0, 1]`
  (`exists_bound_testFunOne_compl_ball`).
* `f_{1,α} ∈ W^{1,p}` for `1 ≤ p`, `0 < α < 1/p` (asserted without proof in the article, p. 465;
  for `n = 1`, Exercise 2.19 of the lecture notes, whose hint is to approximate by smooth
  functions), in the form used: Schwartz functions `φ_k` with `∂_zbar φ_k → ∂_zbar f` and `∂φ_k →
  ∂f` in
  `L^p` (`exists_schwartz_tendsto_testFunOne`).

The limit of `‖∂f_{1,α}‖_p / ‖∂_zbar f_{1,α}‖_p` and the bound `p − 1 ≤ ‖𝓑‖_p` are in
`HarmonicAnalysis.BeurlingAhlfors.LowerBound`.

## Proofs

As for `n = 2` (`HarmonicAnalysis.BeurlingAhlfors.TestFunctions`), with first derivatives only.
Near `z` with `|z| < 1`, resp. `|z| > 1`, `f_{1,α} (w) = w K (|w|²)` with `K (t) = t^{−α}`, resp.
`K (t) = t^{−α} E (t)`, `E (t) = exp (−(√t − 1)²)`; outside the disc the bounds on `K` and `K'`
of the case `n = 2` give `|∂f|, |∂_zbar f| ≤ 32 (1 + |z|²)² e^{−(|z| − 1)²}`. The approximants are
`φ_k (z) = z K_k (|z|²)` (`approxSchwartzOne`), with the profiles `K_k` of the approximations of
`f_{2,α}` (`HarmonicAnalysis.BeurlingAhlfors.TestFunctions.Approx`): they regularise the
singularity at `0`, smooth the cutoff at `|z| = 1` and truncate at infinity; dominated
convergence, by `|z|^{−2α}` on the disc and the bounds of the case `n = 2` outside it.

## References

* O. Dragičević, *Some remarks on the `L^p` estimates for powers of the Ahlfors–Beurling
  operator*, Arch. Math. 96 (2011), 463–471: p. 465 and the proof of Theorem 1.1, pp. 466–467.
* O. Dragičević, *Analysis of the Ahlfors–Beurling transform*, lecture notes,
  [arXiv:2109.04555](https://arxiv.org/abs/2109.04555), Exercise 2.19 and §4.1.
* A. Baernstein II and S. J. Montgomery-Smith, *Some conjectures about integral means of `∂f` and
  `∂_zbar f`*, in: Complex analysis and differential equations (Uppsala, 1997), ed. C. Kiselman,
  Acta
  Univ. Upsaliensis C 64 (1999), 92–109, [arXiv:math/9709215](https://arxiv.org/abs/math/9709215),
  §1.
-/

@[expose] public section

noncomputable section

open MeasureTheory Filter Topology Set
open scoped SchwartzMap ENNReal Real ComplexConjugate ContDiff

namespace HarmonicAnalysis

/-! ### The first Wirtinger derivatives of `z k (|z|²)` -/

/-- `∂ (z k (|z|²)) = k (t) + t k' (t)`, `t = |z|²`, for a real profile `k` differentiable
at `t`. -/
theorem dz_mul_ofReal_radial {k : ℝ → ℝ} {z : ℂ} (hk : DifferentiableAt ℝ k (Complex.normSq z)) :
    dz (fun w => w * ((k (Complex.normSq w) : ℝ) : ℂ)) z =
      ((k (Complex.normSq z) + Complex.normSq z * deriv k (Complex.normSq z) : ℝ) : ℂ) := by
  have hK : DifferentiableAt ℝ (fun s => (k s : ℂ)) (Complex.normSq z) :=
    hk.hasDerivAt.ofReal_comp.differentiableAt
  have h := dz_monomial_mul_radial 1 0 hK
  have hf : (fun w : ℂ => w ^ 1 * conj w ^ 0 * ((k (Complex.normSq w) : ℝ) : ℂ)) =
      fun w => w * ((k (Complex.normSq w) : ℝ) : ℂ) := by
    funext w
    ring
  rw [hf, deriv_ofReal_comp] at h
  rw [h]
  simp only [Nat.cast_one, Nat.sub_self, pow_zero, pow_one, zero_add, one_mul, mul_one]
  push_cast
  rw [← Complex.mul_conj]

/-- `∂_zbar (z k (|z|²)) = z² k' (|z|²)` for a real profile `k` differentiable at `|z|²`. -/
theorem dzbar_mul_ofReal_radial {k : ℝ → ℝ} {z : ℂ}
    (hk : DifferentiableAt ℝ k (Complex.normSq z)) :
    dzbar (fun w => w * ((k (Complex.normSq w) : ℝ) : ℂ)) z =
      z ^ 2 * ((deriv k (Complex.normSq z) : ℝ) : ℂ) := by
  have hK : DifferentiableAt ℝ (fun s => (k s : ℂ)) (Complex.normSq z) :=
    hk.hasDerivAt.ofReal_comp.differentiableAt
  have h := dzbar_monomial_mul_radial 1 0 hK
  have hf : (fun w : ℂ => w ^ 1 * conj w ^ 0 * ((k (Complex.normSq w) : ℝ) : ℂ)) =
      fun w => w * ((k (Complex.normSq w) : ℝ) : ℂ) := by
    funext w
    ring
  rw [hf, deriv_ofReal_comp] at h
  rw [h]
  push_cast
  ring

/-- `|∂ (z k (|z|²))|, |∂_zbar (z k (|z|²))| ≤ 2 (1 + |z|²)² M` if `|k (|z|²)|, |k' (|z|²)| ≤ M`. -/
theorem norm_dz_mul_ofReal_radial_le {k : ℝ → ℝ} {z : ℂ} {M : ℝ}
    (hk : DifferentiableAt ℝ k (Complex.normSq z)) (h : DerivBoundTwo k (Complex.normSq z) M) :
    ‖dz (fun w => w * ((k (Complex.normSq w) : ℝ) : ℂ)) z‖ ≤ 2 * (1 + ‖z‖ ^ 2) ^ 2 * M ∧
      ‖dzbar (fun w => w * ((k (Complex.normSq w) : ℝ) : ℂ)) z‖ ≤
        2 * (1 + ‖z‖ ^ 2) ^ 2 * M := by
  rw [dz_mul_ofReal_radial hk, dzbar_mul_ofReal_radial hk, Complex.norm_real, Real.norm_eq_abs,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← Complex.normSq_eq_norm_sq]
  obtain ⟨h0, h1, -⟩ := h
  set t := Complex.normSq z
  have hM : 0 ≤ M := (abs_nonneg _).trans h0
  have ht0 : 0 ≤ t := Complex.normSq_nonneg z
  have e1 : |k t + t * deriv k t| ≤ |k t| + t * |deriv k t| := by
    refine (abs_add_le _ _).trans (le_of_eq ?_)
    rw [abs_mul, abs_of_nonneg ht0]
  have e2 := mul_le_mul_of_nonneg_left h1 ht0
  have e3 : (1 + t) * M ≤ 2 * (1 + t) ^ 2 * M := by
    have : 1 + t ≤ 2 * (1 + t) ^ 2 := by nlinarith
    exact mul_le_mul_of_nonneg_right this hM
  constructor
  · nlinarith
  · nlinarith

/-- If `f_k → g` with one derivative at `t = |z|²`, then `∂ (z f_k (|z|²)) → ∂ (z g (|z|²))` and
`∂_zbar (z f_k (|z|²)) → ∂_zbar (z g (|z|²))` at `z`. -/
theorem tendsto_dz_mul_ofReal_radial {f : ℕ → ℝ → ℝ} {g : ℝ → ℝ} {z : ℂ}
    (hf : ∀ k, DifferentiableAt ℝ (f k) (Complex.normSq z))
    (hg : DifferentiableAt ℝ g (Complex.normSq z)) (h : TendstoTwo f g (Complex.normSq z)) :
    Tendsto (fun k => dz (fun w => w * ((f k (Complex.normSq w) : ℝ) : ℂ)) z) atTop
        (𝓝 (dz (fun w => w * ((g (Complex.normSq w) : ℝ) : ℂ)) z)) ∧
      Tendsto (fun k => dzbar (fun w => w * ((f k (Complex.normSq w) : ℝ) : ℂ)) z) atTop
        (𝓝 (dzbar (fun w => w * ((g (Complex.normSq w) : ℝ) : ℂ)) z)) := by
  obtain ⟨h0, h1, -⟩ := h
  rw [dz_mul_ofReal_radial hg, dzbar_mul_ofReal_radial hg]
  constructor
  · refine ((Complex.continuous_ofReal.tendsto _).comp (h0.add (h1.const_mul _))).congr
      fun k => ?_
    rw [dz_mul_ofReal_radial (hf k)]
    rfl
  · refine (((Complex.continuous_ofReal.tendsto _).comp h1).const_mul _).congr fun k => ?_
    rw [dzbar_mul_ofReal_radial (hf k)]
    rfl

namespace BeurlingAhlfors

/-! ### The test functions -/

/-- Dragičević's test function for `n = 1` (2011, p. 465), `f_{1,α} (z) = z |z|^{−2α} g₂ (|z|)`,
with the cutoff `g₂` of `n = 2` in place of the article's example `g₁`, which is not `C¹` at `1`.
On the unit disc, it is the function `f_α` of Baernstein–Montgomery-Smith (1999, §1). -/
def testFunOne (α : ℝ) (z : ℂ) : ℂ :=
  z * ((‖z‖ ^ (-2 * α) * testCutoff 2 ‖z‖ : ℝ) : ℂ)

/-- On the unit disc, `f_{1,α} (w) = w K₀ (|w|²)`, `K₀ (t) = t^{−α}`. -/
theorem testFunOne_eventuallyEq_of_norm_lt_one (α : ℝ) {z : ℂ} (hz : ‖z‖ < 1) :
    testFunOne α =ᶠ[𝓝 z] fun w => w * ((Complex.normSq w ^ (-α) : ℝ) : ℂ) := by
  filter_upwards [(isOpen_lt continuous_norm continuous_const).mem_nhds hz] with w
    (hw : ‖w‖ < 1)
  rw [testFunOne, testCutoff, ite_eq_left hw.le, mul_one, normSq_rpow_neg]

/-- Outside the closed unit disc, `f_{1,α} (w) = w K₁ (|w|²)`, `K₁ (t) = t^{−α} E (t)`,
`E (t) = exp (−(√t − 1)²)`. -/
theorem testFunOne_eventuallyEq_of_one_lt_norm (α : ℝ) {z : ℂ} (hz : 1 < ‖z‖) :
    testFunOne α =ᶠ[𝓝 z] fun w =>
      w * ((Complex.normSq w ^ (-α) * expCutoff (Complex.normSq w) : ℝ) : ℂ) := by
  filter_upwards [(isOpen_lt continuous_const continuous_norm).mem_nhds hz] with w
    (hw : 1 < ‖w‖)
  rw [testFunOne, testCutoff, ite_eq_right (not_le.2 hw), normSq_rpow_neg, expCutoff_normSq]

/-! ### The punctured unit disc -/

/-- On the punctured unit disc, `∂f_{1,α} (z) = (1 − α) |z|^{−2α}`. -/
theorem dz_testFunOne_of_norm_lt_one (α : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    dz (testFunOne α) z = (((1 - α) * ‖z‖ ^ (-2 * α) : ℝ) : ℂ) := by
  have ht : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  have h := dz_mul_ofReal_radial
    ((Real.contDiffAt_rpow_const_of_ne (p := -α) (n := 1) ht.ne').differentiableAt one_ne_zero)
  beta_reduce at h
  rw [(testFunOne_eventuallyEq_of_norm_lt_one α hz).dz_eq, h, deriv_rpow_neg]
  beta_reduce
  rw [Real.rpow_sub_one ht.ne', normSq_rpow_neg]
  congr 1
  field_simp
  ring

/-- On the punctured unit disc, `∂_zbar f_{1,α} (z) = −α z² |z|^{−2α−2}`. -/
theorem dzbar_testFunOne_of_norm_lt_one (α : ℝ) {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    dzbar (testFunOne α) z = z ^ 2 * ((-α * Complex.normSq z ^ (-α - 1) : ℝ) : ℂ) := by
  have ht : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  have h := dzbar_mul_ofReal_radial
    ((Real.contDiffAt_rpow_const_of_ne (p := -α) (n := 1) ht.ne').differentiableAt one_ne_zero)
  beta_reduce at h
  rw [(testFunOne_eventuallyEq_of_norm_lt_one α hz).dzbar_eq, h, deriv_rpow_neg]

/-- On the punctured unit disc, `|∂_zbar f_{1,α} (z)| = α |z|^{−2α}` for `α ≥ 0`. -/
theorem norm_dzbar_testFunOne_of_norm_lt_one {α : ℝ} (hα : 0 ≤ α) {z : ℂ} (hz0 : z ≠ 0)
    (hz : ‖z‖ < 1) : ‖dzbar (testFunOne α) z‖ = α * ‖z‖ ^ (-2 * α) := by
  have ht : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  rw [dzbar_testFunOne_of_norm_lt_one α hz0 hz, norm_mul, norm_pow, Complex.norm_real,
    Real.norm_eq_abs, abs_mul, abs_neg, abs_of_nonneg hα,
    abs_of_nonneg (Real.rpow_nonneg ht.le _), ← Complex.normSq_eq_norm_sq,
    Real.rpow_sub_one ht.ne', normSq_rpow_neg]
  field_simp

/-- `∫_Δ |∂f_{1,α}|^p = π / (1 − αp) (1 − α)^p` for `0 < α < 1/p`. -/
theorem lintegral_dz_testFunOne_ball {p α : ℝ} (hp : 1 < p) (hα0 : 0 < α) (hα : α * p < 1) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ‖dz (testFunOne α) z‖ₑ ^ p =
      ENNReal.ofReal (π / (1 - α * p) * (1 - α) ^ p) := by
  have hp0 : 0 < p := by linarith
  have hα1 : α < 1 := by nlinarith
  have hc : 0 < 1 - α := by linarith
  have h : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Metric.ball (0 : ℂ) 1 →
      ‖dz (testFunOne α) z‖ₑ ^ p =
        ENNReal.ofReal ((1 - α) ^ p) * ENNReal.ofReal (‖z‖ ^ (-(2 * α * p))) := by
    filter_upwards [Measure.ae_ne volume 0] with z hz0 hz
    rw [mem_ball_zero_iff] at hz
    rw [dz_testFunOne_of_norm_lt_one α hz0 hz, ← ofReal_norm, Complex.norm_real,
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

/-- `∫_Δ |∂_zbar f_{1,α}|^p = π / (1 − αp) α^p` for `0 < α < 1/p`. -/
theorem lintegral_dzbar_testFunOne_ball {p α : ℝ} (hp : 1 < p) (hα0 : 0 < α)
    (hα : α * p < 1) :
    ∫⁻ z in Metric.ball (0 : ℂ) 1, ‖dzbar (testFunOne α) z‖ₑ ^ p =
      ENNReal.ofReal (π / (1 - α * p) * α ^ p) := by
  have hp0 : 0 < p := by linarith
  have h : ∀ᵐ z ∂(volume : Measure ℂ), z ∈ Metric.ball (0 : ℂ) 1 →
      ‖dzbar (testFunOne α) z‖ₑ ^ p =
        ENNReal.ofReal (α ^ p) * ENNReal.ofReal (‖z‖ ^ (-(2 * α * p))) := by
    filter_upwards [Measure.ae_ne volume 0] with z hz0 hz
    rw [mem_ball_zero_iff] at hz
    rw [← ofReal_norm, norm_dzbar_testFunOne_of_norm_lt_one hα0.le hz0 hz,
      ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le, ← ENNReal.ofReal_mul (by positivity),
      Real.mul_rpow hα0.le (by positivity), ← Real.rpow_mul (norm_nonneg z)]
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

/-- For `|z| > 1` and `α ∈ [0, 1]`:
`|∂f_{1,α} (z)|, |∂_zbar f_{1,α} (z)| ≤ 32 (1 + |z|²)² e^{−(|z| − 1)²}`. -/
theorem norm_testFunOne_le_of_one_lt_norm {α : ℝ} (hα : α ∈ Icc (0 : ℝ) 1) {z : ℂ}
    (hz : 1 < ‖z‖) :
    ‖dz (testFunOne α) z‖ ≤ 32 * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) ∧
      ‖dzbar (testFunOne α) z‖ ≤ 32 * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) := by
  have ht : 1 < Complex.normSq z := by rw [Complex.normSq_eq_norm_sq]; nlinarith
  have h := norm_dz_mul_ofReal_radial_le
    ((contDiffAt_rpow_neg_mul_expCutoff α (by linarith)).differentiableAt (by norm_num))
    (derivBoundTwo_rpow_neg_mul_expCutoff hα ht.le)
  beta_reduce at h
  rw [expCutoff_normSq] at h
  rw [(testFunOne_eventuallyEq_of_one_lt_norm α hz).dz_eq,
    (testFunOne_eventuallyEq_of_one_lt_norm α hz).dzbar_eq]
  exact ⟨h.1.trans_eq (by ring), h.2.trans_eq (by ring)⟩

/-- Outside the unit disc, `∫ |∂f_{1,α}|^p` and `∫ |∂_zbar f_{1,α}|^p` are bounded uniformly in
`α ∈ [0, 1]`. -/
theorem exists_bound_testFunOne_compl_ball {p : ℝ} (hp : 0 < p) :
    ∃ C : ℝ, ∀ α ∈ Set.Icc (0 : ℝ) 1,
      ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖dz (testFunOne α) z‖ₑ ^ p ≤ ENNReal.ofReal C ∧
        ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ, ‖dzbar (testFunOne α) z‖ₑ ^ p ≤ ENNReal.ofReal C := by
  set I := ∫⁻ z in (Metric.ball (0 : ℂ) 1)ᶜ,
    ENNReal.ofReal (32 * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2))) ^ p with hI_def
  have hI : I < ⊤ := lintegral_compl_ball_majorant_lt_top hp (by norm_num)
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
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (norm_testFunOne_le_of_one_lt_norm hα hz).1) hp.le
  · refine lintegral_mono_ae (hae.mono fun z hz => ?_)
    rw [← ofReal_norm]
    exact ENNReal.rpow_le_rpow
      (ENNReal.ofReal_le_ofReal (norm_testFunOne_le_of_one_lt_norm hα hz).2) hp.le

/-! ### Approximation in `W^{1,p}` -/

/-- The approximants `φ_k (z) = z K_k (|z|²)`, with the profiles `K_k` of the approximations of
`f_{2,α}` (`HarmonicAnalysis.BeurlingAhlfors.approxProfile`). -/
def approxFunOne (α : ℝ) (k : ℕ) (z : ℂ) : ℂ :=
  z * ((approxProfile α k (Complex.normSq z) : ℝ) : ℂ)

/-- `φ_k` is smooth. -/
theorem contDiff_approxFunOne (α : ℝ) (k : ℕ) : ContDiff ℝ ∞ (approxFunOne α k) := by
  have hN : ContDiff ℝ ∞ Complex.normSq := by
    rw [show Complex.normSq = fun z : ℂ => ‖z‖ ^ 2 from funext Complex.normSq_eq_norm_sq]
    exact contDiff_norm_sq ℝ
  rw [contDiff_iff_contDiffAt]
  intro z
  have h1 : ContDiffAt ℝ ∞ (approxProfile α k) (Complex.normSq z) :=
    contDiffAt_approxProfile α k (by linarith [Complex.normSq_nonneg z, approxEps_pos k])
  have h2 : ContDiffAt ℝ ∞ (fun w => ((approxProfile α k (Complex.normSq w) : ℝ) : ℂ)) z :=
    Complex.ofRealCLM.contDiff.contDiffAt.comp z (h1.comp z hN.contDiffAt)
  exact contDiffAt_id.mul h2

/-- `φ_k (z) = 0` for `|z|² ≥ 2 R_k`. -/
theorem approxFunOne_eq_zero (α : ℝ) (k : ℕ) {z : ℂ}
    (hz : 2 * approxRadius k ≤ Complex.normSq z) : approxFunOne α k z = 0 := by
  rw [approxFunOne, approxProfile, approxTrunc_eq_zero k hz]
  simp

/-- `φ_k` has compact support. -/
theorem hasCompactSupport_approxFunOne (α : ℝ) (k : ℕ) :
    HasCompactSupport (approxFunOne α k) := by
  refine HasCompactSupport.intro (isCompact_closedBall (0 : ℂ) (2 * approxRadius k))
    fun z hz => approxFunOne_eq_zero α k ?_
  rw [Metric.mem_closedBall, dist_zero_right, not_le] at hz
  rw [Complex.normSq_eq_norm_sq]
  have := two_le_approxRadius k
  nlinarith

/-- `φ_k` as a Schwartz function. -/
def approxSchwartzOne (α : ℝ) (k : ℕ) : 𝓢(ℂ, ℂ) :=
  (hasCompactSupport_approxFunOne α k).toSchwartzMap (contDiff_approxFunOne α k)

/-- `∂φ_k` is the pointwise `∂` of `z K_k (|z|²)`. -/
theorem dzCLM_pow_one_approxSchwartzOne (α : ℝ) (k : ℕ) (z : ℂ) :
    (dzCLM ^ 1) (approxSchwartzOne α k) z =
      dz (fun w => w * ((approxProfile α k (Complex.normSq w) : ℝ) : ℂ)) z := by
  rw [pow_one, dzCLM_apply]
  rfl

/-- `∂_zbar φ_k` is the pointwise `∂_zbar` of `z K_k (|z|²)`. -/
theorem dzbarCLM_pow_one_approxSchwartzOne (α : ℝ) (k : ℕ) (z : ℂ) :
    (dzbarCLM ^ 1) (approxSchwartzOne α k) z =
      dzbar (fun w => w * ((approxProfile α k (Complex.normSq w) : ℝ) : ℂ)) z := by
  rw [pow_one, dzbarCLM_apply]
  rfl

/-- On `(0, 1)`: `|K_k + t K_k'| ≤ t^{−α}` and `t |K_k'| ≤ t^{−α}`, since `t / (t + ε_k) ≤ 1` and
`(t + ε_k)^{−α} ≤ t^{−α}`. -/
theorem abs_approxProfile_add_le_of_lt_one {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ) {t : ℝ}
    (ht0 : 0 < t) (ht1 : t < 1) :
    |approxProfile α k t + t * deriv (approxProfile α k) t| ≤ t ^ (-α) ∧
      t * |deriv (approxProfile α k) t| ≤ t ^ (-α) := by
  obtain ⟨h0, h1, -⟩ := approxProfile_jet_of_lt_one α k ht1
  rw [h0, h1]
  have hε := approxEps_pos k
  obtain ⟨s, hs_def⟩ : ∃ s, s = t + approxEps k := ⟨_, rfl⟩
  rw [← hs_def]
  have hs : 0 < s := by linarith
  have hts : t ≤ s := by linarith
  have hX0 : 0 < s ^ (-α) := Real.rpow_pos_of_pos hs _
  have hXt : s ^ (-α) ≤ t ^ (-α) := Real.rpow_le_rpow_of_nonpos ht0 hts (by linarith)
  have e1 : s ^ (-α - 1) = s ^ (-α) / s := Real.rpow_sub_one hs.ne' _
  rw [e1]
  obtain ⟨r, hr_def⟩ : ∃ r, r = t / s := ⟨_, rfl⟩
  have hr0 : 0 < r := hr_def ▸ div_pos ht0 hs
  have hr1 : r ≤ 1 := hr_def ▸ (div_le_one hs).2 hts
  have eq1 : s ^ (-α) + t * (-α * (s ^ (-α) / s)) = s ^ (-α) * (1 - α * r) := by
    rw [hr_def]; field_simp; ring
  have eq2 : t * |-α * (s ^ (-α) / s)| = s ^ (-α) * (α * r) := by
    rw [abs_mul, abs_neg, abs_of_pos hα0, abs_of_pos (div_pos hX0 hs), hr_def]
    field_simp
  rw [eq1, eq2, abs_mul, abs_of_pos hX0]
  have har : α * r ≤ 1 := by nlinarith
  have har0 : 0 ≤ α * r := by positivity
  constructor
  · rw [abs_of_nonneg (by linarith)]; nlinarith
  · nlinarith

/-- Domination on the punctured unit disc: `|∂φ_k (z)|, |∂_zbar φ_k (z)| ≤ |z|^{−2α}`. -/
theorem norm_approxSchwartzOne_le_of_lt_one {α : ℝ} (hα0 : 0 < α) (hα1 : α < 1) (k : ℕ)
    {z : ℂ} (hz0 : z ≠ 0) (hz : ‖z‖ < 1) :
    ‖(dzCLM ^ 1) (approxSchwartzOne α k) z‖ ≤ ‖z‖ ^ (-2 * α) ∧
      ‖(dzbarCLM ^ 1) (approxSchwartzOne α k) z‖ ≤ ‖z‖ ^ (-2 * α) := by
  have ht0 : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
  have ht1 : Complex.normSq z < 1 := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
  have hk := (contDiffAt_two_approxProfile α k z).differentiableAt (by norm_num)
  obtain ⟨h1, h2⟩ := abs_approxProfile_add_le_of_lt_one hα0 hα1 k ht0 ht1
  rw [dzCLM_pow_one_approxSchwartzOne, dzbarCLM_pow_one_approxSchwartzOne,
    dz_mul_ofReal_radial hk, dzbar_mul_ofReal_radial hk, Complex.norm_real, Real.norm_eq_abs,
    norm_mul, norm_pow, Complex.norm_real, Real.norm_eq_abs, ← Complex.normSq_eq_norm_sq,
    ← normSq_rpow_neg]
  exact ⟨h1, h2⟩

/-- Domination outside the unit disc, for `α ∈ [0, 1]`:
`|∂φ_k (z)|, |∂_zbar φ_k (z)| ≤ C (1 + |z|²)² e^{−(|z| − 1)²}`, uniformly in `k`. -/
theorem exists_norm_approxSchwartzOne_le_of_one_lt {α : ℝ} (hα0 : 0 ≤ α) (hα1 : α ≤ 1) :
    ∃ C, ∀ k z, 1 < ‖z‖ →
      ‖(dzCLM ^ 1) (approxSchwartzOne α k) z‖ ≤
          C * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) ∧
        ‖(dzbarCLM ^ 1) (approxSchwartzOne α k) z‖ ≤
          C * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) := by
  obtain ⟨B, hB⟩ := exists_derivBoundTwo_approxProfile hα0 hα1
  refine ⟨2 * B, fun k z hz => ?_⟩
  have ht : 1 < Complex.normSq z := by
    rw [Complex.normSq_eq_norm_sq]; nlinarith
  have h := norm_dz_mul_ofReal_radial_le
    ((contDiffAt_two_approxProfile α k z).differentiableAt (by norm_num)) (hB k _ ht)
  rw [expCutoff_normSq] at h
  rw [dzCLM_pow_one_approxSchwartzOne, dzbarCLM_pow_one_approxSchwartzOne]
  exact ⟨h.1.trans_eq (by ring), h.2.trans_eq (by ring)⟩

/-- `f_{1,α} ∈ W^{1,p}` for `1 ≤ p < ∞`, `0 < α < 1/p` (Dragičević 2011, p. 465, where `p > 2`), in
the form used: there are Schwartz functions `φ_k` with `∂_zbar φ_k → ∂_zbar f_{1,α}` and `∂φ_k →
∂f_{1,α}`
in `L^p`.

The article asserts this without proof, and the lecture notes leave it as an exercise (Exercise
2.19, whose hint is to approximate by smooth functions); the proof is the standard approximation
argument, as for `n = 2` (`HarmonicAnalysis.BeurlingAhlfors.exists_schwartz_tendsto_testFun`):
`φ_k (z) = z K_k (|z|²)` (`HarmonicAnalysis.BeurlingAhlfors.approxSchwartzOne`) regularises the
singularity at `0`, smooths the cutoff at `|z| = 1` and truncates at infinity. Off `0` and the
unit circle, `∂φ_k → ∂f` and `∂_zbar φ_k → ∂_zbar f` pointwise, with a domination uniform in `k`, by
`|z|^{−2α}` on the disc and by `C (1 + |z|²)² e^{−(|z| − 1)²}` outside it, whose `p`-th power is
integrable; dominated convergence concludes. -/
theorem exists_schwartz_tendsto_testFunOne {p α : ℝ} (hp : 1 ≤ p) (hα0 : 0 < α)
    (hα : α * p < 1) :
    ∃ φ : ℕ → 𝓢(ℂ, ℂ),
      Tendsto (fun k => eLpNorm (fun z => (dzbarCLM ^ 1) (φ k) z - dzbar (testFunOne α) z)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) ∧
      Tendsto (fun k => eLpNorm (fun z => (dzCLM ^ 1) (φ k) z - dz (testFunOne α) z)
        (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
  have hp0 : 0 < p := by linarith
  have hα1 : α < 1 := by nlinarith
  obtain ⟨C, hC⟩ := exists_norm_approxSchwartzOne_le_of_one_lt hα0.le hα1.le
  set c := max C 0 with hc_def
  have hc : 0 ≤ c := le_max_right _ _
  set D : ℂ → ℝ := fun z => if ‖z‖ < 1 then ‖z‖ ^ (-2 * α) else
    c * ((1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2)) with hD_def
  have hae : ∀ᵐ z ∂(volume : Measure ℂ), z ≠ 0 ∧ ‖z‖ ≠ 1 :=
    (Measure.ae_ne volume 0).and ae_norm_ne_one
  -- the domination, uniform in `k`
  have hdom : ∀ k z, z ≠ 0 → ‖z‖ ≠ 1 → ‖(dzbarCLM ^ 1) (approxSchwartzOne α k) z‖ ≤ D z ∧
      ‖(dzCLM ^ 1) (approxSchwartzOne α k) z‖ ≤ D z := by
    intro k z hz0 hz1
    rcases lt_or_gt_of_ne hz1 with h | h
    · rw [hD_def]
      simp only [ite_eq_left h]
      obtain ⟨h1, h2⟩ := norm_approxSchwartzOne_le_of_lt_one hα0 hα1 k hz0 h
      exact ⟨h2, h1⟩
    · rw [hD_def]
      simp only [ite_eq_right (not_lt.2 h.le)]
      obtain ⟨h1, h2⟩ := hC k z h
      have hm : 0 ≤ (1 + ‖z‖ ^ 2) ^ 2 * Real.exp (-(‖z‖ - 1) ^ 2) := by positivity
      exact ⟨h2.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hm),
        h1.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hm)⟩
  -- the pointwise limits
  have hlim : ∀ z, z ≠ 0 → ‖z‖ ≠ 1 →
      Tendsto (fun k => (dzCLM ^ 1) (approxSchwartzOne α k) z) atTop
          (𝓝 (dz (testFunOne α) z)) ∧
        Tendsto (fun k => (dzbarCLM ^ 1) (approxSchwartzOne α k) z) atTop
          (𝓝 (dzbar (testFunOne α) z)) := by
    intro z hz0 hz1
    simp only [dzCLM_pow_one_approxSchwartzOne, dzbarCLM_pow_one_approxSchwartzOne]
    have ht0 : 0 < Complex.normSq z := Complex.normSq_pos.2 hz0
    have hk : ∀ k, DifferentiableAt ℝ (approxProfile α k) (Complex.normSq z) := fun k =>
      (contDiffAt_two_approxProfile α k z).differentiableAt (by norm_num)
    rcases lt_or_gt_of_ne hz1 with h | h
    · have ht1 : Complex.normSq z < 1 := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith [norm_nonneg z]
      have := tendsto_dz_mul_ofReal_radial hk
        ((Real.contDiffAt_rpow_const_of_ne (p := -α) (n := 1) ht0.ne').differentiableAt
          one_ne_zero)
        (tendstoTwo_approxProfile_of_lt_one α ht0 ht1)
      beta_reduce at this
      rwa [(testFunOne_eventuallyEq_of_norm_lt_one α h).dz_eq,
        (testFunOne_eventuallyEq_of_norm_lt_one α h).dzbar_eq]
    · have ht1 : 1 < Complex.normSq z := by
        rw [Complex.normSq_eq_norm_sq]; nlinarith
      have := tendsto_dz_mul_ofReal_radial hk
        ((contDiffAt_rpow_neg_mul_expCutoff α ht0).differentiableAt (by norm_num))
        (tendstoTwo_approxProfile_of_one_lt α ht1)
      beta_reduce at this
      rwa [(testFunOne_eventuallyEq_of_one_lt_norm α h).dz_eq,
        (testFunOne_eventuallyEq_of_one_lt_norm α h).dzbar_eq]
  -- the integrability of the majorant
  have hfin : ∫⁻ z, ENNReal.ofReal (2 * D z) ^ p ≠ ⊤ := by
    rw [← lintegral_add_compl _ (Metric.isOpen_ball (x := (0 : ℂ)) (ε := 1)).measurableSet]
    refine ENNReal.add_ne_top.2 ⟨?_, ?_⟩
    · rw [setLIntegral_congr_fun Metric.isOpen_ball.measurableSet
        (g := fun z => ENNReal.ofReal (2 ^ p) * ENNReal.ofReal (‖z‖ ^ (-(2 * α * p))))
        (fun z hz => ?_)]
      · rw [lintegral_const_mul _ (by fun_prop), lintegral_ball_norm_rpow (by linarith)]
        exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
      · rw [mem_ball_zero_iff] at hz
        rw [hD_def]
        simp only [ite_eq_left hz]
        rw [ENNReal.ofReal_rpow_of_nonneg (by positivity) hp0.le,
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
  refine ⟨approxSchwartzOne α, ?_, ?_⟩
  · exact tendsto_eLpNorm_sub_of_dominated hp0 (fun k => (SchwartzMap.continuous _).measurable)
      (measurable_dzbar _) (fun k => hae.mono fun z hz => (hdom k z hz.1 hz.2).1) hfin
      (hae.mono fun z hz => (hlim z hz.1 hz.2).2)
  · exact tendsto_eLpNorm_sub_of_dominated hp0 (fun k => (SchwartzMap.continuous _).measurable)
      (measurable_dz _) (fun k => hae.mono fun z hz => (hdom k z hz.1 hz.2).2) hfin
      (hae.mono fun z hz => (hlim z hz.1 hz.2).1)

end BeurlingAhlfors

end HarmonicAnalysis
