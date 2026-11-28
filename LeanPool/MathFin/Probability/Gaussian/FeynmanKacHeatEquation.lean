/-
Copyright (c) 2026 Raphael Coelho. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Raphael Coelho
-/
module

-- Ported from Formal MathFin v2.0.0 for Lean Pool.

public import LeanPool.MathFin.Init
public import Mathlib.Analysis.Calculus.Deriv.Prod
public import Mathlib.Analysis.Calculus.ParametricIntegral
public import Mathlib.Analysis.SpecialFunctions.Sqrt
public import Mathlib.Probability.BrownianMotion.Basic

/-!
# Feynman–Kac for the heat equation

This file constructs the heat flow as a Gaussian convolution. It identifies
the convolution with `E[g(x + B_t)]` when the law of `B_t` is centered Gaussian
with variance `t`, and verifies the heat equation for the payoff growth bounds
in the derivative lemmas. At time zero the expectation is `g(x)` when
`B 0 = 0` almost surely. Saporito's Theorem 9.2.1 starts from a unique
bounded classical solution and gives its expectation representation.

This proof does **not** use Itô calculus. The mechanism is:

1. By `Measure.map` transfer, `u(t, x) = ∫ y, g(x + y) ∂(gaussianReal 0 t)`
   `= ∫ y, g(x + y) · gaussianPDFReal 0 t y ∂volume` for `t > 0`.
2. The Gaussian density satisfies the heat-kernel PDE:
   `∂_t pdf(t, y) = (1/2) ∂²_y pdf(t, y)` (pure calculus).
3. Differentiating under the integral sign passes the PDE through to `u`.

## Main definitions

* `heatKernel`: `K(t, y) = (2π t)^{-1/2} · exp(−y² / (2 t))`, defined for all `t : ℝ`; the
  statements about it assume `0 < t`.
* `feynmanU`: `feynmanU g t x = ∫ z, g z · K(t, z − x) dz`, the heat-kernel form of
  `E[g(x + B_t)]`.

## Main results

* `heatConvolution_eq_add_integral_deriv` — the integrated heat-equation form
  `u(t, x) = u(0, x) + ½ ∫₀ᵗ ∂²_x u(s, x) ds` for the Gaussian convolution.
* `feynmanKac_boundary` / `feynmanU_eq_expectation` — `u(t, x) = E[g(x + B_t)]`.
* `expectation_ito` / `expectation_ito_isPreBrownian` — the expectation-form Itô
  identity `E[f(B_t)] = f(0) + ½ ∫₀ᵗ E[f''(B_s)] ds`.
* `hasFDerivAt_heatKernel` — the heat kernel is jointly Fréchet-differentiable in
  `(t, y)` (with `hasDerivAt_heatKernel_t` / `_y` / `_y_y`, the kernel-side derivatives).
* `hasDerivAt_feynmanU_t` / `_x` / `_xx` + `feynmanU_heat_equation` — for sub-Gaussian `h`
  the convolution `u = feynmanU h` is differentiable in `t`, twice in `x`, and solves
  `∂_t u = ½ ∂_xx u` (every derivative falls on the kernel; `h` needs only the growth
  bound). These make the heat flow load-bearing for the Black–Scholes PDE
  (`Models/BlackScholes/PDEFromFeynmanKac.lean`, benchmark `sc-bs-pde-feynman-kac`).

## References

* [Y. F. Saporito, *Stochastic Processes*][Saporito], Theorem 9.2.1,
  representation of a bounded classical solution

## Tags

Feynman–Kac formula, heat equation, heat kernel, parabolic PDE, Black–Scholes PDE,
Gaussian convolution, MSC 60H30, MSC 35K10, JEL G13
-/

@[expose] public section

open MeasureTheory ProbabilityTheory Filter Real
open scoped NNReal ENNReal

namespace MathFin
namespace FeynmanKacHeatEquation

/-! ### Heat-kernel PDE on `gaussianPDFReal 0 t y`

We prove `∂_t pdf(0, t, y) = (1/2) ∂²_y pdf(0, t, y)` for `t > 0`. -/

/-- Our own heat-kernel form: `K(t, y) = (2π t)^{-1/2} · exp(−y² / (2 t))`.
Defined for all `t : ℝ` (when `t ≤ 0` the formula returns nonsense but the
heat-kernel statements gate on `0 < t`). -/
noncomputable def heatKernel (t y : ℝ) : ℝ :=
  (Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-(y ^ 2) / (2 * t))

/-- For `t > 0`, the Mathlib `gaussianPDFReal 0 t y` equals our heatKernel. -/
private lemma heatKernel_eq_gaussianPDFReal {t : ℝ} (ht : 0 < t) (y : ℝ) :
    heatKernel t y = gaussianPDFReal 0 t.toNNReal y := by
  rw [heatKernel, gaussianPDFReal_def]
  have htN : (t.toNNReal : ℝ) = t := Real.coe_toNNReal _ ht.le
  rw [htN]
  ring_nf

/-- First `y`-derivative of the heat kernel: `∂_y K = -(y/t) K`. -/
private lemma hasDerivAt_heatKernel_y {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun z ↦ heatKernel t z) (-(y / t) * heatKernel t y) y := by
  have h_neg_y_sq : HasDerivAt (fun z : ℝ ↦ -(z ^ 2)) (-(2 * y)) y := by
    convert (hasDerivAt_pow 2 y).neg using 1; push_cast; ring
  have h_inner : HasDerivAt (fun z : ℝ ↦ -(z ^ 2) / (2 * t)) (-(y / t)) y := by
    have := h_neg_y_sq.div_const (2 * t)
    have ht_ne : (2 * t) ≠ 0 := by positivity
    convert this using 1; field_simp
  have h_exp : HasDerivAt (fun z : ℝ ↦ Real.exp (-(z ^ 2) / (2 * t)))
      (Real.exp (-(y ^ 2) / (2 * t)) * -(y / t)) y := h_inner.exp
  have h_mul := h_exp.const_mul ((Real.sqrt (2 * Real.pi * t))⁻¹)
  -- h_mul : HasDerivAt (fun z ↦ K(t, z)) ((√(2πt))⁻¹ * (exp(-y²/(2t)) * -(y/t))) y
  have h_val :
      (Real.sqrt (2 * Real.pi * t))⁻¹ * (Real.exp (-(y ^ 2) / (2 * t)) * -(y / t))
        = -(y / t) * heatKernel t y := by
    unfold heatKernel; ring
  rw [← h_val]; exact h_mul

/-- First `t`-derivative of the heat kernel: `∂_t K = K · (y² − t) / (2 t²)`. -/
private lemma hasDerivAt_heatKernel_t {y : ℝ} {t : ℝ} (ht : 0 < t) :
    HasDerivAt (fun s ↦ heatKernel s y) (heatKernel t y * (y ^ 2 - t) / (2 * t ^ 2)) t := by
  -- Write K(s, y) = f(s) * g(s, y) where f(s) = (√(2πs))⁻¹ and g(s) = exp(-y²/(2s)).
  -- f'(s) = -(1/2) * f(s) / s
  -- g'(s) = g(s) * y² / (2 s²)
  -- K'(s) = f'g + fg' = K · [-(1/(2s)) + y²/(2s²)] = K · (y² - s) / (2 s²)
  -- f(s) = (√(2πs))⁻¹: derivative computation
  have h_2pi_pos : 0 < 2 * Real.pi := by positivity
  have h_2pis_pos : 0 < 2 * Real.pi * t := by positivity
  have h_sqrt_pos : 0 < Real.sqrt (2 * Real.pi * t) := Real.sqrt_pos.mpr h_2pis_pos
  have h_sqrt_ne : Real.sqrt (2 * Real.pi * t) ≠ 0 := h_sqrt_pos.ne'
  have h_2pis_id : HasDerivAt (fun s : ℝ ↦ 2 * Real.pi * s) (2 * Real.pi) t := by
    have := (hasDerivAt_id t).const_mul (2 * Real.pi)
    simpa using this
  have h_sqrt_inner : HasDerivAt (fun s : ℝ ↦ Real.sqrt (2 * Real.pi * s))
      (1 / (2 * Real.sqrt (2 * Real.pi * t)) * (2 * Real.pi)) t :=
    (Real.hasDerivAt_sqrt h_2pis_pos.ne').comp t h_2pis_id
  have h_f : HasDerivAt (fun s : ℝ ↦ (Real.sqrt (2 * Real.pi * s))⁻¹)
      (-(1 / (2 * Real.sqrt (2 * Real.pi * t)) * (2 * Real.pi)) /
        (Real.sqrt (2 * Real.pi * t)) ^ 2) t :=
    h_sqrt_inner.inv h_sqrt_ne
  -- g(s) = exp(-y²/(2s)): derivative computation
  have h_2s : HasDerivAt (fun s : ℝ ↦ 2 * s) 2 t := by
    simpa using (hasDerivAt_id t).const_mul 2
  have ht_ne : t ≠ 0 := ht.ne'
  have h_2t_ne : (2 * t) ≠ 0 := by positivity
  have h_inv_2s : HasDerivAt (fun s : ℝ ↦ (2 * s)⁻¹) (-2 / (2 * t) ^ 2) t :=
    h_2s.inv h_2t_ne
  have h_inner : HasDerivAt (fun s : ℝ ↦ -(y ^ 2) / (2 * s))
      (-(y ^ 2) * (-2 / (2 * t) ^ 2)) t := by
    have h_eq : (fun s : ℝ ↦ -(y ^ 2) / (2 * s)) = (fun s : ℝ ↦ -(y ^ 2) * (2 * s)⁻¹) := by
      funext s; rw [div_eq_mul_inv]
    rw [h_eq]
    exact h_inv_2s.const_mul (-(y ^ 2))
  have h_g : HasDerivAt (fun s : ℝ ↦ Real.exp (-(y ^ 2) / (2 * s)))
      (Real.exp (-(y ^ 2) / (2 * t)) * (-(y ^ 2) * (-2 / (2 * t) ^ 2))) t := h_inner.exp
  -- Combine via product rule
  have h_K := h_f.mul h_g
  -- h_K : HasDerivAt (f * g) (h_f_val * g(t) + f(t) * h_g_val) t
  -- where the value is:
  --   -(1/(2√(2πt)) * 2π) / (√(2πt))² · exp(-y²/(2t))
  --     + (√(2πt))⁻¹ · (exp(-y²/(2t)) · (-y² · (-2/(2t)²)))
  -- Using (√(2πt))² = 2πt, simplify:
  --   -π/(2πt · √(2πt)) · exp + (√(2πt))⁻¹ · exp · y²/(2t²)
  --     = (√(2πt))⁻¹ · exp · [-1/(2t) + y²/(2t²)]
  --     = (√(2πt))⁻¹ · exp · (y² - t)/(2t²)
  --     = heatKernel t y · (y² - t)/(2t²)
  have h_sqrt_sq : (Real.sqrt (2 * Real.pi * t)) ^ 2 = 2 * Real.pi * t :=
    Real.sq_sqrt h_2pis_pos.le
  have h_pi_ne : (Real.pi : ℝ) ≠ 0 := Real.pi_pos.ne'
  have h_val :
      -(1 / (2 * Real.sqrt (2 * Real.pi * t)) * (2 * Real.pi))
          / (Real.sqrt (2 * Real.pi * t)) ^ 2 * Real.exp (-(y ^ 2) / (2 * t))
        + (Real.sqrt (2 * Real.pi * t))⁻¹
            * (Real.exp (-(y ^ 2) / (2 * t)) * (-(y ^ 2) * (-2 / (2 * t) ^ 2)))
        = heatKernel t y * (y ^ 2 - t) / (2 * t ^ 2) := by
    unfold heatKernel
    rw [h_sqrt_sq]
    field_simp
    ring
  rw [← h_val]; exact h_K

/-- Second `y`-derivative of the heat kernel: `∂²_y K = K · (y² − t) / t²`.
The first-derivative function being `z ↦ -(z/t) · K(t, z)`. -/
private lemma hasDerivAt_heatKernel_y_y {t : ℝ} (ht : 0 < t) (y : ℝ) :
    HasDerivAt (fun z ↦ -(z / t) * heatKernel t z) (heatKernel t y * (y ^ 2 - t) / t ^ 2) y := by
  have ht_ne : t ≠ 0 := ht.ne'
  have h_a : HasDerivAt (fun z : ℝ ↦ -(z / t)) (-(1 / t)) y := by
    have h1 : HasDerivAt (fun z : ℝ ↦ z / t) (1 / t) y := by
      have := (hasDerivAt_id y).div_const t
      simpa using this
    exact h1.neg
  have h_b : HasDerivAt (fun z : ℝ ↦ heatKernel t z) (-(y / t) * heatKernel t y) y :=
    hasDerivAt_heatKernel_y ht y
  have h_prod := h_a.mul h_b
  have h_val :
      -(1 / t) * heatKernel t y + -(y / t) * (-(y / t) * heatKernel t y)
        = heatKernel t y * (y ^ 2 - t) / t ^ 2 := by
    field_simp; ring
  rw [← h_val]; exact h_prod

/-- **Kernel `x`-derivative of the shifted heat kernel** `x ↦ K(t, z − x)`:
`∂_x K(t, z − x) = ((z − x)/t)·K(t, z − x)`. Chain rule on `hasDerivAt_heatKernel_y`
through the inner map `x ↦ z − x`. Building block for the shifted-integral heat
equation `∂_t u = ½ ∂_xx u` (benchmark `sc-thm-9.2.1`). -/
private lemma hasDerivAt_heatKernel_x {t : ℝ} (ht : 0 < t) (z x : ℝ) :
    HasDerivAt (fun x' ↦ heatKernel t (z - x'))
      ((z - x) / t * heatKernel t (z - x)) x := by
  have h := (hasDerivAt_heatKernel_y ht (z - x)).comp x ((hasDerivAt_id x).const_sub z)
  convert h using 1 <;> first | rfl | ring

/-- **Second kernel `x`-derivative**:
`∂_xx K(t, z − x) = ∂_x [((z − x)/t)·K(t, z − x)] = K(t, z − x)·((z − x)² − t)/t²`.
Chain rule on `hasDerivAt_heatKernel_y_y` through `x ↦ z − x`, then a sign flip
(`(z − x)/t · K = −(−(z − x)/t · K)`). Building block for `sc-thm-9.2.1`. -/
private lemma hasDerivAt_heatKernel_x_x {t : ℝ} (ht : 0 < t) (z x : ℝ) :
    HasDerivAt (fun x' ↦ (z - x') / t * heatKernel t (z - x'))
      (heatKernel t (z - x) * ((z - x) ^ 2 - t) / t ^ 2) x := by
  have hfun : (fun x' ↦ (z - x') / t * heatKernel t (z - x'))
      = (fun x' ↦ -(-((z - x') / t) * heatKernel t (z - x'))) := by funext x'; ring
  rw [hfun]
  have h := ((hasDerivAt_heatKernel_y_y ht (z - x)).comp x
    ((hasDerivAt_id x).const_sub z)).neg
  convert h using 1 <;> first | rfl | ring

/-- **Joint differentiability of the heat kernel** in `(t, y)` (for `t > 0`). The Fréchet derivative
at `(t₀, y₀)` is the row functional `(a, b) ↦ ∂_t K · a + ∂_y K · b` (`∂_t K = K·(y²−t)/(2t²)`,
`∂_y K = −(y/t)·K`). Built from the elementary calculus of `(√(2πt))⁻¹·exp(−y²/(2t))`; the two
columns read off against the basis. This upgrades the two separately-proved partials to a *total*
derivative — the one genuinely-2D ingredient that lets the price, differentiated along a curve
`τ ↦ (v τ, w τ)` with both kernel arguments moving, collapse to a single chain rule. -/
lemma hasFDerivAt_heatKernel {t₀ : ℝ} (ht₀ : 0 < t₀) (y₀ : ℝ) :
    HasFDerivAt (fun p : ℝ × ℝ ↦ heatKernel p.1 p.2)
      ((heatKernel t₀ y₀ * (y₀ ^ 2 - t₀) / (2 * t₀ ^ 2)) • ContinuousLinearMap.fst ℝ ℝ ℝ
        + (-(y₀ / t₀) * heatKernel t₀ y₀) • ContinuousLinearMap.snd ℝ ℝ ℝ) (t₀, y₀) := by
  have h2pit : (0:ℝ) < 2 * Real.pi * t₀ := by positivity
  have hsqrt_ne : Real.sqrt (2 * Real.pi * t₀) ≠ 0 := (Real.sqrt_pos.mpr h2pit).ne'
  have h2t0_ne : (2 * t₀) ≠ 0 := by positivity
  have hlin1 : HasFDerivAt (fun p : ℝ × ℝ ↦ 2 * Real.pi * p.1)
      ((2 * Real.pi) • ContinuousLinearMap.fst ℝ ℝ ℝ) (t₀, y₀) := by
    exact ((2 * Real.pi) • ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := (t₀, y₀))
  have hlin2 : HasFDerivAt (fun p : ℝ × ℝ ↦ 2 * p.1)
      ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ) (t₀, y₀) := by
    exact ((2 : ℝ) • ContinuousLinearMap.fst ℝ ℝ ℝ).hasFDerivAt (x := (t₀, y₀))
  have hsnd : HasFDerivAt (fun p : ℝ × ℝ ↦ p.2) (ContinuousLinearMap.snd ℝ ℝ ℝ) (t₀, y₀) := by
    exact (ContinuousLinearMap.snd ℝ ℝ ℝ).hasFDerivAt (x := (t₀, y₀))
  have hA := (hasDerivAt_inv hsqrt_ne).comp_hasFDerivAt (t₀, y₀)
      ((Real.hasDerivAt_sqrt h2pit.ne').comp_hasFDerivAt (t₀, y₀) hlin1)
  have hnum := (hsnd.pow 2).neg
  have hden := (hasDerivAt_inv h2t0_ne).comp_hasFDerivAt (t₀, y₀) hlin2
  have hB := (hnum.mul hden).exp
  convert hA.mul hB using 1 <;> try rfl
  refine ContinuousLinearMap.ext fun v ↦ ?_
  simp only [add_apply, smul_apply,
    neg_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', smul_eq_mul,
    Pi.mul_apply, Pi.neg_apply, Function.comp_apply, heatKernel]
  rw [show -(y₀ ^ 2) / (2 * t₀) = -(y₀ ^ 2) * (2 * t₀)⁻¹ from div_eq_mul_inv _ _,
      show Real.sqrt (2 * Real.pi * t₀) ^ 2 = 2 * Real.pi * t₀ from Real.sq_sqrt h2pit.le]
  field_simp
  ring

/-- **Derivative of the heat kernel along a curve** `s ↦ K(v s, z − w s)`. With both the variance
`v s` and the centre `w s` moving, the chain rule on `hasFDerivAt_heatKernel` collapses to
`v′·∂_t K + w′·∂_x K`. The kernel-level engine for the Black–Scholes `τ`-derivative, where
`v τ = σ²τ` and `w τ = log S + (r − σ²/2)τ` move together. -/
lemma hasDerivAt_heatKernel_comp {v w : ℝ → ℝ} {τ₀ vd wd : ℝ}
    (hv : HasDerivAt v vd τ₀) (hw : HasDerivAt w wd τ₀) (hvpos : 0 < v τ₀) (z : ℝ) :
    HasDerivAt (fun s ↦ heatKernel (v s) (z - w s))
      (vd * (heatKernel (v τ₀) (z - w τ₀) * ((z - w τ₀) ^ 2 - v τ₀) / (2 * (v τ₀) ^ 2))
        + wd * ((z - w τ₀) / (v τ₀) * heatKernel (v τ₀) (z - w τ₀))) τ₀ := by
  have hcurve : HasDerivAt (fun s ↦ (v s, z - w s)) (vd, -wd) τ₀ :=
    hv.prodMk (hw.const_sub z)
  have hcomp := (hasFDerivAt_heatKernel hvpos (z - w τ₀)).comp_hasDerivAt τ₀ hcurve
  convert hcomp using 1 <;> try rfl
  simp only [add_apply, smul_apply,
    ContinuousLinearMap.coe_fst', ContinuousLinearMap.coe_snd', smul_eq_mul]
  ring

/-- **Heat-kernel PDE on `heatKernel`**: `∂_t K = (1/2) ∂²_y K`. As an algebraic
identity on the derivative values from `hasDerivAt_heatKernel_t` and
`hasDerivAt_heatKernel_y_y`.

The load-bearing kernel-side input to the **heat equation for `u`** `∂_t u = ½ ∂_xx u`:
used by `feynmanU_heat_equation` and the Black–Scholes PDE proof in
`Models/BlackScholes/PDEFromFeynmanKac.lean`. -/
private lemma heatKernel_t_eq_half_y_y {t : ℝ} (ht : 0 < t) (y : ℝ) :
    heatKernel t y * (y ^ 2 - t) / (2 * t ^ 2)
      = (1 / 2) * (heatKernel t y * (y ^ 2 - t) / t ^ 2) := by
  have ht_ne : t ≠ 0 := ht.ne'
  field_simp

/-! ### Auxiliary integrability + nonnegativity for the heat kernel -/

/-- The heat kernel is nonnegative. -/
lemma heatKernel_nonneg {t : ℝ} (ht : 0 < t) (y : ℝ) : 0 ≤ heatKernel t y := by
  rw [heatKernel_eq_gaussianPDFReal ht]
  exact gaussianPDFReal_nonneg 0 _ y

/-- For `t > 0`, the heat kernel is integrable in `y` over Lebesgue. -/
lemma integrable_heatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun y ↦ heatKernel t y) volume := by
  have := integrable_gaussianPDFReal (0 : ℝ) t.toNNReal
  refine this.congr (Filter.Eventually.of_forall fun y ↦ ?_)
  exact (heatKernel_eq_gaussianPDFReal ht y).symm

/-- **Transfer integrability from the Gaussian law to the heat kernel.** If `g ∈ L¹(N(0,t))`,
then `g · K(t,·)` is Lebesgue-integrable — because `N(0,t) = volume.withDensity K(t,·)`. This
turns Gaussian moments (`memLp_id_gaussianReal`) into integrability of polynomial × heat kernel,
needed for the integration-by-parts in the expectation-form Itô formula. -/
private lemma integrable_mul_heatKernel_of_gaussian {t : ℝ} (ht : 0 < t) {g : ℝ → ℝ}
    (hg : Integrable g (gaussianReal 0 t.toNNReal)) :
    Integrable (fun y ↦ g y * heatKernel t y) volume := by
  have hv : (t.toNNReal : ℝ≥0) ≠ 0 := (Real.toNNReal_pos.mpr ht).ne'
  rw [gaussianReal_of_var_ne_zero 0 hv,
    integrable_withDensity_iff_integrable_smul' (by fun_prop)
      (ae_of_all _ fun y ↦ gaussianPDF_lt_top)] at hg
  refine hg.congr (Filter.Eventually.of_forall fun y ↦ ?_)
  change (gaussianPDF 0 t.toNNReal y).toReal • g y = g y * heatKernel t y
  have hpdf : (gaussianPDF 0 t.toNNReal y).toReal = heatKernel t y := by
    rw [heatKernel_eq_gaussianPDFReal ht]
    simp only [gaussianPDF]
    rw [ENNReal.toReal_ofReal (gaussianPDFReal_nonneg _ _ _)]
  rw [smul_eq_mul, hpdf]; ring

/-- First moment: `y · K(t, ·)` is integrable. -/
lemma integrable_id_mul_heatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun y ↦ y * heatKernel t y) volume :=
  integrable_mul_heatKernel_of_gaussian ht
    ((memLp_id_gaussianReal (μ := 0) (v := t.toNNReal) 1).integrable (by norm_num))

/-- Second moment: `y² · K(t, ·)` is integrable. -/
lemma integrable_sq_mul_heatKernel {t : ℝ} (ht : 0 < t) :
    Integrable (fun y ↦ y ^ 2 * heatKernel t y) volume :=
  integrable_mul_heatKernel_of_gaussian ht
    (memLp_id_gaussianReal (μ := 0) (v := t.toNNReal) 2).integrable_sq

/-- `∂_y K = -(y/t)·K` is integrable. -/
private lemma integrable_dK {t : ℝ} (ht : 0 < t) :
    Integrable (fun y ↦ -(y / t) * heatKernel t y) volume := by
  refine ((integrable_id_mul_heatKernel ht).const_mul (-(1 / t))).congr
    (Filter.Eventually.of_forall fun y ↦ ?_)
  change -(1 / t) * (y * heatKernel t y) = -(y / t) * heatKernel t y
  ring

/-- `∂²_y K = K·(y²−t)/t²` is integrable. -/
private lemma integrable_ddK {t : ℝ} (ht : 0 < t) :
    Integrable (fun y ↦ heatKernel t y * (y ^ 2 - t) / t ^ 2) volume := by
  have ht_ne : t ≠ 0 := ht.ne'
  refine (((integrable_sq_mul_heatKernel ht).const_mul (1 / t ^ 2)).sub
    ((integrable_heatKernel ht).const_mul (1 / t))).congr (Filter.Eventually.of_forall fun y ↦ ?_)
  change 1 / t ^ 2 * (y ^ 2 * heatKernel t y) - 1 / t * heatKernel t y
      = heatKernel t y * (y ^ 2 - t) / t ^ 2
  field_simp

/-- **Integration by parts against the heat kernel** (the analytic heart of expectation-Itô).
For `f ∈ C²_b`, two improper integrations by parts over `ℝ` move both derivatives off the kernel
onto `f`: `∫ f(y)·∂²_y K(t,y) dy = ∫ f′′(y)·K(t,y) dy`. The boundary terms vanish (`f, f′` bounded,
`K, ∂_y K` Gaussian-decaying), which is encoded by `integral_mul_deriv_eq_deriv_mul_of_integrable`
(the integrable-product form needs no explicit boundary hypothesis). -/
private lemma ibp_heatKernel {t : ℝ} (ht : 0 < t) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''c : Continuous f'') {Cf Cf' Cf'' : ℝ}
    (hCf : ∀ x, |f x| ≤ Cf) (hCf' : ∀ x, |f' x| ≤ Cf') (hCf'' : ∀ x, |f'' x| ≤ Cf'') :
    ∫ y, f y * (heatKernel t y * (y ^ 2 - t) / t ^ 2) ∂volume
      = ∫ y, f'' y * heatKernel t y ∂volume := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x ↦ (hf x).continuousAt
  have hf'c : Continuous f' := continuous_iff_continuousAt.mpr fun x ↦ (hf' x).continuousAt
  have hi_f_ddK : Integrable (fun y ↦ f y * (heatKernel t y * (y ^ 2 - t) / t ^ 2)) volume :=
    (integrable_ddK ht).bdd_mul hfc.aestronglyMeasurable
      (ae_of_all _ fun y ↦ by rw [Real.norm_eq_abs]; exact hCf y)
  have hi_f'_dK : Integrable (fun y ↦ f' y * (-(y / t) * heatKernel t y)) volume :=
    (integrable_dK ht).bdd_mul hf'c.aestronglyMeasurable
      (ae_of_all _ fun y ↦ by rw [Real.norm_eq_abs]; exact hCf' y)
  have hi_f_dK : Integrable (fun y ↦ f y * (-(y / t) * heatKernel t y)) volume :=
    (integrable_dK ht).bdd_mul hfc.aestronglyMeasurable
      (ae_of_all _ fun y ↦ by rw [Real.norm_eq_abs]; exact hCf y)
  have hi_f''_K : Integrable (fun y ↦ f'' y * heatKernel t y) volume :=
    (integrable_heatKernel ht).bdd_mul hf''c.aestronglyMeasurable
      (ae_of_all _ fun y ↦ by rw [Real.norm_eq_abs]; exact hCf'' y)
  have hi_f'_K : Integrable (fun y ↦ f' y * heatKernel t y) volume :=
    (integrable_heatKernel ht).bdd_mul hf'c.aestronglyMeasurable
      (ae_of_all _ fun y ↦ by rw [Real.norm_eq_abs]; exact hCf' y)
  have ibp1 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f) (v := fun z ↦ -(z / t) * heatKernel t z)
    (v' := fun z ↦ heatKernel t z * (z ^ 2 - t) / t ^ 2)
    (fun x _ ↦ hf x) (fun x _ ↦ hasDerivAt_heatKernel_y_y ht x) hi_f_ddK hi_f'_dK hi_f_dK
  have ibp2 := integral_mul_deriv_eq_deriv_mul_of_integrable
    (u := f') (v := fun z ↦ heatKernel t z)
    (v' := fun z ↦ -(z / t) * heatKernel t z)
    (fun x _ ↦ hf' x) (fun x _ ↦ hasDerivAt_heatKernel_y ht x) hi_f'_dK hi_f''_K hi_f'_K
  rw [ibp1, ibp2, neg_neg]

/-- The heat kernel is continuous in the space variable (for any fixed time). -/
lemma continuous_heatKernel (s : ℝ) : Continuous (fun y ↦ heatKernel s y) := by
  unfold heatKernel; fun_prop

/-- The polynomial-times-heat-kernel function `(y² + c)·K(s, y)` is integrable (`s > 0`). This
is the integrable majorant used to dominate `∂_t K(·, y)` over a time-neighbourhood of `t`
(instantiated at `s = 3t/2`); built directly from the moment integrabilities
`integrable_sq_mul_heatKernel` / `integrable_heatKernel`, avoiding raw-`rpow` Gaussians. -/
private lemma integrable_poly_heatKernel {s : ℝ} (hs : 0 < s) (c : ℝ) :
    Integrable (fun y ↦ (y ^ 2 + c) * heatKernel s y) volume := by
  refine ((integrable_sq_mul_heatKernel hs).add
    ((integrable_heatKernel hs).const_mul c)).congr (Filter.Eventually.of_forall fun y ↦ ?_)
  simp only [Pi.add_apply]; ring

/-- **Completing-the-square mean shift at the kernel level.** Multiplying the heat kernel by the
exponential `eᶻ` is the same as translating its centre by the variance:
`eᶻ·K(σ, z−c) = e^{c+σ/2}·K(σ, z−(c+σ))`. The proof is the elementary completing-the-square identity
`z − (z−c)²/(2σ) = (c+σ/2) − (z−(c+σ))²/(2σ)` — the analytic core underlying the Cameron–Martin /
Girsanov density shift, here used purely as a real-analysis fact (no measure change). It converts a
sub-Gaussian envelope `eᶻ·poly·K` into `poly·(shifted K)`, whose integrability is then just Gaussian
moments — the load-bearing input to `integrable_exp_mul_poly_heatKernel`. -/
private lemma exp_mul_heatKernel {σ : ℝ} (hσ : 0 < σ) (c z : ℝ) :
    Real.exp z * heatKernel σ (z - c)
      = Real.exp (c + σ / 2) * heatKernel σ (z - (c + σ)) := by
  have hσ' : σ ≠ 0 := hσ.ne'
  simp only [heatKernel]
  rw [mul_left_comm, mul_left_comm (Real.exp (c + σ / 2))]
  congr 1
  rw [← Real.exp_add, ← Real.exp_add]
  congr 1
  field_simp
  ring

/-- **The sub-Gaussian envelope is integrable.** For `σ > 0`, the function
`z ↦ eᶻ·((z−c)² + d)·K(σ, z−c)` is Lebesgue-integrable. By the mean shift `exp_mul_heatKernel`
it equals `e^{c+σ/2}·((z−c)² + d)·K(σ, z−(c+σ))`; expanding `(z−c)² = (z−(c+σ))² + 2σ(z−(c+σ)) + σ²`
turns it into a finite combination of heat-kernel moments (`integrable_sq_mul_heatKernel`,
`integrable_id_mul_heatKernel`, `integrable_heatKernel`) translated by `c+σ`
(`Integrable.comp_sub_right`). This is the dominating function that lets the call payoff
`(eᶻ − K)⁺ ≤ eᶻ` pass under the integral sign — the one genuinely new analytic ingredient for the
kernel-side heat equation. -/
lemma integrable_exp_mul_poly_heatKernel {σ : ℝ} (hσ : 0 < σ) (c d : ℝ) :
    Integrable (fun z ↦ Real.exp z * (((z - c) ^ 2 + d) * heatKernel σ (z - c))) volume := by
  have hbase : Integrable (fun w : ℝ ↦
      w ^ 2 * heatKernel σ w + 2 * σ * (w * heatKernel σ w) + (σ ^ 2 + d) * heatKernel σ w)
      volume := by
    have h1 := integrable_sq_mul_heatKernel hσ
    have h2 := (integrable_id_mul_heatKernel hσ).const_mul (2 * σ)
    have h3 := (integrable_heatKernel hσ).const_mul (σ ^ 2 + d)
    exact (h1.add h2).add h3
  have htrans := (hbase.comp_sub_right (c + σ)).const_mul (Real.exp (c + σ / 2))
  refine htrans.congr (Filter.Eventually.of_forall fun z ↦ ?_)
  dsimp only
  rw [show Real.exp z * (((z - c) ^ 2 + d) * heatKernel σ (z - c))
        = ((z - c) ^ 2 + d) * (Real.exp z * heatKernel σ (z - c)) from by ring,
      exp_mul_heatKernel hσ c z]
  ring

/-- **Integrability of a sub-Gaussian payoff against the shifted heat kernel.** For `t > 0`,
`h` continuous with `|h z| ≤ eᶻ`, the integrand `z ↦ h z · K(t, z−x)` is Lebesgue-integrable —
dominated by the envelope `eᶻ·((z−x)²+1)·K(t, z−x)` of `integrable_exp_mul_poly_heatKernel`. The
"value at the base point" integrability shared by the time- and first-space-derivative lemmas
`hasDerivAt_feynmanU_t` / `hasDerivAt_feynmanU_x` below. -/
lemma integrable_payoff_mul_heatKernel {t : ℝ} (ht : 0 < t) {h : ℝ → ℝ} (hhc : Continuous h)
    (hh : ∀ z, |h z| ≤ Real.exp z) (x : ℝ) :
    Integrable (fun z ↦ h z * heatKernel t (z - x)) volume := by
  refine (integrable_exp_mul_poly_heatKernel ht x 1).mono'
    (hhc.mul ((continuous_heatKernel t).comp
      (continuous_id.sub continuous_const))).aestronglyMeasurable (ae_of_all _ fun z ↦ ?_)
  change ‖h z * heatKernel t (z - x)‖ ≤ Real.exp z * (((z - x) ^ 2 + 1) * heatKernel t (z - x))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatKernel_nonneg ht (z - x))]
  have hKnn := heatKernel_nonneg ht (z - x)
  calc |h z| * heatKernel t (z - x)
      ≤ Real.exp z * heatKernel t (z - x) := mul_le_mul_of_nonneg_right (hh z) hKnn
    _ ≤ Real.exp z * (((z - x) ^ 2 + 1) * heatKernel t (z - x)) := by
        apply mul_le_mul_of_nonneg_left _ (Real.exp_nonneg z)
        simpa only [one_mul] using mul_le_mul_of_nonneg_right
          (show 1 ≤ (z - x) ^ 2 + 1 from le_add_of_nonneg_left (sq_nonneg (z - x))) hKnn

/-- **Spatial monotonicity of the heat kernel.** For `t > 0` and `|x − x₀| < δ`, the kernel centred
near `x` is dominated by a *wider* kernel centred at the fixed `x₀`:
`K(t, z − x) ≤ √2 · e^{δ²/(2t)} · K(2t, z − x₀)`. From the elementary `(a + b)² ≥ ½a² − b²` (here
`(z−x)² ≥ ½(z−x₀)² − (x−x₀)² ≥ ½(z−x₀)² − δ²`), so
`exp(−(z−x)²/(2t)) ≤ e^{δ²/(2t)}·exp(−(z−x₀)²/(4t))`, and
`exp(−(z−x₀)²/(4t)) = √2·√(2πt)·K(2t,z−x₀)`. This is the spatial analogue of the temporal bound
`K(s,·) ≤ √3·K(3t/2,·)` (`heatKernel_temporal_le`); it makes the `x`-derivatives' dominating
function independent of `x` over `Metric.ball x₀ δ`. -/
lemma heatKernel_shift_le {t : ℝ} (ht : 0 < t) {x x₀ δ : ℝ}
    (hx : |x - x₀| < δ) (z : ℝ) :
    heatKernel t (z - x)
      ≤ Real.sqrt 2 * Real.exp (δ ^ 2 / (2 * t)) * heatKernel (2 * t) (z - x₀) := by
  have h2t : (0 : ℝ) < 2 * t := by positivity
  have h4t : (0 : ℝ) < 4 * t := by positivity
  have hδsq : (x - x₀) ^ 2 < δ ^ 2 := sq_lt_sq' (abs_lt.mp hx).1 (abs_lt.mp hx).2
  have hnum : 2 * (z - x) ^ 2 - (z - x₀) ^ 2 + 2 * δ ^ 2 ≥ 0 := by
    linarith only [sq_nonneg (z - x₀ - 2 * (x - x₀)), hδsq]
  have hexp : -(z - x) ^ 2 / (2 * t) ≤ δ ^ 2 / (2 * t) + -(z - x₀) ^ 2 / (4 * t) := by
    rw [div_add_div _ _ (ne_of_gt h2t) (ne_of_gt h4t), div_le_div_iff₀ h2t (by positivity)]
    linarith only [mul_nonneg hnum (sq_nonneg t)]
  have hexp_le : Real.exp (-(z - x) ^ 2 / (2 * t))
      ≤ Real.exp (δ ^ 2 / (2 * t)) * Real.exp (-(z - x₀) ^ 2 / (4 * t)) := by
    rw [← Real.exp_add]; exact Real.exp_le_exp.mpr hexp
  have hconst : (Real.sqrt (2 * Real.pi * t))⁻¹
      = Real.sqrt 2 * (Real.sqrt (2 * Real.pi * (2 * t)))⁻¹ := by
    rw [show 2 * Real.pi * (2 * t) = 2 * (2 * Real.pi * t) from by ring,
        Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 2), mul_inv, ← mul_assoc,
        mul_inv_cancel₀ (Real.sqrt_pos.mpr (by norm_num : (0:ℝ) < 2)).ne', one_mul]
  have hKeq : (Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-(z - x₀) ^ 2 / (4 * t))
      = Real.sqrt 2 * heatKernel (2 * t) (z - x₀) := by
    rw [heatKernel, show -(z - x₀) ^ 2 / (2 * (2 * t)) = -(z - x₀) ^ 2 / (4 * t) from by
          rw [show 2 * (2 * t) = 4 * t from by ring], hconst]
    ring
  calc heatKernel t (z - x)
      = (Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-(z - x) ^ 2 / (2 * t)) := by rw [heatKernel]
    _ ≤ (Real.sqrt (2 * Real.pi * t))⁻¹
          * (Real.exp (δ ^ 2 / (2 * t)) * Real.exp (-(z - x₀) ^ 2 / (4 * t))) :=
        mul_le_mul_of_nonneg_left hexp_le (by positivity)
    _ = Real.exp (δ ^ 2 / (2 * t))
          * ((Real.sqrt (2 * Real.pi * t))⁻¹ * Real.exp (-(z - x₀) ^ 2 / (4 * t))) := by ring
    _ = Real.exp (δ ^ 2 / (2 * t)) * (Real.sqrt 2 * heatKernel (2 * t) (z - x₀)) := by rw [hKeq]
    _ = Real.sqrt 2 * Real.exp (δ ^ 2 / (2 * t)) * heatKernel (2 * t) (z - x₀) := by ring

/-- **Temporal monotonicity of the heat kernel.** On the time-window `(t/2, 3t/2)`,
`K(s, y) ≤ √3 · K(3t/2, y)`: a smaller variance is dominated by the fixed wider one. The temporal
analogue of `heatKernel_shift_le`, and the domination engine for the time-derivative lemmas
`hasDerivAt_phi` / `hasDerivAt_feynmanU_t`. -/
lemma heatKernel_temporal_le {t s : ℝ} (ht : 0 < t) (hs_lo : t / 2 < s) (hs_hi : s < 3 * t / 2)
    (y : ℝ) : heatKernel s y ≤ Real.sqrt 3 * heatKernel (3 * t / 2) y := by
  have hs_pos : 0 < s := by linarith
  have hKstep : heatKernel s y ≤ (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-(y ^ 2) / (3 * t)) := by
    rw [heatKernel]
    have hf1 : (Real.sqrt (2 * Real.pi * s))⁻¹ ≤ (Real.sqrt (Real.pi * t))⁻¹ := by
      apply inv_anti₀ (by positivity) (Real.sqrt_le_sqrt ?_)
      linarith only [mul_le_mul_of_nonneg_left (show t ≤ 2 * s by linarith only [hs_lo])
        Real.pi_pos.le]
    have hf2 : Real.exp (-(y ^ 2) / (2 * s)) ≤ Real.exp (-(y ^ 2) / (3 * t)) := by
      apply Real.exp_le_exp.mpr
      rw [neg_div, neg_div, neg_le_neg_iff, div_le_div_iff₀ (by positivity) (by positivity)]
      exact mul_le_mul_of_nonneg_left (by linarith only [hs_hi]) (sq_nonneg y)
    exact mul_le_mul hf1 hf2 (by positivity) (by positivity)
  have hKeq : (Real.sqrt (Real.pi * t))⁻¹ * Real.exp (-(y ^ 2) / (3 * t))
      = Real.sqrt 3 * heatKernel (3 * t / 2) y := by
    have hsqrt : Real.sqrt (2 * Real.pi * (3 * t / 2)) = Real.sqrt 3 * Real.sqrt (Real.pi * t) := by
      rw [show 2 * Real.pi * (3 * t / 2) = 3 * (Real.pi * t) from by ring,
          Real.sqrt_mul (by norm_num : (0:ℝ) ≤ 3)]
    simp only [heatKernel]
    rw [show -(y ^ 2) / (2 * (3 * t / 2)) = -(y ^ 2) / (3 * t) from by
          rw [show 2 * (3 * t / 2) = 3 * t from by ring],
        hsqrt, mul_inv]
    field_simp
  exact hKeq ▸ hKstep

/-- **Quadratic-over-variance ratio bound** on the time window `(t/2, 3t/2)`:
`|w² − s| / (2 s²) ≤ 2 (w² + 3t/2) / t²`. The polynomial factor of the time-derivative domination,
shared verbatim (modulo the centring `w = y` vs `w = z−x`) by `hasDerivAt_phi` and
`hasDerivAt_feynmanU_t`. -/
lemma sq_sub_div_le {t s : ℝ} (ht : 0 < t) (hs_lo : t / 2 < s) (hs_hi : s < 3 * t / 2)
    (w : ℝ) : |w ^ 2 - s| / (2 * s ^ 2) ≤ 2 * (w ^ 2 + 3 * t / 2) / t ^ 2 := by
  have hs_pos : 0 < s := by linarith
  have habs : |w ^ 2 - s| ≤ w ^ 2 + 3 * t / 2 := by
    rw [abs_le]; constructor <;> nlinarith [sq_nonneg w]
  have ht4s : t ^ 2 ≤ 4 * s ^ 2 := by
    have h := (sq_le_sq₀ ht.le (show 0 ≤ 2 * s by positivity)).2
      (show t ≤ 2 * s by linarith only [hs_lo])
    linarith only [h]
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  linarith only [mul_le_mul_of_nonneg_right habs (sq_nonneg t),
    mul_le_mul_of_nonneg_left ht4s (show (0:ℝ) ≤ w ^ 2 + 3 * t / 2 by positivity)]

/-- **Local domination of the heat kernel under a joint variance + centre perturbation.** When the
variance `v` stays in `(v₀/2, 3v₀/2)` and the centre `x` within `δ` of `x₀`,
`K(v, z−x) ≤ √3·√2·e^{δ²/(3v₀)}·K(3v₀, z−x₀)`. The composition of `heatKernel_temporal_le`
(variance) with `heatKernel_shift_le` (centre); the domination engine for differentiating the price
along the curve `τ ↦ (σ²τ, log S + (r−σ²/2)τ)`, where both kernel arguments move with `τ`. -/
lemma heatKernel_loc_le {v₀ v x x₀ δ : ℝ} (hv₀ : 0 < v₀)
    (hv_lo : v₀ / 2 < v) (hv_hi : v < 3 * v₀ / 2) (hx : |x - x₀| < δ) (z : ℝ) :
    heatKernel v (z - x)
      ≤ Real.sqrt 3 * (Real.sqrt 2 * Real.exp (δ ^ 2 / (3 * v₀))) *
          heatKernel (3 * v₀) (z - x₀) := by
  have h32 : (0 : ℝ) < 3 * v₀ / 2 := by positivity
  calc heatKernel v (z - x)
      ≤ Real.sqrt 3 * heatKernel (3 * v₀ / 2) (z - x) :=
        heatKernel_temporal_le hv₀ hv_lo hv_hi (z - x)
    _ ≤ Real.sqrt 3 * (Real.sqrt 2 * Real.exp (δ ^ 2 / (2 * (3 * v₀ / 2)))
          * heatKernel (2 * (3 * v₀ / 2)) (z - x₀)) :=
        mul_le_mul_of_nonneg_left (heatKernel_shift_le h32 hx z) (Real.sqrt_nonneg 3)
    _ = Real.sqrt 3 * (Real.sqrt 2 * Real.exp (δ ^ 2 / (3 * v₀))) *
        heatKernel (3 * v₀) (z - x₀) := by
        rw [show 2 * (3 * v₀ / 2) = 3 * v₀ from by ring]; ring

/-- **Curve quadratic-ratio bound** (the `∂_t`-kernel polynomial factor of the curve domination). On
`v ∈ (v₀/2, 3v₀/2)` with the centre shifted by `≤ d` (`|W − W₀| ≤ d`), the moving denominator is
absorbed into the fixed `v₀`: `|W²−v|/(2v²) ≤ 2(2W₀²+2d²+3v₀/2)/v₀²`. Isolated as its own lemma so
the `nlinarith` elaborates without the heartbeat blow-up that defeats it inline. -/
lemma curve_sq_ratio_le {v₀ v W W₀ d : ℝ} (hv₀ : 0 < v₀) (hvlo : v₀ / 2 < v)
    (hvhi : v < 3 * v₀ / 2) (hW : |W - W₀| ≤ d) (hd : 0 ≤ d) :
    |W ^ 2 - v| / (2 * v ^ 2) ≤ 2 * (2 * W₀ ^ 2 + 2 * d ^ 2 + 3 * v₀ / 2) / v₀ ^ 2 := by
  have hvpos : 0 < v := by linarith
  have hWsq : W ^ 2 ≤ 2 * W₀ ^ 2 + 2 * d ^ 2 := by
    have hd2 : (W - W₀) ^ 2 ≤ d ^ 2 := by
      nlinarith [sq_abs (W - W₀), mul_le_mul hW hW (abs_nonneg (W - W₀)) hd]
    nlinarith [hd2, sq_nonneg (W - 2 * W₀)]
  have habs : |W ^ 2 - v| ≤ W ^ 2 + v := by rw [abs_le]; constructor <;> nlinarith [sq_nonneg W]
  have hfac : (0:ℝ) ≤ 4 * v ^ 2 - v₀ ^ 2 := by nlinarith [hvlo, hvpos, hv₀]
  have hpoly_nn : (0:ℝ) ≤ 2 * W₀ ^ 2 + 2 * d ^ 2 + 3 * v₀ / 2 := by positivity
  rw [div_le_div_iff₀ (by positivity) (by positivity)]
  nlinarith [habs, hWsq, hvhi, hvpos, mul_nonneg hpoly_nn hfac, sq_nonneg W₀]

/-- **Curve linear-ratio bound** (the `∂_x`-kernel polynomial factor). Companion to
`curve_sq_ratio_le`: `|W|/v ≤ 2(W₀²+1+d)/v₀` on `v > v₀/2` with `|W − W₀| ≤ d`. -/
lemma curve_abs_ratio_le {v₀ v W W₀ d : ℝ} (hv₀ : 0 < v₀) (hvlo : v₀ / 2 < v)
    (hW : |W - W₀| ≤ d) (hd : 0 ≤ d) :
    |W| / v ≤ 2 * (W₀ ^ 2 + 1 + d) / v₀ := by
  have hvpos : 0 < v := by linarith
  have hWabs : |W| ≤ W₀ ^ 2 + 1 + d := by
    have h1 : |W| ≤ |W₀| + d := by
      have htri : |W| ≤ |W₀| + |W - W₀| := by
        calc |W| = |W₀ + (W - W₀)| := by ring_nf
          _ ≤ |W₀| + |W - W₀| := abs_add_le _ _
      linarith [htri, hW]
    have h2 : |W₀| ≤ W₀ ^ 2 + 1 := by nlinarith [sq_nonneg (|W₀| - 1), sq_abs W₀, abs_nonneg W₀]
    linarith
  rw [div_le_div_iff₀ hvpos (by positivity)]
  nlinarith [hWabs, hvlo, hvpos, hv₀, abs_nonneg W,
    mul_nonneg (show (0:ℝ) ≤ W₀ ^ 2 + 1 + d by positivity) (show (0:ℝ) ≤ 2 * v - v₀ by linarith)]

/-- **Parametric differentiation under the integral, for an `h`-weighted kernel family.** The single
skeleton behind every derivative of a heat-flow integral `p ↦ ∫ z, h z · φ(p, z) dz`: given the
family's pointwise derivative `φ′(p, ·)` on a ball around `p₀`, an integrable base point, and an
integrable uniform dominating function for `h·φ′`, the integral is differentiable with
`d/dp = ∫ h·φ′(p₀, ·)`. Specialising `φ` to `K(s, z−x)` (time) or `K(t, z−x')` (space, once and
twice) recovers `hasDerivAt_phi` and `hasDerivAt_feynmanU_{t,x,xx}`, each supplying only its
genuinely-distinct domination. The `h z`-factor is pulled through `HasDerivAt.const_mul`, so callers
hand over the bare kernel-family derivative. -/
theorem hasDerivAt_integral_mul_kernelFamily {h : ℝ → ℝ} (hhc : Continuous h)
    {φ φ' : ℝ → ℝ → ℝ} {p₀ r : ℝ} (hr : 0 < r)
    (hφc : ∀ p, Continuous (fun z ↦ φ p z)) (hφ'c : Continuous (fun z ↦ φ' p₀ z))
    (hpt : Integrable (fun z ↦ h z * φ p₀ z) volume)
    {bound : ℝ → ℝ} (hbi : Integrable bound volume)
    (hb : ∀ᵐ z ∂volume, ∀ p ∈ Metric.ball p₀ r, ‖h z * φ' p z‖ ≤ bound z)
    (hderiv : ∀ z, ∀ p ∈ Metric.ball p₀ r, HasDerivAt (fun p ↦ φ p z) (φ' p z) p) :
    HasDerivAt (fun p ↦ ∫ z, h z * φ p z ∂volume) (∫ z, h z * φ' p₀ z ∂volume) p₀ :=
  (hasDerivAt_integral_of_dominated_loc_of_deriv_le (F := fun p z ↦ h z * φ p z)
    (F' := fun p z ↦ h z * φ' p z) (Metric.ball_mem_nhds p₀ hr)
    (Filter.Eventually.of_forall fun p ↦ (hhc.mul (hφc p)).aestronglyMeasurable)
    hpt (hhc.mul hφ'c).aestronglyMeasurable hb hbi
    (ae_of_all _ fun z p hp ↦ (hderiv z p hp).const_mul (h z))).2

/-- **Differentiation under the integral for the Gaussian convolution.** For `t > 0` and `f`
continuous and bounded (`|f| ≤ Cf`), `φ(s) = ∫ f(y)·K(s, y) dy` is differentiable at `t` with
`φ′(t) = ∫ f(y)·∂_t K(t, y) dy`. The `s`-derivative `f(y)·K(s,y)·(y²−s)/(2s²)` is dominated,
uniformly over `s ∈ (t/2, 3t/2)`, by `Cf·(2√3/t²)·(y²+3t/2)·K(3t/2, y)` (integrable), using the
heat-kernel monotonicity `K(s, y) ≤ √3·K(3t/2, y)` on that interval. -/
private lemma hasDerivAt_phi {t : ℝ} (ht : 0 < t) {f : ℝ → ℝ} (hfc : Continuous f)
    {Cf : ℝ} (hCf : ∀ x, |f x| ≤ Cf) :
    HasDerivAt (fun s ↦ ∫ y, f y * heatKernel s y ∂volume)
      (∫ y, f y * (heatKernel t y * (y ^ 2 - t) / (2 * t ^ 2)) ∂volume) t := by
  have h32 : (0 : ℝ) < 3 * t / 2 := by positivity
  have hCf0 : 0 ≤ Cf := le_trans (abs_nonneg _) (hCf 0)
  have hf_gauss : Integrable f (gaussianReal 0 t.toNNReal) :=
    (integrable_const Cf).mono' hfc.aestronglyMeasurable
      (ae_of_all _ fun y ↦ by rw [Real.norm_eq_abs]; exact hCf y)
  refine hasDerivAt_integral_mul_kernelFamily (φ := fun s y ↦ heatKernel s y)
    (φ' := fun s y ↦ heatKernel s y * (y ^ 2 - s) / (2 * s ^ 2))
    (p₀ := t) (r := t / 2) hfc (by positivity)
    (fun s ↦ continuous_heatKernel s)
    (((continuous_heatKernel t).mul ((continuous_pow 2).sub continuous_const)).div_const _)
    (integrable_mul_heatKernel_of_gaussian ht hf_gauss)
    ((integrable_poly_heatKernel h32 (3 * t / 2)).const_mul (Cf * (2 * Real.sqrt 3 / t ^ 2)))
    ?_ (fun y s hs ↦ ?_)
  · -- uniform domination on `(t/2, 3t/2)`, via temporal monotonicity `heatKernel_temporal_le`
    refine ae_of_all _ fun y s hs ↦ ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hs_lo : t / 2 < s := by linarith [hs.1]
    have hs_hi : s < 3 * t / 2 := by linarith [hs.2]
    have hs_pos : 0 < s := by linarith
    have hKsnn : 0 ≤ heatKernel s y := heatKernel_nonneg hs_pos y
    have hKtnn : 0 ≤ heatKernel (3 * t / 2) y := heatKernel_nonneg h32 y
    have hK := heatKernel_temporal_le ht hs_lo hs_hi y
    have hpoly := sq_sub_div_le ht hs_lo hs_hi y
    have habs_nn : 0 ≤ |y ^ 2 - s| / (2 * s ^ 2) := by positivity
    have hF'norm : ‖f y * (heatKernel s y * (y ^ 2 - s) / (2 * s ^ 2))‖
        = |f y| * (heatKernel s y * (|y ^ 2 - s| / (2 * s ^ 2))) := by
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul,
          abs_of_nonneg hKsnn, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * s ^ 2), mul_div_assoc]
    rw [hF'norm]
    calc |f y| * (heatKernel s y * (|y ^ 2 - s| / (2 * s ^ 2)))
        ≤ Cf * (Real.sqrt 3 * heatKernel (3 * t / 2) y * (2 * (y ^ 2 + 3 * t / 2) / t ^ 2)) := by
          refine mul_le_mul (hCf y) ?_ (mul_nonneg hKsnn habs_nn) hCf0
          exact mul_le_mul hK hpoly habs_nn (mul_nonneg (Real.sqrt_nonneg 3) hKtnn)
      _ = Cf * (2 * Real.sqrt 3 / t ^ 2) * ((y ^ 2 + 3 * t / 2) * heatKernel (3 * t / 2) y) := by
          ring
  · -- pointwise kernel `s`-derivative
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact hasDerivAt_heatKernel_t (y := y) (by linarith [hs.1])

/-- **The Gaussian convolution satisfies the heat equation.** For `f ∈ C²_b`,
`φ(s) = ∫ f(y)·K(s, y) dy` has `φ′(t) = ½·∫ f′′(y)·K(t, y) dy`. Combines the parametric derivative
`hasDerivAt_phi` (`φ′(t) = ∫ f·∂_t K`) with the kernel PDE `∂_t K = ½·∂²_y K` and the double
integration by parts `∫ f·∂²_y K = ∫ f′′·K` (`ibp_heatKernel`). This is the heat equation for the
*function* `φ`, not merely the kernel. -/
private lemma hasDerivAt_phi_heatEq {t : ℝ} (ht : 0 < t) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''c : Continuous f'') {Cf Cf' Cf'' : ℝ}
    (hCf : ∀ x, |f x| ≤ Cf) (hCf' : ∀ x, |f' x| ≤ Cf') (hCf'' : ∀ x, |f'' x| ≤ Cf'') :
    HasDerivAt (fun s ↦ ∫ y, f y * heatKernel s y ∂volume)
      (1 / 2 * ∫ y, f'' y * heatKernel t y ∂volume) t := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x ↦ (hf x).continuousAt
  convert hasDerivAt_phi ht hfc hCf using 1
  rw [← ibp_heatKernel ht hf hf' hf''c hCf hCf' hCf'', ← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun y ↦ ?_)
  ring

/-- **The heat kernel is an approximate identity** (`ε → 0⁺`): for `f` continuous and bounded
(`|f| ≤ Cf`), `∫ f(y)·K(ε, y) dy → f(0)`. Proof by the rescaling `y = √ε·u`, which turns the
integral into `∫ f(√ε·u)·φ(u) du` against the *fixed* standard-normal density
`φ(u) = (2π)^{-1/2} e^{-u²/2}`, followed by dominated convergence (`f(√ε·u) → f(0)` pointwise,
dominated by the integrable `Cf·φ`). This supplies the `ε → 0` boundary value for the FTC. -/
private lemma tendsto_integral_heatKernel_zero {f : ℝ → ℝ} (hfc : Continuous f)
    {Cf : ℝ} (hCf : ∀ x, |f x| ≤ Cf) :
    Tendsto (fun ε ↦ ∫ y, f y * heatKernel ε y ∂volume) (nhdsWithin 0 (Set.Ioi 0))
      (nhds (f 0)) := by
  set g : ℝ → ℝ := fun u ↦ (Real.sqrt (2 * Real.pi))⁻¹ * Real.exp (-(1 / 2) * u ^ 2) with hg
  have hgc : Continuous g := by rw [hg]; fun_prop
  have hgnn : ∀ u, 0 ≤ g u := fun u ↦ by rw [hg]; positivity
  have hg_int : Integrable g volume :=
    (integrable_exp_neg_mul_sq (by norm_num : (0:ℝ) < 1 / 2)).const_mul (Real.sqrt (2 * Real.pi))⁻¹
  have hg_int1 : ∫ u, g u ∂volume = 1 := by
    simp only [hg]
    rw [integral_const_mul, integral_gaussian, show Real.pi / (1 / 2) = 2 * Real.pi from by ring,
      inv_mul_cancel₀ (by positivity : Real.sqrt (2 * Real.pi) ≠ 0)]
  -- rescaling identity `φ(ε) = ∫ u, f(√ε·u)·g(u)` for ε > 0
  have hrw : ∀ ε : ℝ, 0 < ε →
      (∫ y, f y * heatKernel ε y ∂volume) = ∫ u, f (Real.sqrt ε * u) * g u ∂volume := by
    intro ε hε
    have hsε : 0 < Real.sqrt ε := Real.sqrt_pos.mpr hε
    have hεne : ε ≠ 0 := hε.ne'
    have hscale : ∀ u, Real.sqrt ε * heatKernel ε (Real.sqrt ε * u) = g u := by
      intro u
      simp only [hg, heatKernel]
      have hse2 : Real.sqrt ε ^ 2 = ε := Real.sq_sqrt hε.le
      have hexp : -(Real.sqrt ε * u) ^ 2 / (2 * ε) = -(1 / 2) * u ^ 2 := by
        rw [mul_pow, hse2]; field_simp
      rw [hexp, Real.sqrt_mul (by positivity : (0:ℝ) ≤ 2 * Real.pi) ε, mul_inv]
      field_simp
    have hcomp := Measure.integral_comp_mul_left (fun y ↦ f y * heatKernel ε y) (Real.sqrt ε)
    rw [abs_of_pos (by positivity : (0:ℝ) < (Real.sqrt ε)⁻¹), smul_eq_mul] at hcomp
    have hkey : ∀ u, f (Real.sqrt ε * u) * g u
        = Real.sqrt ε * (f (Real.sqrt ε * u) * heatKernel ε (Real.sqrt ε * u)) := by
      intro u; rw [← hscale u]; ring
    rw [integral_congr_ae (Filter.Eventually.of_forall hkey), integral_const_mul, hcomp,
      ← mul_assoc, mul_inv_cancel₀ hsε.ne', one_mul]
  -- dominated convergence on the rescaled integrand
  have hlimeq : f 0 = ∫ u, f 0 * g u ∂volume := by rw [integral_const_mul, hg_int1, mul_one]
  rw [hlimeq]
  refine Tendsto.congr' (f₁ := fun ε ↦ ∫ u, f (Real.sqrt ε * u) * g u ∂volume)
    (by filter_upwards [self_mem_nhdsWithin] with ε hε using (hrw ε hε).symm) ?_
  refine tendsto_integral_filter_of_dominated_convergence (fun u ↦ Cf * g u) ?_ ?_
    (hg_int.const_mul Cf) ?_
  · filter_upwards [self_mem_nhdsWithin] with ε _hε
    exact ((hfc.comp (continuous_const.mul continuous_id)).mul hgc).aestronglyMeasurable
  · filter_upwards [self_mem_nhdsWithin] with ε _hε
    refine Filter.Eventually.of_forall fun u ↦ ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hgnn u)]
    exact mul_le_mul_of_nonneg_right (hCf _) (hgnn u)
  · refine Filter.Eventually.of_forall fun u ↦ ?_
    apply Tendsto.mul_const
    have hsqrt0 : Tendsto Real.sqrt (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have h := (Real.continuous_sqrt.tendsto 0).mono_left
        (nhdsWithin_le_nhds (a := (0:ℝ)) (s := Set.Ioi 0))
      rwa [Real.sqrt_zero] at h
    have h_inner : Tendsto (fun ε : ℝ ↦ Real.sqrt ε * u) (nhdsWithin 0 (Set.Ioi 0)) (nhds 0) := by
      have := hsqrt0.mul_const u; rwa [zero_mul] at this
    exact (hfc.tendsto 0).comp h_inner

/-- The heat kernel integrates to `1` over `ℝ` (it is a probability density), for `s > 0`. -/
private lemma integral_heatKernel_eq_one {s : ℝ} (hs : 0 < s) :
    ∫ y, heatKernel s y ∂volume = 1 := by
  rw [integral_congr_ae (Filter.Eventually.of_forall (heatKernel_eq_gaussianPDFReal hs))]
  exact integral_gaussianPDFReal_eq_one 0 (Real.toNNReal_pos.mpr hs).ne'

/-- Uniform bound on the time-derivative `φ′(s) = ½∫f′′·K(s,·)`: `|φ′(s)| ≤ ½·Cf′′` for `s > 0`.
Here `∫ K(s,·) = 1` and `|f′′| ≤ Cf′′`. This majorant makes `φ′` interval-integrable on `[0, t]`. -/
private lemma abs_half_integral_ddf_heatKernel_le {s : ℝ} (hs : 0 < s) {f'' : ℝ → ℝ}
    (_hf''c : Continuous f'') {Cf'' : ℝ} (hCf'' : ∀ x, |f'' x| ≤ Cf'') :
    |(1 / 2) * ∫ y, f'' y * heatKernel s y ∂volume| ≤ (1 / 2) * Cf'' := by
  rw [abs_mul, abs_of_nonneg (by norm_num : (0:ℝ) ≤ 1 / 2)]
  refine mul_le_mul_of_nonneg_left ?_ (by norm_num : (0:ℝ) ≤ 1 / 2)
  calc |∫ y, f'' y * heatKernel s y ∂volume|
      ≤ ∫ y, |f'' y * heatKernel s y| ∂volume := abs_integral_le_integral_abs
    _ ≤ ∫ y, Cf'' * heatKernel s y ∂volume := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y ↦ abs_nonneg _)
          ((integrable_heatKernel hs).const_mul Cf'') (Filter.Eventually.of_forall fun y ↦ ?_)
        change |f'' y * heatKernel s y| ≤ Cf'' * heatKernel s y
        rw [abs_mul, abs_of_nonneg (heatKernel_nonneg hs y)]
        exact mul_le_mul_of_nonneg_right (hCf'' y) (heatKernel_nonneg hs y)
    _ = Cf'' := by rw [integral_const_mul, integral_heatKernel_eq_one hs, mul_one]

/-- **Itô's formula in expectation — analytic core (Feynman–Kac).** For `f ∈ C²_b` and `t > 0`,
`∫ f(y)·K(t,y) dy = f(0) + ∫₀ᵗ ½·(∫ f′′(y)·K(s,y) dy) ds`. The Gaussian convolution at time `t`
equals its `t→0` boundary value `f(0)` plus the integral of its time-derivative
`φ′(s) = ½∫f′′·K(s,·)`. Proof: the fundamental theorem of calculus for the continuous-corrected
`Φ` (value `φ(s)` for `s>0`, `f(0)` at `s=0`), whose right derivative on `(0,t)` is `φ′`
(`hasDerivAt_phi_heatEq`), whose boundary value is the approximate-identity limit
(`tendsto_integral_heatKernel_zero`), and whose derivative is interval-integrable (bounded by
`½Cf′′`). Under the standard Brownian hypotheses this reads `E[f(Bₜ)] = f(0) + ½∫₀ᵗ E[f′′(Bₛ)] ds`
via `feynmanU_eq_expectation`. -/
theorem heatConvolution_eq_add_integral_deriv {t : ℝ} (ht : 0 < t) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''c : Continuous f'') {Cf Cf' Cf'' : ℝ}
    (hCf : ∀ x, |f x| ≤ Cf) (hCf' : ∀ x, |f' x| ≤ Cf') (hCf'' : ∀ x, |f'' x| ≤ Cf'') :
    (∫ y, f y * heatKernel t y ∂volume)
      = f 0 + ∫ s in (0:ℝ)..t, (1 / 2) * ∫ y, f'' y * heatKernel s y ∂volume := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x ↦ (hf x).continuousAt
  set φ : ℝ → ℝ := fun s ↦ ∫ y, f y * heatKernel s y ∂volume with hφdef
  set ψ : ℝ → ℝ := fun s ↦ (1 / 2) * ∫ y, f'' y * heatKernel s y ∂volume with hψdef
  set Φ : ℝ → ℝ := fun s ↦ if 0 < s then φ s else f 0 with hΦdef
  -- (a) `ψ = φ′` is interval-integrable on `[0, t]` (continuous on `(0,t]`, bounded by `½Cf′′`)
  have hψ_cont : ∀ s : ℝ, 0 < s → ContinuousAt ψ s := fun s hs ↦
    (hasDerivAt_phi hs hf''c hCf'').continuousAt.const_mul (1 / 2)
  have hψ_int : IntervalIntegrable ψ volume 0 t := by
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.le]
    refine Integrable.mono' (g := fun _ : ℝ ↦ (1 / 2) * Cf'')
      (integrableOn_const (hs := measure_Ioc_lt_top.ne))
      (ContinuousOn.aestronglyMeasurable (fun s hs ↦ (hψ_cont s hs.1).continuousWithinAt)
        measurableSet_Ioc)
      (ae_restrict_of_forall_mem measurableSet_Ioc fun s hs ↦ ?_)
    change ‖(1 / 2) * ∫ y, f'' y * heatKernel s y ∂volume‖ ≤ (1 / 2) * Cf''
    rw [Real.norm_eq_abs]
    exact abs_half_integral_ddf_heatKernel_le hs.1 hf''c hCf''
  -- (b) `Φ` is continuous on `[0, t]`
  have hΦ_cont : ContinuousOn Φ (Set.Icc 0 t) := by
    intro s hs
    rcases eq_or_lt_of_le hs.1 with h0 | h0
    · rw [← h0, ContinuousWithinAt, show Φ 0 = f 0 from ite_eq_right (lt_irrefl 0),
        show Set.Icc (0:ℝ) t = {0} ∪ Set.Ioc 0 t from by
          rw [Set.union_comm, Set.Ioc_union_left ht.le],
        nhdsWithin_union, nhdsWithin_singleton, tendsto_sup]
      refine ⟨by rw [← show Φ 0 = f 0 from ite_eq_right (lt_irrefl 0)]; exact tendsto_pure_nhds Φ 0,
        ?_⟩
      refine Filter.Tendsto.congr' ?_ ((tendsto_integral_heatKernel_zero hfc hCf).mono_left
        (nhdsWithin_mono 0 Set.Ioc_subset_Ioi_self))
      filter_upwards [self_mem_nhdsWithin] with x hx using (ite_eq_left hx.1).symm
    · have hca : ContinuousAt Φ s := by
        refine (hasDerivAt_phi h0 hfc hCf).continuousAt.congr ?_
        filter_upwards [lt_mem_nhds h0] with x hx using (ite_eq_left hx).symm
      exact hca.continuousWithinAt
  -- (c) right derivative of `Φ` on `(0, t)` is `ψ`
  have hΦ_deriv : ∀ s ∈ Set.Ioo (0:ℝ) t, HasDerivWithinAt Φ (ψ s) (Set.Ioi s) s := by
    intro s hs
    have heq : Φ =ᶠ[nhds s] φ := by
      filter_upwards [lt_mem_nhds hs.1] with x hx using ite_eq_left hx
    exact ((hasDerivAt_phi_heatEq hs.1 hf hf' hf''c hCf hCf' hCf'').congr_of_eventuallyEq
      heq).hasDerivWithinAt
  -- (d) FTC, then read off the boundary values `Φ t = φ t`, `Φ 0 = f 0`
  have hFTC :=
      intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le ht.le hΦ_cont hΦ_deriv hψ_int
  rw [show Φ t = φ t from ite_eq_left ht, show Φ 0 = f 0 from ite_eq_right (lt_irrefl 0)] at hFTC
  linarith [hFTC]

/-! ### The Feynman–Kac function `u(t, x) = ∫ z, g(z) · K(t, z - x) dz`

We define `u` directly via the heat-kernel representation, then show it equals
the textbook formula `E[g(x + B_t)]` under the standard BM hypotheses. -/

/-- Feynman–Kac heat-kernel function: `u(t, x) = ∫ z, g(z) · K(t, z − x) dz`.
This form is symmetric to `∫ y, g(x + y) · K(t, y) dy` by Lebesgue translation
invariance, but is easier to differentiate in `x` (the `x`-dependence sits in
the kernel argument, not in `g`). -/
noncomputable def feynmanU (g : ℝ → ℝ) (t x : ℝ) : ℝ :=
  ∫ z, g z * heatKernel t (z - x) ∂volume

/-! ### Equivalence of forms: `∫ y, g(x+y) · K(t, y) dy = ∫ z, g(z) · K(t, z-x) dz` -/

/-- Lebesgue translation invariance: `∫ y, g(x+y) · K(t, y) dy = feynmanU g t x`. -/
private lemma integral_shift_eq_feynmanU (g : ℝ → ℝ) (t x : ℝ) :
    ∫ y, g (x + y) * heatKernel t y ∂volume = feynmanU g t x := by
  rw [feynmanU]
  have h_fun_eq : (fun z ↦ g z * heatKernel t (z - x))
        = (fun z ↦ g (x + (z - x)) * heatKernel t (z - x)) := by
    funext z; congr 2; ring
  rw [h_fun_eq]
  exact (MeasureTheory.integral_sub_right_eq_self
    (fun z ↦ g (x + z) * heatKernel t z) x).symm

/-! ### Identification of `feynmanU` with `E[g(x + B_t)]` -/

variable {Ω : Type*} [MeasurableSpace Ω] {μ : Measure Ω}

/-- **Core transfer.** If `B_t` has law `N(0, t)`
(`Measure.map (B t) μ = gaussianReal 0 t.toNNReal`), the heat-kernel form `feynmanU g t x` equals
the expectation `E[g(x + B_t)]`. Factored out of `feynmanU_eq_expectation` so the same transfer
serves both the increment-hypothesis bundle and the `IsPreBrownianReal` marginal law. -/
theorem feynmanU_eq_integral_of_map
    {B : ℝ → Ω → ℝ} {g : ℝ → ℝ} {t : ℝ}
    (h_aem : AEMeasurable (B t) μ)
    (h_map : Measure.map (B t) μ = gaussianReal 0 t.toNNReal)
    (hg_cont : Continuous g) (ht : 0 < t) (x : ℝ) :
    feynmanU g t x = ∫ ω, g (x + B t ω) ∂μ := by
  have h_eg_cont : Continuous (fun y ↦ g (x + y)) :=
    hg_cont.comp (continuous_const.add continuous_id)
  have h_eg_smeas_map : AEStronglyMeasurable (fun y ↦ g (x + y)) (Measure.map (B t) μ) :=
    h_eg_cont.aestronglyMeasurable
  have h_expect_eq_gauss :
      ∫ ω, g (x + B t ω) ∂μ = ∫ y, g (x + y) ∂(gaussianReal 0 t.toNNReal) := by
    have h_map' : ∫ y, g (x + y) ∂(Measure.map (B t) μ) = ∫ ω, g (x + B t ω) ∂μ :=
      integral_map h_aem h_eg_smeas_map
    rw [← h_map', h_map]
  have h_tN_ne : (t.toNNReal : ℝ≥0) ≠ 0 := (Real.toNNReal_pos.mpr ht).ne'
  have h_gauss_eq_pdf :
      ∫ y, g (x + y) ∂(gaussianReal 0 t.toNNReal) =
        ∫ y, gaussianPDFReal 0 t.toNNReal y • g (x + y) ∂volume :=
    integral_gaussianReal_eq_integral_smul (μ := 0) (v := t.toNNReal)
      (f := fun y ↦ g (x + y)) h_tN_ne
  have h_pdf_eq_heat : ∀ y,
      gaussianPDFReal 0 t.toNNReal y • g (x + y) = g (x + y) * heatKernel t y := by
    intro y
    rw [← heatKernel_eq_gaussianPDFReal ht y, smul_eq_mul, mul_comm]
  rw [h_expect_eq_gauss, h_gauss_eq_pdf,
    show (fun y ↦ gaussianPDFReal 0 t.toNNReal y • g (x + y))
        = (fun y ↦ g (x + y) * heatKernel t y) from funext h_pdf_eq_heat]
  exact (integral_shift_eq_feynmanU g t x).symm

/-- For `t > 0`, the heat-kernel form `feynmanU g t x` equals the Feynman–Kac
expectation `E[g(x + B_t)]`, assuming:
* `B 0 = 0` a.s.
* `B_t − B_0 ∼ N(0, t)` (Gaussian increments at the origin),
* `B_t` is measurable,
* `g` is continuous. -/
theorem feynmanU_eq_expectation
    {B : ℝ → Ω → ℝ} {g : ℝ → ℝ}
    (hB_meas : ∀ t, Measurable (B t))
    (hB_zero : ∀ᵐ ω ∂μ, B 0 ω = 0)
    (hB_gauss : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ∃ v : NNReal, (v : ℝ) = t - s ∧
        Measure.map (fun ω ↦ B t ω - B s ω) μ = gaussianReal 0 v)
    (hg_cont : Continuous g)
    {t : ℝ} (ht : 0 < t) (x : ℝ) :
    feynmanU g t x = ∫ ω, g (x + B t ω) ∂μ := by
  -- Step 1: Use `B 0 = 0 a.s.` and `gauss_increments` at (0, t) to deduce
  -- Measure.map (B t) μ = gaussianReal 0 t.toNNReal.
  obtain ⟨v, hv_eq, h_map_diff⟩ := hB_gauss ht.le
  have hv_eq_t : (v : ℝ) = t := by rw [hv_eq]; ring
  have hv_t : v = t.toNNReal := by
    apply NNReal.coe_inj.mp
    rw [hv_eq_t, Real.coe_toNNReal _ ht.le]
  have h_diff_eq : (fun ω ↦ B t ω - B 0 ω) =ᵐ[μ] (fun ω ↦ B t ω) := by
    filter_upwards [hB_zero] with ω hω
    rw [hω, sub_zero]
  have h_map_Bt : Measure.map (B t) μ = gaussianReal 0 t.toNNReal := by
    rw [← hv_t, ← h_map_diff]
    exact (Measure.map_congr h_diff_eq).symm
  -- Steps 2–5 are the core transfer, now factored out:
  exact feynmanU_eq_integral_of_map (hB_meas t).aemeasurable h_map_Bt hg_cont ht x

/-- The boundary condition: at `t = 0`, the Feynman-Kac expectation equals `g(x)`
(since `B 0 = 0` a.s. and `μ` is a probability measure). -/
theorem feynmanKac_boundary [IsProbabilityMeasure μ]
    {B : ℝ → Ω → ℝ} {g : ℝ → ℝ}
    (hB_zero : ∀ᵐ ω ∂μ, B 0 ω = 0) (x : ℝ) :
    ∫ ω, g (x + B 0 ω) ∂μ = g x := by
  have h_pt : ∀ᵐ ω ∂μ, g (x + B 0 ω) = g x := by
    filter_upwards [hB_zero] with ω hω
    rw [hω, add_zero]
  rw [integral_congr_ae h_pt, integral_const, probReal_univ, one_smul]

/-- **Itô's formula in expectation** (Dynkin / Kolmogorov form). For a Brownian motion `B`
(`B 0 = 0` a.s., Gaussian increments `B_t − B_s ∼ N(0, t−s)`, each `B_t` measurable) and
`f ∈ C²_b`, `E[f(Bₜ)] = f(0) + ½·∫₀ᵗ E[f′′(Bₛ)] ds` for `t > 0`. This is the expectation form of
the analytic Feynman–Kac identity `heatConvolution_eq_add_integral_deriv`, transported across the
bridge `feynmanU_eq_expectation` (`∫ g·K(r,·) = E[g(B_r)]`). The `½ f′′` term is the signature of
the quadratic variation of Brownian motion — the source of the Itô correction. -/
theorem expectation_ito
    {B : ℝ → Ω → ℝ}
    (hB_meas : ∀ t, Measurable (B t))
    (hB_zero : ∀ᵐ ω ∂μ, B 0 ω = 0)
    (hB_gauss : ∀ ⦃s t : ℝ⦄, s ≤ t →
      ∃ v : NNReal, (v : ℝ) = t - s ∧
        Measure.map (fun ω ↦ B t ω - B s ω) μ = gaussianReal 0 v)
    {t : ℝ} (ht : 0 < t) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''c : Continuous f'') {Cf Cf' Cf'' : ℝ}
    (hCf : ∀ x, |f x| ≤ Cf) (hCf' : ∀ x, |f' x| ≤ Cf') (hCf'' : ∀ x, |f'' x| ≤ Cf'') :
    (∫ ω, f (B t ω) ∂μ) = f 0 + ∫ s in (0:ℝ)..t, (1 / 2) * ∫ ω, f'' (B s ω) ∂μ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x ↦ (hf x).continuousAt
  -- the heat-kernel ↔ expectation bridge, for any continuous `g` and time `r > 0`
  have hbridge : ∀ (g : ℝ → ℝ), Continuous g → ∀ {r : ℝ}, 0 < r →
      (∫ y, g y * heatKernel r y ∂volume) = ∫ ω, g (B r ω) ∂μ := by
    intro g hgc r hr
    have h1 := integral_shift_eq_feynmanU g r 0
    simp only [zero_add] at h1
    rw [h1, feynmanU_eq_expectation hB_meas hB_zero hB_gauss hgc hr 0]
    simp only [zero_add]
  rw [← hbridge f hfc ht, heatConvolution_eq_add_integral_deriv ht hf hf' hf''c hCf hCf' hCf'']
  congr 1
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs ↦ ?_)
  rw [Set.uIoc_of_le ht.le] at hs
  show (1 / 2) * ∫ y, f'' y * heatKernel s y ∂volume = (1 / 2) * ∫ ω, f'' (B s ω) ∂μ
  rw [hbridge f'' hf''c hs.1]

/-- **Itô's formula in expectation for a pre-Brownian motion** — the repo-standard
`IsPreBrownianReal` (Degenne) reading of `expectation_ito`. For `f ∈ C²_b` and `t > 0`,
`E[f(X_t)] = f(0) + ½·∫₀ᵗ E[f′′(X_s)] ds`. The increment-law hypotheses are discharged from the
marginal law `IsPreBrownianReal.hasLaw_eval` through the shared transfer
`feynmanU_eq_integral_of_map`. (`X` is `ℝ≥0`-indexed; the `∫₀ᵗ` runs over real `s`, so `X` is read
at `·.toNNReal`.) -/
theorem expectation_ito_isPreBrownian {X : ℝ≥0 → Ω → ℝ} (hX : IsPreBrownianReal X μ)
    {t : ℝ} (ht : 0 < t) {f f' f'' : ℝ → ℝ}
    (hf : ∀ x, HasDerivAt f (f' x) x) (hf' : ∀ x, HasDerivAt f' (f'' x) x)
    (hf''c : Continuous f'') {Cf Cf' Cf'' : ℝ}
    (hCf : ∀ x, |f x| ≤ Cf) (hCf' : ∀ x, |f' x| ≤ Cf') (hCf'' : ∀ x, |f'' x| ≤ Cf'') :
    (∫ ω, f (X t.toNNReal ω) ∂μ)
      = f 0 + ∫ s in (0:ℝ)..t, (1 / 2) * ∫ ω, f'' (X s.toNNReal ω) ∂μ := by
  have hfc : Continuous f := continuous_iff_continuousAt.mpr fun x ↦ (hf x).continuousAt
  have hbridge : ∀ (g : ℝ → ℝ), Continuous g → ∀ {r : ℝ}, 0 < r →
      (∫ y, g y * heatKernel r y ∂volume) = ∫ ω, g (X r.toNNReal ω) ∂μ := by
    intro g hgc r hr
    have h1 := integral_shift_eq_feynmanU g r 0
    simp only [zero_add] at h1
    rw [h1, feynmanU_eq_integral_of_map (B := fun s ↦ X s.toNNReal) (t := r)
      (hX.aemeasurable r.toNNReal)
      (hX.hasLaw_eval r.toNNReal).map_eq hgc hr 0]
    simp only [zero_add]
  rw [← hbridge f hfc ht, heatConvolution_eq_add_integral_deriv ht hf hf' hf''c hCf hCf' hCf'']
  congr 1
  refine intervalIntegral.integral_congr_ae (ae_of_all _ fun s hs ↦ ?_)
  rw [Set.uIoc_of_le ht.le] at hs
  show (1 / 2) * ∫ y, f'' y * heatKernel s y ∂volume = (1 / 2) * ∫ ω, f'' (X s.toNNReal ω) ∂μ
  rw [hbridge f'' hf''c hs.1]

/-! ### Kernel-side heat equation for `feynmanU` (sub-Gaussian payoff)

For `h` continuous with `|h z| ≤ eᶻ` (the call payoff `(eᶻ − K)⁺ ≤ eᶻ` qualifies) and `t > 0`,
`u(t, x) = feynmanU h t x` is twice differentiable in `x`, differentiable in `t`, and satisfies the
heat equation `∂_t u = ½ ∂_xx u`. Every derivative falls on the smooth, fast-decaying *kernel*; `h`
needs no regularity beyond the growth bound. The three diff-under-integral lemmas mirror
`hasDerivAt_phi`, replacing its bounded `|f| ≤ Cf` by the sub-Gaussian envelope
`integrable_exp_mul_poly_heatKernel` and (for the `x`-derivatives) its temporal monotonicity by the
spatial `heatKernel_shift_le`. This kernel-side heat equation for `u` (`feynmanU_heat_equation`,
with the derivatives below) is consumed by the Black–Scholes-PDE keystone `sc-bs-pde-feynman-kac`.
-/

/-- **Time-derivative of the Feynman–Kac function** (kernel-side, sub-Gaussian payoff). For `h`
continuous with `|h z| ≤ eᶻ` and `t > 0`,
`∂_t (feynmanU h t x) = ∫ z, h z · K(t, z−x)·((z−x)²−t)/(2t²) dz`. The sub-Gaussian analogue of
`hasDerivAt_phi`: the `s`-derivative is dominated, uniformly over `s ∈ (t/2, 3t/2)`, by the
integrable envelope `(2√3/t²)·eᶻ·((z−x)²+3t/2)·K(3t/2, z−x)`, via the temporal monotonicity
`K(s, w) ≤ √3·K(3t/2, w)`. Differentiating the kernel (not the payoff) is what frees `h` of any
regularity beyond exponential growth — the call payoff's kink is irrelevant. -/
theorem hasDerivAt_feynmanU_t {t : ℝ} (ht : 0 < t) {h : ℝ → ℝ} (hhc : Continuous h)
    (hh : ∀ z, |h z| ≤ Real.exp z) (x : ℝ) :
    HasDerivAt (fun s ↦ feynmanU h s x)
      (∫ z, h z * (heatKernel t (z - x) * ((z - x) ^ 2 - t) / (2 * t ^ 2)) ∂volume) t := by
  change HasDerivAt (fun s ↦ ∫ z, h z * heatKernel s (z - x) ∂volume)
      (∫ z, h z * (heatKernel t (z - x) * ((z - x) ^ 2 - t) / (2 * t ^ 2)) ∂volume) t
  have h32 : (0 : ℝ) < 3 * t / 2 := by positivity
  refine hasDerivAt_integral_mul_kernelFamily (φ := fun s z ↦ heatKernel s (z - x))
    (φ' := fun s z ↦ heatKernel s (z - x) * ((z - x) ^ 2 - s) / (2 * s ^ 2))
    (p₀ := t) (r := t / 2) hhc (by positivity)
    (fun s ↦ (continuous_heatKernel s).comp (continuous_id.sub continuous_const))
    (((continuous_heatKernel t).comp (continuous_id.sub continuous_const)).mul
        (((continuous_id.sub continuous_const).pow 2).sub continuous_const) |>.div_const _)
    (integrable_payoff_mul_heatKernel ht hhc hh x)
    ((integrable_exp_mul_poly_heatKernel h32 x (3 * t / 2)).const_mul (2 * Real.sqrt 3 / t ^ 2))
    ?_ (fun z s hs ↦ ?_)
  · -- uniform domination on `(t/2, 3t/2)`, via temporal monotonicity `heatKernel_temporal_le`
    refine ae_of_all _ fun z s hs ↦ ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hs_lo : t / 2 < s := by linarith [hs.1]
    have hs_hi : s < 3 * t / 2 := by linarith [hs.2]
    have hs_pos : 0 < s := by linarith
    have hKsnn : 0 ≤ heatKernel s (z - x) := heatKernel_nonneg hs_pos (z - x)
    have hKtnn : 0 ≤ heatKernel (3 * t / 2) (z - x) := heatKernel_nonneg h32 (z - x)
    have hK := heatKernel_temporal_le ht hs_lo hs_hi (z - x)
    have hpoly := sq_sub_div_le ht hs_lo hs_hi (z - x)
    have habs_nn : 0 ≤ |(z - x) ^ 2 - s| / (2 * s ^ 2) := by positivity
    have hF'norm : ‖h z * (heatKernel s (z - x) * ((z - x) ^ 2 - s) / (2 * s ^ 2))‖
        = |h z| * (heatKernel s (z - x) * (|(z - x) ^ 2 - s| / (2 * s ^ 2))) := by
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul,
          abs_of_nonneg hKsnn, abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * s ^ 2), mul_div_assoc]
    rw [hF'norm]
    calc |h z| * (heatKernel s (z - x) * (|(z - x) ^ 2 - s| / (2 * s ^ 2)))
        ≤ Real.exp z
            * (Real.sqrt 3 * heatKernel (3 * t / 2) (z - x)
              * (2 * ((z - x) ^ 2 + 3 * t / 2) / t ^ 2)) := by
          refine mul_le_mul (hh z) ?_ (mul_nonneg hKsnn habs_nn) (Real.exp_nonneg z)
          exact mul_le_mul hK hpoly habs_nn (mul_nonneg (Real.sqrt_nonneg 3) hKtnn)
      _ = (2 * Real.sqrt 3 / t ^ 2)
            * (Real.exp z * (((z - x) ^ 2 + 3 * t / 2) * heatKernel (3 * t / 2) (z - x))) := by
          ring
  · -- pointwise kernel `s`-derivative
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    exact hasDerivAt_heatKernel_t (y := z - x) (by linarith [hs.1])

/-- **Space-derivative of the Feynman–Kac function** (kernel-side, sub-Gaussian payoff). For `h`
continuous with `|h z| ≤ eᶻ` and `t > 0`,
`∂_x (feynmanU h t x) = ∫ z, h z · ((z−x)/t)·K(t, z−x) dz`. Differentiating the shifted kernel in
`x` via `hasDerivAt_heatKernel_x`; dominated, uniformly over `x' ∈ ball x 1`, by the integrable
envelope `(√2·e^{1/2t}/t)·eᶻ·((z−x)²+2)·K(2t, z−x)` (`integrable_exp_mul_poly_heatKernel` at σ=2t),
via the spatial monotonicity `heatKernel_shift_le`. -/
theorem hasDerivAt_feynmanU_x {t : ℝ} (ht : 0 < t) {h : ℝ → ℝ} (hhc : Continuous h)
    (hh : ∀ z, |h z| ≤ Real.exp z) (x : ℝ) :
    HasDerivAt (fun x' ↦ feynmanU h t x')
      (∫ z, h z * ((z - x) / t * heatKernel t (z - x)) ∂volume) x := by
  change HasDerivAt (fun x' ↦ ∫ z, h z * heatKernel t (z - x') ∂volume)
      (∫ z, h z * ((z - x) / t * heatKernel t (z - x)) ∂volume) x
  have h2t : (0 : ℝ) < 2 * t := by positivity
  refine hasDerivAt_integral_mul_kernelFamily (φ := fun x' z ↦ heatKernel t (z - x'))
    (φ' := fun x' z ↦ (z - x') / t * heatKernel t (z - x'))
    (p₀ := x) (r := 1) hhc (by norm_num)
    (fun c ↦ (continuous_heatKernel t).comp (continuous_id.sub continuous_const))
    (((continuous_id.sub continuous_const).div_const t).mul
      ((continuous_heatKernel t).comp (continuous_id.sub continuous_const)))
    (integrable_payoff_mul_heatKernel ht hhc hh x)
    ((integrable_exp_mul_poly_heatKernel h2t x 2).const_mul
      (Real.sqrt 2 * Real.exp (1 / (2 * t)) / t))
    ?_ (fun z x' _ ↦ hasDerivAt_heatKernel_x ht z x')
  · -- uniform domination on `ball x 1`, via spatial monotonicity `heatKernel_shift_le`
    refine ae_of_all _ fun z x' hx' ↦ ?_
    rw [Metric.mem_ball, Real.dist_eq] at hx'
    have hKsnn : 0 ≤ heatKernel t (z - x') := heatKernel_nonneg ht (z - x')
    have hKshift : heatKernel t (z - x')
        ≤ Real.sqrt 2 * Real.exp (1 / (2 * t)) * heatKernel (2 * t) (z - x) := by
      simpa [one_pow] using heatKernel_shift_le ht hx' z
    have habs2 : |z - x'| ≤ (z - x) ^ 2 + 2 := by
      have htri : |z - x'| ≤ |z - x| + |x - x'| := by
        have hsplit : z - x' = (z - x) + (x - x') := by ring
        rw [hsplit]; exact abs_add_le _ _
      have hxx : |x - x'| ≤ 1 := by rw [abs_sub_comm]; linarith [hx']
      have hsq : |z - x| ≤ (z - x) ^ 2 + 1 := by
        nlinarith [sq_nonneg (|z - x| - 1), sq_abs (z - x), abs_nonneg (z - x)]
      linarith
    have hF'norm : ‖h z * ((z - x') / t * heatKernel t (z - x'))‖
        = 1 / t * (|h z| * (|z - x'| * heatKernel t (z - x'))) := by
      rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_nonneg hKsnn, abs_of_nonneg ht.le]
      ring
    rw [hF'norm]
    have hstep : |h z| * (|z - x'| * heatKernel t (z - x'))
        ≤ Real.exp z
            * (((z - x) ^ 2 + 2)
              * (Real.sqrt 2 * Real.exp (1 / (2 * t)) * heatKernel (2 * t) (z - x))) := by
      refine mul_le_mul (hh z) ?_ (mul_nonneg (abs_nonneg _) hKsnn) (Real.exp_nonneg z)
      exact mul_le_mul habs2 hKshift hKsnn (by positivity)
    calc 1 / t * (|h z| * (|z - x'| * heatKernel t (z - x')))
        ≤ 1 / t
            * (Real.exp z
              * (((z - x) ^ 2 + 2)
                * (Real.sqrt 2 * Real.exp (1 / (2 * t)) * heatKernel (2 * t) (z - x)))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (Real.sqrt 2 * Real.exp (1 / (2 * t)) / t)
            * (Real.exp z * (((z - x) ^ 2 + 2) * heatKernel (2 * t) (z - x))) := by ring

/-- **Second space-derivative of the Feynman–Kac function**. The derivative of the first-space-
derivative integral is `∫ z, h z · K(t, z−x)·((z−x)²−t)/t² dz`. Same template, now differentiating
`hasDerivAt_heatKernel_x_x`; dominated over `x' ∈ ball x 1` by the envelope at `σ=2t, d=3+t`
(using `|(z−x')²−t| ≤ 3((z−x)²+(3+t))`). -/
theorem hasDerivAt_feynmanU_xx {t : ℝ} (ht : 0 < t) {h : ℝ → ℝ} (hhc : Continuous h)
    (hh : ∀ z, |h z| ≤ Real.exp z) (x : ℝ) :
    HasDerivAt (fun x' ↦ ∫ z, h z * ((z - x') / t * heatKernel t (z - x')) ∂volume)
      (∫ z, h z * (heatKernel t (z - x) * ((z - x) ^ 2 - t) / t ^ 2) ∂volume) x := by
  have h2t : (0 : ℝ) < 2 * t := by positivity
  refine hasDerivAt_integral_mul_kernelFamily
    (φ := fun x' z ↦ (z - x') / t * heatKernel t (z - x'))
    (φ' := fun x' z ↦ heatKernel t (z - x') * ((z - x') ^ 2 - t) / t ^ 2)
    (p₀ := x) (r := 1) hhc (by norm_num)
    (fun c ↦ ((continuous_id.sub continuous_const).div_const t).mul
      ((continuous_heatKernel t).comp (continuous_id.sub continuous_const)))
    (((continuous_heatKernel t).comp (continuous_id.sub continuous_const)).mul
        (((continuous_id.sub continuous_const).pow 2).sub continuous_const) |>.div_const _)
    ?_
    ((integrable_exp_mul_poly_heatKernel h2t x (3 + t)).const_mul
      (3 * Real.sqrt 2 * Real.exp (1 / (2 * t)) / t ^ 2))
    ?_ (fun z x' _ ↦ hasDerivAt_heatKernel_x_x ht z x')
  · -- the first-derivative integrand is integrable at the base point
    apply ((integrable_exp_mul_poly_heatKernel ht x 1).const_mul (1 / t)).mono'
    · exact (hhc.mul (((continuous_id.sub continuous_const).div_const t).mul
        ((continuous_heatKernel t).comp (continuous_id.sub continuous_const)))).aestronglyMeasurable
    · refine ae_of_all _ fun z ↦ ?_
      have hKnn := heatKernel_nonneg ht (z - x)
      have hnorm : ‖h z * ((z - x) / t * heatKernel t (z - x))‖
          = 1 / t * (|h z| * (|z - x| * heatKernel t (z - x))) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_div, abs_of_nonneg hKnn,
            abs_of_nonneg ht.le]; ring
      rw [hnorm]
      have habs1 : |z - x| ≤ (z - x) ^ 2 + 1 := by
        nlinarith [sq_nonneg (|z - x| - 1), sq_abs (z - x), abs_nonneg (z - x)]
      apply mul_le_mul_of_nonneg_left _ (by positivity : (0:ℝ) ≤ 1 / t)
      refine mul_le_mul (hh z) ?_ (mul_nonneg (abs_nonneg _) hKnn) (Real.exp_nonneg z)
      exact mul_le_mul_of_nonneg_right habs1 hKnn
  · -- uniform domination on `ball x 1`, via spatial monotonicity `heatKernel_shift_le`
    refine ae_of_all _ fun z x' hx' ↦ ?_
    rw [Metric.mem_ball, Real.dist_eq] at hx'
    have hKsnn : 0 ≤ heatKernel t (z - x') := heatKernel_nonneg ht (z - x')
    have hKshift : heatKernel t (z - x')
        ≤ Real.sqrt 2 * Real.exp (1 / (2 * t)) * heatKernel (2 * t) (z - x) := by
      simpa [one_pow] using heatKernel_shift_le ht hx' z
    have hb : (x - x') ^ 2 ≤ 1 := by
      have hxx : |x - x'| ≤ 1 := by rw [abs_sub_comm]; linarith [hx']
      nlinarith [sq_abs (x - x'), hxx, abs_nonneg (x - x')]
    have habs2 : |(z - x') ^ 2 - t| ≤ 3 * ((z - x) ^ 2 + (3 + t)) := by
      rw [abs_le]
      refine ⟨?_, ?_⟩
      · nlinarith
          [sq_nonneg (z - x), sq_nonneg (z - 2 * x + x'), sq_nonneg (2 * (z - x) + (x - x')),
          hb, ht.le, sq_nonneg (z - x')]
      · nlinarith
          [sq_nonneg (z - x), sq_nonneg (z - 2 * x + x'), sq_nonneg (2 * (z - x) + (x - x')),
          hb, ht.le, sq_nonneg (z - x')]
    have hF'norm : ‖h z * (heatKernel t (z - x') * ((z - x') ^ 2 - t) / t ^ 2)‖
        = 1 / t ^ 2 * (|h z| * (heatKernel t (z - x') * |(z - x') ^ 2 - t|)) := by
      rw [Real.norm_eq_abs, abs_mul, abs_div, abs_mul, abs_of_nonneg hKsnn,
          abs_of_nonneg (by positivity : (0:ℝ) ≤ t ^ 2)]
      ring
    rw [hF'norm]
    have hstep : |h z| * (heatKernel t (z - x') * |(z - x') ^ 2 - t|)
        ≤ Real.exp z
            * ((Real.sqrt 2 * Real.exp (1 / (2 * t)) * heatKernel (2 * t) (z - x))
              * (3 * ((z - x) ^ 2 + (3 + t)))) := by
      refine mul_le_mul (hh z) ?_ (mul_nonneg hKsnn (abs_nonneg _)) (Real.exp_nonneg z)
      exact mul_le_mul hKshift habs2 (abs_nonneg _)
        (mul_nonneg (mul_nonneg (Real.sqrt_nonneg 2) (Real.exp_nonneg _))
          (heatKernel_nonneg h2t (z - x)))
    calc 1 / t ^ 2 * (|h z| * (heatKernel t (z - x') * |(z - x') ^ 2 - t|))
        ≤ 1 / t ^ 2
            * (Real.exp z
              * ((Real.sqrt 2 * Real.exp (1 / (2 * t)) * heatKernel (2 * t) (z - x))
                * (3 * ((z - x) ^ 2 + (3 + t))))) :=
          mul_le_mul_of_nonneg_left hstep (by positivity)
      _ = (3 * Real.sqrt 2 * Real.exp (1 / (2 * t)) / t ^ 2)
            * (Real.exp z * (((z - x) ^ 2 + (3 + t)) * heatKernel (2 * t) (z - x))) := by ring

/-- **Derivative of the Feynman–Kac function along an affine curve** `s ↦ (α s, x₀ + β s)`
(kernel-side, sub-Gaussian payoff). For `h` continuous with `|h z| ≤ eᶻ`, `α > 0`, `τ > 0`, the
price `s ↦ feynmanU h (α s) (x₀ + β s)` — with both kernel arguments moving — is differentiable at
`τ` with `d/ds = ∫ z, h z · (α·∂_t K + β·∂_x K)`. This is the Black–Scholes `τ`-derivative engine
(`α = σ²`, `β = r − σ²/2`, `x₀ = log S`) and the consumer that makes the heat kernel's joint
differentiability `hasFDerivAt_heatKernel` load-bearing for pricing. Pointwise derivative:
`hasDerivAt_heatKernel_comp`. The uniform domination on `s ∈ (τ/2, 3τ/2)` bounds the two terms
*separately* by Gaussian-moment envelopes (`integrable_exp_mul_poly_heatKernel`) via
`heatKernel_loc_le` + `curve_sq_ratio_le` / `curve_abs_ratio_le` — no single mega-constant — fed to
`hasDerivAt_integral_mul_kernelFamily`. -/
theorem hasDerivAt_feynmanU_comp {h : ℝ → ℝ} (hhc : Continuous h) (hh : ∀ z, |h z| ≤ Real.exp z)
    {α β x₀ τ : ℝ} (hα : 0 < α) (hτ : 0 < τ) :
    HasDerivAt (fun s ↦ feynmanU h (α * s) (x₀ + β * s))
      (∫ z, h z * (α * (heatKernel (α * τ) (z - (x₀ + β * τ))
              * ((z - (x₀ + β * τ)) ^ 2 - α * τ) / (2 * (α * τ) ^ 2))
          + β * ((z - (x₀ + β * τ)) / (α * τ)
              * heatKernel (α * τ) (z - (x₀ + β * τ)))) ∂volume) τ := by
  change HasDerivAt (fun s ↦ ∫ z, h z * heatKernel (α * s) (z - (x₀ + β * s)) ∂volume) _ τ
  have hατ : (0 : ℝ) < α * τ := by positivity
  have h3ατ : (0 : ℝ) < 3 * (α * τ) := by positivity
  have hd_nn : (0 : ℝ) ≤ |β| * (τ / 2) := by positivity
  set Cexp : ℝ :=
    Real.sqrt 3 * (Real.sqrt 2 * Real.exp ((|β| * (τ / 2) + 1) ^ 2 / (3 * (α * τ)))) with hCexp
  have hCexp_nn : 0 ≤ Cexp := by rw [hCexp]; positivity
  refine hasDerivAt_integral_mul_kernelFamily
    (φ := fun s z ↦ heatKernel (α * s) (z - (x₀ + β * s)))
    (φ' := fun s z ↦ α * (heatKernel (α * s) (z - (x₀ + β * s))
          * ((z - (x₀ + β * s)) ^ 2 - α * s) / (2 * (α * s) ^ 2))
        + β * ((z - (x₀ + β * s)) / (α * s) * heatKernel (α * s) (z - (x₀ + β * s))))
    (p₀ := τ) (r := τ / 2) hhc (by positivity)
    (fun s ↦ (continuous_heatKernel (α * s)).comp (continuous_id.sub continuous_const))
    ((((((continuous_heatKernel (α * τ)).comp (continuous_id.sub continuous_const)).mul
          (((continuous_id.sub continuous_const).pow 2).sub continuous_const)).div_const
          _).const_mul α).add
      ((((continuous_id.sub continuous_const).div_const _).mul
          ((continuous_heatKernel (α * τ)).comp (continuous_id.sub continuous_const))).const_mul β))
    (integrable_payoff_mul_heatKernel hατ hhc hh (x₀ + β * τ))
    (((integrable_exp_mul_poly_heatKernel h3ατ (x₀ + β * τ)
          ((|β| * (τ / 2)) ^ 2 + 3 * (α * τ) / 4)).const_mul (4 * α * Cexp / (α * τ) ^ 2)).add
      ((integrable_exp_mul_poly_heatKernel h3ατ (x₀ + β * τ)
          (1 + |β| * (τ / 2))).const_mul (2 * |β| * Cexp / (α * τ))))
    ?_ ?_
  · -- uniform domination: bound the two terms separately by Gaussian-moment envelopes
    refine ae_of_all _ fun z s hs ↦ ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hs_pos : 0 < s := by linarith [hs.1]
    have hvpos : 0 < α * s := by positivity
    have hvlo : α * τ / 2 < α * s := by nlinarith [mul_pos hα (show (0:ℝ) < s - τ / 2 by linarith)]
    have hvhi : α * s < 3 * (α * τ) / 2 := by
      nlinarith [mul_pos hα (show (0:ℝ) < 3 * τ / 2 - s by linarith)]
    set W : ℝ := z - (x₀ + β * s) with hW
    set W₀ : ℝ := z - (x₀ + β * τ) with hW₀
    have hKnn : 0 ≤ heatKernel (α * s) W := heatKernel_nonneg hvpos _
    have hK0nn : 0 ≤ heatKernel (3 * (α * τ)) W₀ := heatKernel_nonneg h3ατ _
    have hWd : |W - W₀| ≤ |β| * (τ / 2) := by
      rw [hW, hW₀, show z - (x₀ + β * s) - (z - (x₀ + β * τ)) = β * (τ - s) from by ring, abs_mul]
      have : |τ - s| ≤ τ / 2 := by rw [abs_le]; constructor <;> linarith
      exact mul_le_mul_of_nonneg_left this (abs_nonneg β)
    have hcenter : |(x₀ + β * s) - (x₀ + β * τ)| < |β| * (τ / 2) + 1 := by
      rw [show x₀ + β * s - (x₀ + β * τ) = β * (s - τ) from by ring, abs_mul]
      have : |s - τ| < τ / 2 := by rw [abs_lt]; constructor <;> linarith
      nlinarith [mul_le_mul_of_nonneg_left this.le (abs_nonneg β), abs_nonneg β]
    have hk : heatKernel (α * s) W ≤ Cexp * heatKernel (3 * (α * τ)) W₀ := by
      have := heatKernel_loc_le (v₀ := α * τ) (v := α * s) (x := x₀ + β * s) (x₀ := x₀ + β * τ)
        (δ := |β| * (τ / 2) + 1) hατ hvlo hvhi hcenter z
      rwa [← hW, ← hW₀, ← hCexp] at this
    have hrt := curve_sq_ratio_le (v₀ := α * τ) (v := α * s) (W := W) (W₀ := W₀)
      (d := |β| * (τ / 2)) hατ hvlo hvhi hWd hd_nn
    have hrx := curve_abs_ratio_le (v₀ := α * τ) (v := α * s) (W := W) (W₀ := W₀)
      (d := |β| * (τ / 2)) hατ hvlo hWd hd_nn
    -- |φ'| ≤ the two nonneg envelope-ready terms
    have e1 : |α * (heatKernel (α * s) W * (W ^ 2 - α * s) / (2 * (α * s) ^ 2))|
        = α * (heatKernel (α * s) W * (|W ^ 2 - α * s| / (2 * (α * s) ^ 2))) := by
      rw [abs_mul, abs_of_nonneg hα.le, abs_div, abs_mul, abs_of_nonneg hKnn,
        abs_of_nonneg (by positivity : (0:ℝ) ≤ 2 * (α * s) ^ 2), mul_div_assoc]
    have e2 : |β * (W / (α * s) * heatKernel (α * s) W)|
        = |β| * (|W| / (α * s) * heatKernel (α * s) W) := by
      rw [abs_mul, abs_mul, abs_div, abs_of_nonneg hvpos.le, abs_of_nonneg hKnn]
    rw [Real.norm_eq_abs, abs_mul]
    refine (mul_le_mul (hh z) ((abs_add_le _ _).trans_eq (by rw [e1, e2]))
      (abs_nonneg _) (Real.exp_nonneg z)).trans ?_
    rw [mul_add]
    simp only [Pi.add_apply, ← hW₀]
    have hr_t_nn : (0:ℝ) ≤ |W ^ 2 - α * s| / (2 * (α * s) ^ 2) := by positivity
    refine add_le_add ?_ ?_
    · -- α-term ≤ first envelope
      calc Real.exp z * (α * (heatKernel (α * s) W * (|W ^ 2 - α * s| / (2 * (α * s) ^ 2))))
          ≤ Real.exp z * (α * ((Cexp * heatKernel (3 * (α * τ)) W₀)
              * (2 * (2 * W₀ ^ 2 + 2 * (|β| * (τ / 2)) ^ 2 + 3 * (α * τ) / 2) / (α * τ) ^ 2))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul hk hrt hr_t_nn (mul_nonneg hCexp_nn hK0nn)) hα.le)
              (Real.exp_nonneg z)
        _ = 4 * α * Cexp / (α * τ) ^ 2
              * (Real.exp z * ((W₀ ^ 2 + ((|β| * (τ / 2)) ^ 2 + 3 * (α * τ) / 4))
                * heatKernel (3 * (α * τ)) W₀)) := by ring
    · -- β-term ≤ second envelope
      calc Real.exp z * (|β| * (|W| / (α * s) * heatKernel (α * s) W))
          ≤ Real.exp z * (|β| * (2 * (W₀ ^ 2 + 1 + |β| * (τ / 2)) / (α * τ)
              * (Cexp * heatKernel (3 * (α * τ)) W₀))) :=
            mul_le_mul_of_nonneg_left
              (mul_le_mul_of_nonneg_left
                (mul_le_mul hrx hk hKnn (by positivity)) (abs_nonneg β))
              (Real.exp_nonneg z)
        _ = 2 * |β| * Cexp / (α * τ)
              * (Real.exp z * ((W₀ ^ 2 + (1 + |β| * (τ / 2)))
                * heatKernel (3 * (α * τ)) W₀)) := by ring
  · -- pointwise curve derivative
    refine fun z s hs ↦ ?_
    rw [Metric.mem_ball, Real.dist_eq, abs_lt] at hs
    have hs_pos : 0 < s := by linarith [hs.1]
    exact hasDerivAt_heatKernel_comp (v := fun s ↦ α * s) (w := fun s ↦ x₀ + β * s)
      (by simpa using (hasDerivAt_id s).const_mul α)
      (by simpa using ((hasDerivAt_id s).const_mul β).const_add x₀) (by positivity) z

/-- **The Feynman–Kac function solves the heat equation** `∂_t u = ½ ∂_xx u` (the derivative
*values*). Pointwise on the kernel: `K·((z−x)²−t)/(2t²) = ½·K·((z−x)²−t)/t²`. Combined with
`hasDerivAt_feynmanU_t` (`∂_t u = ∫ h·K·((z−x)²−t)/(2t²)`) and `hasDerivAt_feynmanU_xx`
(`∂_xx u = ∫ h·K·((z−x)²−t)/t²`) this is the heat equation for `u = feynmanU h`. Consumed by the
Black–Scholes-PDE keystone `bsV_satisfies_bs_pde_via_feynmanKac` (`sc-bs-pde-feynman-kac`). -/
theorem feynmanU_heat_equation {t : ℝ} (ht : 0 < t) (h : ℝ → ℝ) (x : ℝ) :
    (∫ z, h z * (heatKernel t (z - x) * ((z - x) ^ 2 - t) / (2 * t ^ 2)) ∂volume)
      = (1 / 2) * ∫ z, h z * (heatKernel t (z - x) * ((z - x) ^ 2 - t) / t ^ 2) ∂volume := by
  rw [← integral_const_mul]
  congr 1
  ext z
  rw [heatKernel_t_eq_half_y_y ht (z - x)]
  ring

end FeynmanKacHeatEquation
end MathFin
