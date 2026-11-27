/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Differences.Differences
public import LeanPool.FunctionSpaces.Analysis.Fourier.LittlewoodPaleyKernels
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Cascade
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.TransferExamples

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Sobolev regularity of the scaling function

For a Daubechies mask of order `N ≥ 2` with symbol product `Φ` (`Daubechies.symbolProduct`) and
scaling function `φ = 𝓕⁻ Φ` (`Daubechies.scalingFun`), this file bounds the moduli of smoothness
`ω_r(φ, t)_p = sup_{|h| ≤ t} ‖Δ_h^r φ‖_p` (`Rd.modulus`) for `p ≤ 2`. Here
`Δ_h f(x) = f(x + h) - f(x)` is the forward difference (Mathlib's `fwdDiff h f`) and `Δ_h^r` its
`r`-fold iterate, written `(fwdDiff h)^[r]`. Under a growth bound `T^n 1 ≤ C λ^n` for the transfer
operator `T` (`Daubechies.TransferGrowth N λ C`), for every real `s` with `0 ≤ s < N - log₄ λ` and
every order `r ∈ ℕ` with `r ≥ s` there is a finite constant `K` with

`ω_r(φ, t)_2 ≤ K t^s` for `0 < t ≤ 1` (`Daubechies.modulus_scalingFun_two_le`),

and the same holds in `L_p` for every `p ≤ 2` (`Daubechies.modulus_scalingFun_le_two`). As `s` may
be any number in `[0, N - log₄ λ)`, these bounds express the Sobolev regularity `φ ∈ H^s` for every
`s < N - log₄ λ` by moduli of smoothness (the bound for `s` says `φ ∈ B^s_{2,∞}`, and
`B^s_{2,∞} ⊂ H^(s')` for `s' < s`).

* **The Fourier transform of a difference.** For integrable `f : ℝ → ℂ`,
  `𝓕 (Δ_h f)(ξ) = (e^(2πihξ) - 1) 𝓕 f(ξ)` by linearity and the translation rule
  (`Real.fourier_fwdDiff_apply`), hence `𝓕 (Δ_h^r f)(ξ) = (e^(2πihξ) - 1)^r 𝓕 f(ξ)`
  (`Real.fourier_iterate_fwdDiff_apply`).
* **The multiplier.** The elementary bounds `|e^(iθ) - 1| ≤ 2` and `|e^(iθ) - 1| ≤ |θ|` for real
  `θ` give `|e^(2πihξ) - 1| ≤ 2π min(1, |hξ|)` (`Daubechies.norm_exp_sub_one_le_min`). Since
  `min(1, x)^r ≤ x^a` for `x ≥ 0` and `0 ≤ a ≤ r` (`Daubechies.min_one_rpow_le_rpow`), the
  power form is `|e^(2πihξ) - 1|^r ≤ (2π)^r |h|^a (1 + |ξ|)^a` for all `h, ξ ∈ ℝ`
  (`Daubechies.norm_exp_sub_one_pow_le_mul_rpow`), used here with the exponents `2s ≤ 2r`
  (`Daubechies.norm_exp_sub_one_pow_le`). The factor is bounded by `2^r`, so
  `(e^(2πihξ) - 1)^r F(ξ)` is integrable with `F` (`Real.integrable_exp_sub_one_pow_mul`).
* **Parseval's identity for the differences of `φ`.** The scaling function is continuous and
  integrable with `𝓕 φ = Φ`, so `Δ_h^r φ` is continuous and integrable with the integrable
  transform `(e^(2πihξ) - 1)^r Φ(ξ)` (`Daubechies.fourier_higherDiff_scalingFun`,
  `Daubechies.integrable_fourier_higherDiff_scalingFun`). Plancherel's identity
  (`Real.integral_norm_sq_fourier`) gives `‖Δ_h^r φ‖_2² = ∫ |e^(2πihξ) - 1|^(2r) |Φ(ξ)|² dξ`
  (`Daubechies.integral_norm_sq_higherDiff_scalingFun`,
  `Daubechies.eLpNorm_two_higherDiff_scalingFun_sq`).
* **The `L²` modulus.** With the power form of the multiplier bound,
  `‖Δ_h^r φ‖_2 ≤ (2π)^r (∫ (1 + |ξ|)^(2s) |Φ(ξ)|² dξ)^(1/2) |h|^s`
  (`Daubechies.eLpNorm_two_higherDiff_scalingFun_le`), where the integral is finite for
  `s < N - log₄ λ` (`Daubechies.integrable_rpow_mul_normSq`). The supremum over `|h| ≤ t` bounds
  `ω_r(φ, t)_2` (`Daubechies.modulus_scalingFun_two_le_mul_rpow`).
* **Exponents `p ≤ 2`.** For `|h| ≤ 1` the difference `Δ_h^r φ` vanishes outside
  `[-r, 2N - 1 + r]` (`Daubechies.higherDiff_scalingFun_eq_zero`), since `φ` vanishes outside
  `[0, 2N - 1]`. Hölder's inequality on this interval of length `2N - 1 + 2r`
  (`Daubechies.eLpNorm_le_eLpNorm_mul_of_eq_zero`) gives
  `ω_r(φ, t)_p ≤ (2N - 1 + 2r)^(1/p - 1/2) ω_r(φ, t)_2` for `t ≤ 1`
  (`Daubechies.modulus_scalingFun_le_modulus_two`).
* **Orders two and three.** The growth bounds `T^n 1 ≤ 4^n` for `N = 2` and `T^n 1 ≤ 2 · 9^n` for
  `N = 3` (`Daubechies.transferGrowth_two`, `Daubechies.transferGrowth_three`) have the exponents
  `2 - log₄ 4 = 1` and `3 - log₄ 9 = 3 - log₂ 3 ≈ 1.415`. Hence `ω_r(φ, t)_p ≤ K t^s` for
  `p ≤ 2` and `0 < t ≤ 1`, for every `0 ≤ s < 1` if `N = 2`
  (`Daubechies.modulus_scalingFun_two_le_order_two`,
  `Daubechies.modulus_scalingFun_le_two_order_two`) and for every `0 ≤ s < 3 - log₂ 3` if
  `N = 3` (`Daubechies.modulus_scalingFun_two_le_order_three`,
  `Daubechies.modulus_scalingFun_le_two_order_three`).
-/

@[expose] public section

open MeasureTheory Complex
open scoped Real FourierTransform ENNReal

namespace Real

/-! ### The Fourier transform of a difference -/

variable {f : ℝ → ℂ}

/-- **The Fourier transform of a difference**: for integrable `f : ℝ → ℂ` and all `h, ξ ∈ ℝ`,
`𝓕 (Δ_h f)(ξ) = (e^(2πihξ) - 1) 𝓕 f(ξ)`, where `Δ_h f(x) = f(x + h) - f(x)` is Mathlib's
`fwdDiff h f`. The transform is linear on integrable functions (`Rd.fourier_sub_apply`), and
translation becomes modulation, `𝓕[f(· + h)](ξ) = e^(2πihξ) 𝓕 f(ξ)`
(`Real.fourier_comp_add_right_apply`). -/
theorem fourier_fwdDiff_apply (hf : Integrable f) (h ξ : ℝ) :
    𝓕 (fwdDiff h f) ξ = (cexp (2 * π * h * ξ * I) - 1) * 𝓕 f ξ := by
  rw [show fwdDiff h f = (fun x => f (x + h)) - f from rfl,
    Rd.fourier_sub_apply (hf.comp_add_right h) hf, fourier_comp_add_right_apply, sub_one_mul]

/-- **The Fourier transform of a difference of order `r`**: for integrable `f : ℝ → ℂ`,
`𝓕 (Δ_h^r f)(ξ) = (e^(2πihξ) - 1)^r 𝓕 f(ξ)` for every `r ∈ ℕ` and all `h, ξ ∈ ℝ`, where
`Δ_h^r f = (fwdDiff h)^[r] f` is the `r`-fold iterate of the difference. By induction on `r` with
`Real.fourier_fwdDiff_apply`, since every difference of an integrable function is integrable
(`Rd.integrable_higherDiff`). -/
theorem fourier_iterate_fwdDiff_apply (hf : Integrable f) (r : ℕ) (h ξ : ℝ) :
    𝓕 ((fwdDiff h)^[r] f) ξ = (cexp (2 * π * h * ξ * I) - 1) ^ r * 𝓕 f ξ := by
  induction r with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', fourier_fwdDiff_apply (Rd.integrable_higherDiff hf r h),
      ih, pow_succ']
    ring

end Real

namespace Daubechies

/-! ### The multiplier of a difference -/

/-- `e^(2πihξ) = e^(iθ)` with the real number `θ = 2πhξ`. This is the form `exp(iθ)`, `θ` real, in
which Mathlib states `|e^(iθ)| = 1` and `|e^(iθ) - 1| ≤ |θ|` (`Complex.norm_exp_ofReal_mul_I`,
`Real.norm_exp_I_mul_ofReal_sub_one_le`). -/
theorem exp_two_pi_mul_I_eq (h ξ : ℝ) :
    cexp (2 * π * h * ξ * I) = cexp (I * ((2 * π * (h * ξ) : ℝ) : ℂ)) := by
  congr 1
  push_cast
  ring

/-- `|e^(2πihξ) - 1| ≤ 2` for all `h, ξ ∈ ℝ`, by the triangle inequality and `|e^(iθ)| = 1` for
real `θ` (Mathlib's `Complex.norm_exp_ofReal_mul_I`). -/
theorem norm_exp_sub_one_le_two (h ξ : ℝ) : ‖cexp (2 * π * h * ξ * I) - 1‖ ≤ 2 := by
  calc ‖cexp (2 * π * h * ξ * I) - 1‖ ≤ ‖cexp (2 * π * h * ξ * I)‖ + ‖(1 : ℂ)‖ :=
        norm_sub_le _ _
    _ = 2 := by
        rw [exp_two_pi_mul_I_eq, mul_comm, Complex.norm_exp_ofReal_mul_I, norm_one]
        norm_num

/-- **The multiplier of a difference**: `|e^(2πihξ) - 1| ≤ 2π min(1, |hξ|)` for all `h, ξ ∈ ℝ`.
It combines `|e^(iθ) - 1| ≤ 2 ≤ 2π` (`Daubechies.norm_exp_sub_one_le_two`) with
`|e^(iθ) - 1| ≤ |θ|` for `θ = 2πhξ` (Mathlib's `Real.norm_exp_I_mul_ofReal_sub_one_le`). -/
theorem norm_exp_sub_one_le_min (h ξ : ℝ) :
    ‖cexp (2 * π * h * ξ * I) - 1‖ ≤ 2 * π * min 1 |h * ξ| := by
  rw [mul_min_of_nonneg _ _ (by positivity), mul_one]
  refine le_min ((norm_exp_sub_one_le_two h ξ).trans (by linarith [Real.two_le_pi])) ?_
  rw [exp_two_pi_mul_I_eq]
  refine Real.norm_exp_I_mul_ofReal_sub_one_le.trans_eq ?_
  rw [Real.norm_eq_abs, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 2 * π)]

/-- `min(1, x)^b ≤ x^a` for `x ≥ 0` and real exponents `0 ≤ a ≤ b`. For `x ≤ 1` the power `x^t`
decreases in `t`, so `x^b ≤ x^a` (Mathlib's `Real.rpow_le_rpow_of_exponent_ge'`); for `x ≥ 1`
the left side is `1 ≤ x^a` (Mathlib's `Real.one_le_rpow`). -/
theorem min_one_rpow_le_rpow {x a b : ℝ} (hx : 0 ≤ x) (ha : 0 ≤ a) (hab : a ≤ b) :
    min 1 x ^ b ≤ x ^ a := by
  rcases le_total x 1 with hx1 | hx1
  · rw [min_eq_right hx1]
    exact Real.rpow_le_rpow_of_exponent_ge' hx hx1 ha hab
  · rw [min_eq_left hx1, Real.one_rpow]
    exact Real.one_le_rpow hx1 ha

/-- **The multiplier bound in power form**: for real `a` and `r ∈ ℕ` with `0 ≤ a ≤ r`,
`|e^(2πihξ) - 1|^r ≤ (2π)^r |h|^a (1 + |ξ|)^a` for all `h, ξ ∈ ℝ`. It follows from
`|e^(2πihξ) - 1| ≤ 2π min(1, |hξ|)` (`Daubechies.norm_exp_sub_one_le_min`),
`min(1, |hξ|)^r ≤ |hξ|^a` (`Daubechies.min_one_rpow_le_rpow`) and `|ξ| ≤ 1 + |ξ|`. The bound holds
for every step `h`, small or large; its squared form, with the exponents `2r` and `2a`, is
`Daubechies.norm_exp_sub_one_pow_le`. -/
theorem norm_exp_sub_one_pow_le_mul_rpow {a : ℝ} {r : ℕ} (ha0 : 0 ≤ a) (har : a ≤ r)
    (h ξ : ℝ) :
    ‖cexp (2 * π * h * ξ * I) - 1‖ ^ r ≤ (2 * π) ^ r * (|h| ^ a * (1 + |ξ|) ^ a) := by
  have h1 : min 1 |h * ξ| ^ r ≤ |h * ξ| ^ a := by
    have := min_one_rpow_le_rpow (abs_nonneg (h * ξ)) ha0 har
    rwa [Real.rpow_natCast] at this
  have h2 : |h * ξ| ^ a ≤ |h| ^ a * (1 + |ξ|) ^ a := by
    rw [abs_mul, Real.mul_rpow (abs_nonneg _) (abs_nonneg _)]
    exact mul_le_mul_of_nonneg_left
      (Real.rpow_le_rpow (abs_nonneg _) (by linarith) ha0) (by positivity)
  calc ‖cexp (2 * π * h * ξ * I) - 1‖ ^ r ≤ (2 * π * min 1 |h * ξ|) ^ r :=
        pow_le_pow_left₀ (norm_nonneg _) (norm_exp_sub_one_le_min h ξ) _
    _ = (2 * π) ^ r * min 1 |h * ξ| ^ r := mul_pow _ _ _
    _ ≤ _ := mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)

/-- **The power form of the multiplier bound**: for real `s` and `r ∈ ℕ` with `0 ≤ s ≤ r`,
`|e^(2πihξ) - 1|^(2r) ≤ (2π)^(2r) |h|^(2s) (1 + |ξ|)^(2s)` for all `h, ξ ∈ ℝ`: the case of the
exponents `2s ≤ 2r` of `Daubechies.norm_exp_sub_one_pow_le_mul_rpow`. The exponent `s` trades the
factor `|h|^(2s)` for the weight `(1 + |ξ|)^(2s)` on the Fourier side. -/
theorem norm_exp_sub_one_pow_le {s : ℝ} {r : ℕ} (hs0 : 0 ≤ s) (hsr : s ≤ r) (h ξ : ℝ) :
    ‖cexp (2 * π * h * ξ * I) - 1‖ ^ (2 * r) ≤
      (2 * π) ^ (2 * r) * (|h| ^ (2 * s) * (1 + |ξ|) ^ (2 * s)) :=
  norm_exp_sub_one_pow_le_mul_rpow (by linarith) (by push_cast; linarith) h ξ

end Daubechies

namespace Real

/-- For integrable `F : ℝ → ℂ`, every `r ∈ ℕ` and every `h ∈ ℝ`, the function
`ξ ↦ (e^(2πihξ) - 1)^r F(ξ)` is integrable: the continuous factor is bounded by `2^r`
(`Daubechies.norm_exp_sub_one_le_two`, Mathlib's `MeasureTheory.Integrable.bdd_mul`). -/
theorem integrable_exp_sub_one_pow_mul {F : ℝ → ℂ} (hF : Integrable F) (r : ℕ)
    (h : ℝ) : Integrable (fun ξ : ℝ => (cexp (2 * π * h * ξ * I) - 1) ^ r * F ξ) := by
  refine hF.bdd_mul (c := 2 ^ r)
    (by fun_prop : Continuous fun ξ : ℝ => (cexp (2 * π * h * ξ * I) - 1) ^ r).aestronglyMeasurable
    (Filter.Eventually.of_forall fun ξ => ?_)
  rw [norm_pow]
  exact pow_le_pow_left₀ (norm_nonneg _) (Daubechies.norm_exp_sub_one_le_two h ξ) r

end Real

namespace Daubechies

/-! ### Continuity and `L_p` norms of differences -/

/-- The differences `Δ_h^r f` of a continuous `f : ℝ → ℂ` are continuous, for every `r ∈ ℕ` and
every `h ∈ ℝ`: by induction on `r`, since `Δ_h g = g(· + h) - g`. -/
theorem continuous_iterate_fwdDiff {f : ℝ → ℂ} (hf : Continuous f) (r : ℕ) (h : ℝ) :
    Continuous ((fwdDiff h)^[r] f) := by
  induction r with
  | zero => exact hf
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    exact (ih.comp (continuous_id.add continuous_const)).sub ih

/-- The differences of a function in `L_p(ℝ)`, `p ≥ 1`, lie in `L_p(ℝ)`: `Δ_h^r f ∈ L_p` for
every `r ∈ ℕ` and every `h ∈ ℝ`, since `‖Δ_h^r f‖_p ≤ 2^r ‖f‖_p` (`Rd.eLpNorm_higherDiff_le`). -/
theorem memLp_iterate_fwdDiff {f : ℝ → ℂ} {p : ℝ≥0∞} (hf : MemLp f p) (hp : 1 ≤ p) (r : ℕ)
    (h : ℝ) : MemLp ((fwdDiff h)^[r] f) p :=
  (Rd.eLpNorm_higherDiff_le hf.aestronglyMeasurable hp r h).trans_lt
    (ENNReal.mul_lt_top (by simp) hf)

/-- **The `L²` norm as an integral**: `‖g‖_2 = (∫ ‖g(x)‖² dμ(x))^(1/2)` for every `g ∈ L²(μ)`
with values in a normed group, on every measure space. The left side is Mathlib's
`eLpNorm g 2 μ ∈ [0, ∞]`, the right side the real square root, embedded by `ENNReal.ofReal`
(Mathlib's `MeasureTheory.MemLp.eLpNorm_eq_integral_rpow_norm`). -/
theorem eLpNorm_two_eq_sqrt_integral {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {g : α → E} (hg : MemLp g 2 μ) :
    eLpNorm g 2 μ = ENNReal.ofReal √(∫ x, ‖g x‖ ^ 2 ∂μ) := by
  rw [hg.eLpNorm_eq_integral_rpow_norm two_ne_zero ENNReal.ofNat_ne_top, ENNReal.toReal_ofNat,
    Real.sqrt_eq_rpow, one_div]
  simp_rw [Real.rpow_two]

/-! ### Parseval's identity for the differences of the scaling function -/

variable {N : ℕ} (m : Mask N)

/-- **The Fourier transform of the differences of the scaling function**: for `N ≥ 2`,
`𝓕 (Δ_h^r φ)(ξ) = (e^(2πihξ) - 1)^r Φ(ξ)` for every `r ∈ ℕ` and all `h, ξ ∈ ℝ`. This is
`Real.fourier_iterate_fwdDiff_apply` for the integrable function `φ`
(`Daubechies.integrable_scalingFun`) together with `𝓕 φ = Φ` (`Daubechies.fourier_scalingFun`). -/
theorem fourier_higherDiff_scalingFun (hN : 2 ≤ N) (r : ℕ) (h ξ : ℝ) :
    𝓕 ((fwdDiff h)^[r] (scalingFun m)) ξ =
      (cexp (2 * π * h * ξ * I) - 1) ^ r * symbolProduct m ξ := by
  rw [Real.fourier_iterate_fwdDiff_apply (integrable_scalingFun m hN), fourier_scalingFun m hN]

/-- For `N ≥ 2` the Fourier transform `ξ ↦ (e^(2πihξ) - 1)^r Φ(ξ)` of `Δ_h^r φ`
(`Daubechies.fourier_higherDiff_scalingFun`) is integrable: `Φ` is integrable
(`Daubechies.integrable_symbolProduct`, `Real.integrable_exp_sub_one_pow_mul`). -/
theorem integrable_fourier_higherDiff_scalingFun (hN : 2 ≤ N) (r : ℕ) (h : ℝ) :
    Integrable (𝓕 ((fwdDiff h)^[r] (scalingFun m))) := by
  rw [funext (fourier_higherDiff_scalingFun m hN r h)]
  exact Real.integrable_exp_sub_one_pow_mul (integrable_symbolProduct m hN) r h

/-- **Parseval's identity for the differences of the scaling function**: for `N ≥ 2`,
`∫ |Δ_h^r φ(x)|² dx = ∫ |e^(2πihξ) - 1|^(2r) |Φ(ξ)|² dξ` for every `r ∈ ℕ` and every `h ∈ ℝ`.
The function `Δ_h^r φ` is continuous and integrable (`Daubechies.continuous_iterate_fwdDiff`,
`Rd.integrable_higherDiff`) and has an integrable transform
(`Daubechies.integrable_fourier_higherDiff_scalingFun`), so Plancherel's identity
`Real.integral_norm_sq_fourier` applies; the transform is given by
`Daubechies.fourier_higherDiff_scalingFun`. -/
theorem integral_norm_sq_higherDiff_scalingFun (hN : 2 ≤ N) (r : ℕ) (h : ℝ) :
    ∫ x, ‖(fwdDiff h)^[r] (scalingFun m) x‖ ^ 2 =
      ∫ ξ : ℝ, ‖cexp (2 * π * h * ξ * I) - 1‖ ^ (2 * r) * ‖symbolProduct m ξ‖ ^ 2 := by
  rw [← Real.integral_norm_sq_fourier
    (continuous_iterate_fwdDiff (continuous_scalingFun m hN) r h)
    (Rd.integrable_higherDiff (integrable_scalingFun m hN) r h)
    (integrable_fourier_higherDiff_scalingFun m hN r h)]
  congr 1 with ξ
  rw [fourier_higherDiff_scalingFun m hN, norm_mul, norm_pow, mul_pow, ← pow_mul, mul_comm r 2]

/-- For `N ≥ 2` the differences `Δ_h^r φ` of the scaling function lie in `L_p(ℝ)` for every
`p ≥ 1`, since `φ` does (`Daubechies.memLp_scalingFun`, `Daubechies.memLp_iterate_fwdDiff`). -/
theorem memLp_higherDiff_scalingFun (hN : 2 ≤ N) {p : ℝ≥0∞} (hp : 1 ≤ p) (r : ℕ) (h : ℝ) :
    MemLp ((fwdDiff h)^[r] (scalingFun m)) p :=
  memLp_iterate_fwdDiff (memLp_scalingFun m hN p) hp r h

/-- **The `L²` norm of the differences on the Fourier side**: for `N ≥ 2`,
`‖Δ_h^r φ‖_2² = ∫ |e^(2πihξ) - 1|^(2r) |Φ(ξ)|² dξ` for every `r ∈ ℕ` and every `h ∈ ℝ`, as an
identity in `[0, ∞]`. This is Parseval's identity
`Daubechies.integral_norm_sq_higherDiff_scalingFun` together with `‖g‖_2 = (∫ ‖g‖²)^(1/2)`
(`Daubechies.eLpNorm_two_eq_sqrt_integral`). -/
theorem eLpNorm_two_higherDiff_scalingFun_sq (hN : 2 ≤ N) (r : ℕ) (h : ℝ) :
    eLpNorm ((fwdDiff h)^[r] (scalingFun m)) 2 volume ^ 2 =
      ENNReal.ofReal
        (∫ ξ : ℝ, ‖cexp (2 * π * h * ξ * I) - 1‖ ^ (2 * r) * ‖symbolProduct m ξ‖ ^ 2) := by
  rw [eLpNorm_two_eq_sqrt_integral (memLp_higherDiff_scalingFun m hN one_le_two r h),
    ← ENNReal.ofReal_pow (Real.sqrt_nonneg _),
    Real.sq_sqrt (integral_nonneg fun x => sq_nonneg _),
    integral_norm_sq_higherDiff_scalingFun m hN]

/-! ### The `L²` modulus of the scaling function -/

/-- `x^(2s) = (x^s)²` for `x ≥ 0` and every real `s` (Mathlib's `Real.rpow_mul`). -/
theorem rpow_two_mul_eq_sq {x : ℝ} (hx : 0 ≤ x) (s : ℝ) : x ^ (2 * s) = (x ^ s) ^ 2 := by
  rw [mul_comm, Real.rpow_mul hx, Real.rpow_two]

/-- **The squared `L²` bound for the differences of the scaling function**: let `N ≥ 2`, let
`T^n 1 ≤ C λ^n` be a growth bound for the transfer operator (`Daubechies.TransferGrowth`), and
let `s ∈ ℝ`, `r ∈ ℕ` with `0 ≤ s ≤ r` and `s < N - log₄ λ`. Then for every `h ∈ ℝ`,
`∫ |Δ_h^r φ(x)|² dx ≤ ((2π)^r |h|^s)² ∫ (1 + |ξ|)^(2s) |Φ(ξ)|² dξ`.
Parseval's identity (`Daubechies.integral_norm_sq_higherDiff_scalingFun`) and the pointwise bound
`Daubechies.norm_exp_sub_one_pow_le` give the estimate. The condition `s < N - log₄ λ` makes the
integrand on the right integrable (`Daubechies.integrable_rpow_mul_normSq`), which the comparison
of the integrals needs. -/
theorem integral_norm_sq_higherDiff_scalingFun_le (hN : 2 ≤ N) {lam C s : ℝ} {r : ℕ}
    (hg : TransferGrowth N lam C) (hs0 : 0 ≤ s) (hs : s < N - Real.logb 4 lam) (hsr : s ≤ r)
    (h : ℝ) :
    ∫ x, ‖(fwdDiff h)^[r] (scalingFun m) x‖ ^ 2 ≤
      ((2 * π) ^ r * |h| ^ s) ^ 2 * ∫ ξ, (1 + |ξ|) ^ (2 * s) * ‖symbolProduct m ξ‖ ^ 2 := by
  rw [integral_norm_sq_higherDiff_scalingFun m hN, ← integral_const_mul]
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun ξ => by positivity)
    ((integrable_rpow_mul_normSq m hg hs).const_mul _) (Filter.Eventually.of_forall fun ξ => ?_)
  calc ‖cexp (2 * π * h * ξ * I) - 1‖ ^ (2 * r) * ‖symbolProduct m ξ‖ ^ 2
      ≤ (2 * π) ^ (2 * r) * (|h| ^ (2 * s) * (1 + |ξ|) ^ (2 * s)) * ‖symbolProduct m ξ‖ ^ 2 :=
        mul_le_mul_of_nonneg_right (norm_exp_sub_one_pow_le hs0 hsr h ξ) (by positivity)
    _ = ((2 * π) ^ r * |h| ^ s) ^ 2 * ((1 + |ξ|) ^ (2 * s) * ‖symbolProduct m ξ‖ ^ 2) := by
        rw [rpow_two_mul_eq_sq (abs_nonneg h), pow_mul']
        ring

/-- **The `L²` bound for the differences of the scaling function**: under the hypotheses of
`Daubechies.integral_norm_sq_higherDiff_scalingFun_le`, for every `h ∈ ℝ`,
`‖Δ_h^r φ‖_2 ≤ (2π)^r (∫ (1 + |ξ|)^(2s) |Φ(ξ)|² dξ)^(1/2) |h|^s`, the square root of that bound
(`Daubechies.eLpNorm_two_eq_sqrt_integral`). -/
theorem eLpNorm_two_higherDiff_scalingFun_le (hN : 2 ≤ N) {lam C s : ℝ} {r : ℕ}
    (hg : TransferGrowth N lam C) (hs0 : 0 ≤ s) (hs : s < N - Real.logb 4 lam) (hsr : s ≤ r)
    (h : ℝ) :
    eLpNorm ((fwdDiff h)^[r] (scalingFun m)) 2 volume ≤
      ENNReal.ofReal ((2 * π) ^ r * √(∫ ξ, (1 + |ξ|) ^ (2 * s) * ‖symbolProduct m ξ‖ ^ 2)) *
        ENNReal.ofReal (|h| ^ s) := by
  rw [eLpNorm_two_eq_sqrt_integral (memLp_higherDiff_scalingFun m hN one_le_two r h),
    ← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ((Real.sqrt_le_sqrt
    (integral_norm_sq_higherDiff_scalingFun_le m hN hg hs0 hs hsr h)).trans_eq ?_)
  rw [Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (by positivity)]
  ring

/-- **The `L²` modulus of the scaling function, with an explicit constant**: under the hypotheses
of `Daubechies.integral_norm_sq_higherDiff_scalingFun_le`, for every `t ∈ ℝ`,
`ω_r(φ, t)_2 ≤ (2π)^r (∫ (1 + |ξ|)^(2s) |Φ(ξ)|² dξ)^(1/2) t^s`. This is the supremum over
`|h| ≤ t` of `Daubechies.eLpNorm_two_higherDiff_scalingFun_le`, with `|h|^s ≤ t^s` since
`s ≥ 0`. -/
theorem modulus_scalingFun_two_le_mul_rpow (hN : 2 ≤ N) {lam C s : ℝ} {r : ℕ}
    (hg : TransferGrowth N lam C) (hs0 : 0 ≤ s) (hs : s < N - Real.logb 4 lam) (hsr : s ≤ r)
    (t : ℝ) :
    Rd.modulus volume r 2 (scalingFun m) t ≤
      ENNReal.ofReal ((2 * π) ^ r * √(∫ ξ, (1 + |ξ|) ^ (2 * s) * ‖symbolProduct m ξ‖ ^ 2)) *
        ENNReal.ofReal (t ^ s) := by
  refine iSup₂_le fun h hh => (eLpNorm_two_higherDiff_scalingFun_le m hN hg hs0 hs hsr h).trans ?_
  gcongr
  exact hh

/-- **The `L²` modulus of smoothness of the scaling function**: let `N ≥ 2` and let
`T^n 1 ≤ C λ^n` be a growth bound for the transfer operator (`Daubechies.TransferGrowth`). For
every real `s` with `0 ≤ s < N - log₄ λ` and every order `r ∈ ℕ` with `r ≥ s` there is a finite
constant `K` with `ω_r(φ, t)_2 ≤ K t^s` for all `0 < t ≤ 1`
(`Daubechies.modulus_scalingFun_two_le_mul_rpow`). Over all such `s`, this is the Sobolev
regularity `φ ∈ H^s` for every `s < N - log₄ λ`, in terms of moduli of smoothness. -/
theorem modulus_scalingFun_two_le (hN : 2 ≤ N) {lam C s : ℝ} {r : ℕ}
    (hg : TransferGrowth N lam C) (hs0 : 0 ≤ s) (hs : s < N - Real.logb 4 lam) (hsr : s ≤ r) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r 2 (scalingFun m) t ≤ K * ENNReal.ofReal (t ^ s) :=
  ⟨_, ENNReal.ofReal_ne_top, fun t _ => modulus_scalingFun_two_le_mul_rpow m hN hg hs0 hs hsr t⟩

/-! ### Exponents `p ≤ 2` -/

/-- **The support of a difference**: if `f : ℝ → ℂ` vanishes outside `[a, b]`, then `Δ_h^r f`
vanishes outside `[a - r|h|, b + r|h|]`, for every `r ∈ ℕ` and every `h ∈ ℝ`. By induction on
`r`: `Δ_h^(r+1) f(x) = Δ_h^r f(x + h) - Δ_h^r f(x)`, and for `x` outside
`[a - (r+1)|h|, b + (r+1)|h|]` both `x` and `x + h` lie outside `[a - r|h|, b + r|h|]`. -/
theorem iterate_fwdDiff_eq_zero_of_notMem {f : ℝ → ℂ} {a b : ℝ}
    (hf : ∀ x ∉ Set.Icc a b, f x = 0) (r : ℕ) (h : ℝ) {x : ℝ}
    (hx : x ∉ Set.Icc (a - r * |h|) (b + r * |h|)) : (fwdDiff h)^[r] f x = 0 := by
  induction r generalizing x with
  | zero =>
    rw [Nat.cast_zero, zero_mul, sub_zero, add_zero] at hx
    exact hf x hx
  | succ r ih =>
    have hh := abs_nonneg h
    rw [Function.iterate_succ_apply']
    change (fwdDiff h)^[r] f (x + h) - (fwdDiff h)^[r] f x = 0
    rw [ih fun hmem => ?_, ih fun hmem => ?_, sub_zero]
    · refine hx ⟨?_, ?_⟩ <;> push_cast <;> linarith [hmem.1, hmem.2]
    · refine hx ⟨?_, ?_⟩ <;> push_cast <;> linarith [hmem.1, hmem.2, neg_abs_le h, le_abs_self h]

/-- **Hölder's inequality for a function supported in an interval**: if `g : ℝ → E` is almost
everywhere strongly measurable and vanishes outside `[a, b]`, then
`‖g‖_p ≤ ‖g‖_q (b - a)^(1/p - 1/q)` for exponents `p ≤ q` in `[0, ∞]`, where `1/p` stands for
`1 / p.toReal` (so `1/∞ = 0`). Both norms are the norms for Lebesgue measure restricted to
`[a, b]` (Mathlib's `MeasureTheory.eLpNorm_restrict_eq_of_support_subset`), and on this finite
measure space the comparison of `L_p` norms
(Mathlib's `MeasureTheory.eLpNorm_le_eLpNorm_mul_rpow_measure_univ`) gives the factor
`|[a, b]|^(1/p - 1/q)`. -/
theorem eLpNorm_le_eLpNorm_mul_of_eq_zero {E : Type*} [NormedAddCommGroup E] {g : ℝ → E}
    (hg : AEStronglyMeasurable g) {a b : ℝ} (hab : ∀ x ∉ Set.Icc a b, g x = 0) {p q : ℝ≥0∞}
    (hpq : p ≤ q) :
    eLpNorm g p volume ≤
      eLpNorm g q volume * ENNReal.ofReal (b - a) ^ (1 / p.toReal - 1 / q.toReal) := by
  have hsupp : Function.support g ⊆ Set.Icc a b := fun x hx => by_contra fun h => hx (hab x h)
  rw [← eLpNorm_restrict_eq_of_support_subset hg hsupp,
    ← eLpNorm_restrict_eq_of_support_subset (p := q) hg hsupp]
  refine (eLpNorm_le_eLpNorm_mul_rpow_measure_univ hpq hg.restrict).trans_eq ?_
  rw [Measure.restrict_apply_univ, Real.volume_Icc]

/-- **The support of the differences of the scaling function**: for `N ≥ 2`, `r ∈ ℕ` and a step
`|h| ≤ 1`, `Δ_h^r φ(x) = 0` for every `x ∉ [-r, 2N - 1 + r]`. The scaling function vanishes
outside `[0, 2N - 1]` (`Daubechies.scalingFun_eq_zero`), so `Δ_h^r φ` vanishes outside
`[-r|h|, 2N - 1 + r|h|] ⊆ [-r, 2N - 1 + r]` (`Daubechies.iterate_fwdDiff_eq_zero_of_notMem`). -/
theorem higherDiff_scalingFun_eq_zero (hN : 2 ≤ N) (r : ℕ) {h : ℝ} (hh : |h| ≤ 1) {x : ℝ}
    (hx : x ∉ Set.Icc (-(r : ℝ)) (2 * N - 1 + r)) : (fwdDiff h)^[r] (scalingFun m) x = 0 := by
  have hr : (r : ℝ) * |h| ≤ r := mul_le_of_le_one_right r.cast_nonneg hh
  refine iterate_fwdDiff_eq_zero_of_notMem (fun y hy => scalingFun_eq_zero m hN hy) r h
    fun hmem => hx ⟨?_, ?_⟩
  · linarith [hmem.1]
  · linarith [hmem.2]

/-- **`L_p` norms of the differences by the `L²` norm**: for `N ≥ 2`, `p ≤ 2`, `r ∈ ℕ` and a
step `|h| ≤ 1`, `‖Δ_h^r φ‖_p ≤ ‖Δ_h^r φ‖_2 (2N - 1 + 2r)^(1/p - 1/2)`. The difference vanishes
outside the interval `[-r, 2N - 1 + r]` of length `2N - 1 + 2r`
(`Daubechies.higherDiff_scalingFun_eq_zero`), and Hölder's inequality on this interval gives the
factor (`Daubechies.eLpNorm_le_eLpNorm_mul_of_eq_zero`). -/
theorem eLpNorm_higherDiff_scalingFun_le_two (hN : 2 ≤ N) {p : ℝ≥0∞} (hp2 : p ≤ 2) (r : ℕ)
    {h : ℝ} (hh : |h| ≤ 1) :
    eLpNorm ((fwdDiff h)^[r] (scalingFun m)) p volume ≤
      eLpNorm ((fwdDiff h)^[r] (scalingFun m)) 2 volume *
        ENNReal.ofReal (2 * N - 1 + 2 * r) ^ (1 / p.toReal - 1 / 2) := by
  have h1 := eLpNorm_le_eLpNorm_mul_of_eq_zero
    (memLp_higherDiff_scalingFun m hN one_le_two r h).aestronglyMeasurable
    (fun x hx => higherDiff_scalingFun_eq_zero m hN r hh hx) hp2
  rwa [ENNReal.toReal_ofNat, show (2 * N - 1 + r : ℝ) - -r = 2 * N - 1 + 2 * r by ring] at h1

/-- **The `L_p` modulus by the `L²` modulus**: for `N ≥ 2`, `p ≤ 2`, `r ∈ ℕ` and `t ≤ 1`,
`ω_r(φ, t)_p ≤ (2N - 1 + 2r)^(1/p - 1/2) ω_r(φ, t)_2`, the supremum over `|h| ≤ t` of
`Daubechies.eLpNorm_higherDiff_scalingFun_le_two`. -/
theorem modulus_scalingFun_le_modulus_two (hN : 2 ≤ N) {p : ℝ≥0∞} (hp2 : p ≤ 2) (r : ℕ) {t : ℝ}
    (ht : t ≤ 1) :
    Rd.modulus volume r p (scalingFun m) t ≤
      ENNReal.ofReal (2 * N - 1 + 2 * r) ^ (1 / p.toReal - 1 / 2) *
        Rd.modulus volume r 2 (scalingFun m) t := by
  refine iSup₂_le fun h hh => ?_
  rw [mul_comm]
  exact (eLpNorm_higherDiff_scalingFun_le_two m hN hp2 r (hh.trans ht)).trans
    (mul_le_mul_left (Rd.eLpNorm_higherDiff_le_modulus hh) _)

/-- **The `L_p` modulus of smoothness of the scaling function, `p ≤ 2`**: let `N ≥ 2`, let
`T^n 1 ≤ C λ^n` be a growth bound for the transfer operator (`Daubechies.TransferGrowth`), and
let `p ≤ 2`. For every real `s` with `0 ≤ s < N - log₄ λ` and every order `r ∈ ℕ` with `r ≥ s`
there is a finite constant `K` with `ω_r(φ, t)_p ≤ K t^s` for all `0 < t ≤ 1`, namely
`K = (2N - 1 + 2r)^(1/p - 1/2) K₂` with the constant `K₂` of the `L²` bound
`Daubechies.modulus_scalingFun_two_le` (`Daubechies.modulus_scalingFun_le_modulus_two`). The
exponent may be any `p ≤ 2`, including `p < 1`. -/
theorem modulus_scalingFun_le_two (hN : 2 ≤ N) {p : ℝ≥0∞} (hp2 : p ≤ 2) {lam C s : ℝ} {r : ℕ}
    (hg : TransferGrowth N lam C) (hs0 : 0 ≤ s) (hs : s < N - Real.logb 4 lam) (hsr : s ≤ r) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r p (scalingFun m) t ≤ K * ENNReal.ofReal (t ^ s) := by
  obtain ⟨K, hK, hmod⟩ := modulus_scalingFun_two_le m hN hg hs0 hs hsr
  have hL : (0 : ℝ) < 2 * N - 1 + 2 * r := by
    have : (2 : ℝ) ≤ N := by exact_mod_cast hN
    linarith [r.cast_nonneg (α := ℝ)]
  refine ⟨ENNReal.ofReal (2 * N - 1 + 2 * r) ^ (1 / p.toReal - 1 / 2) * K,
    ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_ne_zero (ENNReal.ofReal_pos.2 hL).ne'
      ENNReal.ofReal_ne_top) hK, fun t ht => ?_⟩
  rw [mul_assoc]
  exact (modulus_scalingFun_le_modulus_two m hN hp2 r ht.2).trans (mul_le_mul_right (hmod t ht) _)

/-! ### Orders two and three -/

/-- **The `L²` modulus of the scaling function of order two**: for every Daubechies mask of order
`N = 2`, every real `s` with `0 ≤ s < 1` and every order `r ∈ ℕ` with `r ≥ s` there is a finite
constant `K` with `ω_r(φ, t)_2 ≤ K t^s` for all `0 < t ≤ 1`. The growth bound `T^n 1 ≤ 4^n`
(`Daubechies.transferGrowth_two`) has the exponent `2 - log₄ 4 = 1`
(`Daubechies.two_sub_logb_four_four`), so `Daubechies.modulus_scalingFun_two_le` applies. -/
theorem modulus_scalingFun_two_le_order_two (m : Mask 2) {s : ℝ} {r : ℕ} (hs0 : 0 ≤ s)
    (hs : s < 1) (hsr : s ≤ r) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r 2 (scalingFun m) t ≤ K * ENNReal.ofReal (t ^ s) :=
  modulus_scalingFun_two_le m le_rfl transferGrowth_two hs0
    (by rw [Nat.cast_ofNat, two_sub_logb_four_four]; exact hs) hsr

/-- **The `L_p` modulus of the scaling function of order two, `p ≤ 2`**: for every Daubechies
mask of order `N = 2`, every `p ≤ 2`, every real `s` with `0 ≤ s < 1` and every order `r ∈ ℕ`
with `r ≥ s` there is a finite constant `K` with `ω_r(φ, t)_p ≤ K t^s` for all `0 < t ≤ 1`
(`Daubechies.modulus_scalingFun_le_two` with the growth bound `Daubechies.transferGrowth_two`). -/
theorem modulus_scalingFun_le_two_order_two (m : Mask 2) {p : ℝ≥0∞} (hp2 : p ≤ 2) {s : ℝ}
    {r : ℕ} (hs0 : 0 ≤ s) (hs : s < 1) (hsr : s ≤ r) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r p (scalingFun m) t ≤ K * ENNReal.ofReal (t ^ s) :=
  modulus_scalingFun_le_two m le_rfl hp2 transferGrowth_two hs0
    (by rw [Nat.cast_ofNat, two_sub_logb_four_four]; exact hs) hsr

/-- **The `L²` modulus of the scaling function of order three**: for every Daubechies mask of
order `N = 3`, every real `s` with `0 ≤ s < 3 - log₂ 3 ≈ 1.415` and every order `r ∈ ℕ` with
`r ≥ s` there is a finite constant `K` with `ω_r(φ, t)_2 ≤ K t^s` for all `0 < t ≤ 1`. The
growth bound `T^n 1 ≤ 2 · 9^n` (`Daubechies.transferGrowth_three`) has the exponent
`3 - log₄ 9 = 3 - log₂ 3` (`Daubechies.three_sub_logb_four_nine`), so
`Daubechies.modulus_scalingFun_two_le` applies. -/
theorem modulus_scalingFun_two_le_order_three (m : Mask 3) {s : ℝ} {r : ℕ} (hs0 : 0 ≤ s)
    (hs : s < 3 - Real.logb 2 3) (hsr : s ≤ r) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r 2 (scalingFun m) t ≤ K * ENNReal.ofReal (t ^ s) :=
  modulus_scalingFun_two_le m (by norm_num) transferGrowth_three hs0
    (by rw [Nat.cast_ofNat, three_sub_logb_four_nine]; exact hs) hsr

/-- **The `L_p` modulus of the scaling function of order three, `p ≤ 2`**: for every Daubechies
mask of order `N = 3`, every `p ≤ 2`, every real `s` with `0 ≤ s < 3 - log₂ 3` and every order
`r ∈ ℕ` with `r ≥ s` there is a finite constant `K` with `ω_r(φ, t)_p ≤ K t^s` for all
`0 < t ≤ 1` (`Daubechies.modulus_scalingFun_le_two` with the growth bound
`Daubechies.transferGrowth_three`). -/
theorem modulus_scalingFun_le_two_order_three (m : Mask 3) {p : ℝ≥0∞} (hp2 : p ≤ 2) {s : ℝ}
    {r : ℕ} (hs0 : 0 ≤ s) (hs : s < 3 - Real.logb 2 3) (hsr : s ≤ r) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r p (scalingFun m) t ≤ K * ENNReal.ofReal (t ^ s) :=
  modulus_scalingFun_le_two m (by norm_num) hp2 transferGrowth_three hs0
    (by rw [Nat.cast_ofNat, three_sub_logb_four_nine]; exact hs) hsr

end Daubechies
