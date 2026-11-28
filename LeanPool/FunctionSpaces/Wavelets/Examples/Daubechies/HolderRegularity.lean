/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Analysis.Lp.Interpolation
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.SobolevRegularity

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Hölder regularity of the scaling function

For a Daubechies mask of order `N` with symbol product `Φ` (`Daubechies.symbolProduct`) and
scaling function `φ = 𝓕⁻ Φ` (`Daubechies.scalingFun`), this file bounds the differences
`Δ_h^r φ(x)` pointwise and the moduli of smoothness `ω_r(φ, t)_p = sup_{|h| ≤ t} ‖Δ_h^r φ‖_p`
(`Rd.modulus`) for `2 ≤ p ≤ ∞`. Here `Δ_h f(x) = f(x + h) - f(x)` is Mathlib's `fwdDiff h f` and
`Δ_h^r = (fwdDiff h)^[r]` its `r`-fold iterate. Under a growth bound `T^n 1 ≤ C λ^n` for the
transfer operator `T` (`Daubechies.TransferGrowth N λ C`), for every real `a` with
`0 ≤ a < N - log₄ λ - 1/2` and every order `r ∈ ℕ` with `r ≥ a` there is a constant `K` with

`|Δ_h^r φ(x)| ≤ K |h|^a` for all `x, h ∈ ℝ` (`Daubechies.norm_higherDiff_scalingFun_le`).

For `r = 1` and `a ≤ 1` this is the Hölder estimate `|φ(x) - φ(y)| ≤ K |x - y|^a`
(`Daubechies.holder_scalingFun_fourier`); in `L^∞` it reads `ω_r(φ, t)_∞ ≤ K t^a`
(`Daubechies.modulus_scalingFun_top_le`). Interpolation with the `L²` bound `ω_r(φ, t)_2 ≤ K t^s`,
`0 ≤ s < N - log₄ λ`, of `FunctionSpaces.Wavelets.Examples.Daubechies.SobolevRegularity` gives, for
`N ≥ 2`, `2 ≤ p ≤ ∞` and `0 < t ≤ 1`,

`ω_r(φ, t)_p ≤ K t^θ`, `θ = (2/p) s + (1 - 2/p) a` (`Daubechies.modulus_scalingFun_interp`).

* **Differences on the Fourier side.** For integrable `F : ℝ → ℂ`, the translate of `𝓕⁻ F` by `h`
  is the inverse transform of `e^(2πihξ) F(ξ)`, so
  `Δ_h^r (𝓕⁻ F)(x) = 𝓕⁻[ξ ↦ (e^(2πihξ) - 1)^r F(ξ)](x)`
  (`Real.iterate_fwdDiff_fourierInv_apply`) and
  `|Δ_h^r (𝓕⁻ F)(x)| ≤ ∫ |e^(2πihξ) - 1|^r |F(ξ)| dξ`
  (`Real.norm_iterate_fwdDiff_fourierInv_le`).
* **The uniform bound.** For `0 ≤ a ≤ r` and every step `h`,
  `|e^(2πihξ) - 1|^r ≤ (2π)^r |h|^a (1 + |ξ|)^a`
  (`Daubechies.norm_exp_sub_one_pow_le_mul_rpow`, in
  `FunctionSpaces.Wavelets.Examples.Daubechies.SobolevRegularity`), hence
  `|Δ_h^r φ(x)| ≤ (2π)^r (∫ (1 + |ξ|)^a |Φ(ξ)| dξ) |h|^a`
  (`Daubechies.norm_higherDiff_scalingFun_le_mul_rpow`), where the integral is finite for
  `a < N - log₄ λ - 1/2` (`Daubechies.integrable_rpow_mul_norm`); its case `a = 0` is `Φ ∈ L¹`
  (`Daubechies.integrable_symbolProduct_of_growth`, in
  `FunctionSpaces.Wavelets.Examples.Daubechies.SymbolDecay`).
* **Interpolation.** For `2 ≤ p < ∞`, `‖g‖_p ≤ ‖g‖_∞^(1 - 2/p) ‖g‖_2^(2/p)`
  (`Daubechies.eLpNorm_le_rpow_mul_rpow_of_eLpNorm_two_le`, from the project's
  `MeasureTheory.eLpNorm_le_rpow_mul_eLpNorm_rpow`). For differences with a uniform bound
  `|Δ_h^r f(x)| ≤ K |h|^a` and an `L²` bound `‖Δ_h^r f‖_2 ≤ B |h|^s` it gives
  `ω_r(f, t)_p ≤ K^(1 - 2/p) B^(2/p) t^θ` (`Daubechies.modulus_le_of_norm_le_of_eLpNorm_two_le`).
  For the scaling function the uniform bound may be the Fourier one
  (`Daubechies.modulus_scalingFun_interp`) or come from any Hölder estimate
  `|φ(x) - φ(y)| ≤ K₀ |x - y|^a` (`Daubechies.modulus_scalingFun_interp_of_holder`), through
  `|Δ_h^r f(x)| ≤ 2^(r-1) K₀ |h|^a` for `r ≥ 1` (`Daubechies.norm_iterate_fwdDiff_le_of_holder`);
  the Hölder estimate of the mask D4 by the matrix method is of this kind.
* **Orders two and three.** The growth bounds `T^n 1 ≤ 4^n` for `N = 2` and `T^n 1 ≤ 2 · 9^n` for
  `N = 3` (`Daubechies.transferGrowth_two`, `Daubechies.transferGrowth_three`) give the Hölder
  estimates for every `0 ≤ a < 1/2` and every `0 ≤ a < 5/2 - log₂ 3 ≈ 0.915`
  (`Daubechies.holder_scalingFun_order_two`, `Daubechies.holder_scalingFun_order_three`), and the
  interpolated `L_p` bounds with `s < 1` and `s < 3 - log₂ 3`
  (`Daubechies.modulus_scalingFun_interp_order_two`,
  `Daubechies.modulus_scalingFun_interp_order_three`).
-/

@[expose] public section

open MeasureTheory Complex Filter
open scoped Real FourierTransform ENNReal

namespace Real

/-! ### Differences of an inverse Fourier transform -/

variable {F G : ℝ → ℂ}

/-- The inverse Fourier transform of a difference of integrable functions is the difference of
the inverse transforms: `𝓕⁻ (F - G)(x) = 𝓕⁻ F(x) - 𝓕⁻ G(x)`. Since `𝓕⁻ F(x) = 𝓕 F(-x)`
(Mathlib's `Real.fourierInv_eq_fourier_neg`), this is the linearity of the Fourier transform
(`Rd.fourier_sub_apply`). -/
theorem fourierInv_sub_apply (hF : Integrable F) (hG : Integrable G) (x : ℝ) :
    𝓕⁻ (F - G) x = 𝓕⁻ F x - 𝓕⁻ G x := by
  rw [fourierInv_eq_fourier_neg, fourierInv_eq_fourier_neg, fourierInv_eq_fourier_neg,
    Rd.fourier_sub_apply hF hG]

/-- For integrable `F : ℝ → ℂ` and every `h ∈ ℝ`, the modulated function
`ξ ↦ e^(2πihξ) F(ξ)` is integrable: the continuous factor has modulus `1`
(Mathlib's `Complex.norm_exp_ofReal_mul_I`, `MeasureTheory.Integrable.bdd_mul`). -/
theorem integrable_exp_mul (hF : Integrable F) (h : ℝ) :
    Integrable (fun ξ : ℝ => cexp (2 * π * h * ξ * I) * F ξ) :=
  hF.bdd_mul (c := 1)
    (by fun_prop : Continuous fun ξ : ℝ => cexp (2 * π * h * ξ * I)).aestronglyMeasurable
    (Eventually.of_forall fun ξ => by
      rw [Daubechies.exp_two_pi_mul_I_eq, mul_comm, Complex.norm_exp_ofReal_mul_I])

/-- **A difference of an inverse Fourier transform**: for integrable `F : ℝ → ℂ` and all
`h, x ∈ ℝ`, `Δ_h (𝓕⁻ F)(x) = 𝓕⁻[ξ ↦ (e^(2πihξ) - 1) F(ξ)](x)`, where `Δ_h g = g(· + h) - g` is
Mathlib's `fwdDiff h g`. The translate `𝓕⁻ F(x + h)` is the inverse transform of the modulated
function `e^(2πihξ) F(ξ)` (`Real.fourierInv_exp_mul_apply`), and the inverse transform is linear
on integrable functions (`Real.fourierInv_sub_apply`). -/
theorem fwdDiff_fourierInv_apply (hF : Integrable F) (h x : ℝ) :
    fwdDiff h (𝓕⁻ F) x = 𝓕⁻ (fun ξ : ℝ => (cexp (2 * π * h * ξ * I) - 1) * F ξ) x := by
  have hsub : (fun ξ : ℝ => (cexp (2 * π * h * ξ * I) - 1) * F ξ) =
      (fun ξ : ℝ => cexp (2 * π * h * ξ * I) * F ξ) - F := by
    ext ξ
    simp only [Pi.sub_apply]
    ring
  rw [hsub, fourierInv_sub_apply (integrable_exp_mul hF h) hF, fourierInv_exp_mul_apply]
  rfl

/-- **The differences of an inverse Fourier transform**: for integrable `F : ℝ → ℂ`, every
`r ∈ ℕ` and all `h, x ∈ ℝ`, `Δ_h^r (𝓕⁻ F)(x) = 𝓕⁻[ξ ↦ (e^(2πihξ) - 1)^r F(ξ)](x)`, where
`Δ_h^r = (fwdDiff h)^[r]` is the `r`-fold difference. By induction on `r` with
`Real.fwdDiff_fourierInv_apply`, since the functions `(e^(2πihξ) - 1)^r F(ξ)` are integrable
(`Real.integrable_exp_sub_one_pow_mul`). It is the inverse-transform form of
`Real.fourier_iterate_fwdDiff_apply`. -/
theorem iterate_fwdDiff_fourierInv_apply (hF : Integrable F) (r : ℕ) (h x : ℝ) :
    (fwdDiff h)^[r] (𝓕⁻ F) x = 𝓕⁻ (fun ξ : ℝ => (cexp (2 * π * h * ξ * I) - 1) ^ r * F ξ) x := by
  induction r generalizing x with
  | zero => simp
  | succ r ih =>
    rw [Function.iterate_succ_apply', funext ih,
      fwdDiff_fourierInv_apply (integrable_exp_sub_one_pow_mul hF r h)]
    refine congrArg (fun G : ℝ → ℂ => 𝓕⁻ G x) (funext fun ξ => ?_)
    ring

/-- **The uniform bound for the differences of an inverse Fourier transform**: for integrable
`F : ℝ → ℂ`, every `r ∈ ℕ` and all `h, x ∈ ℝ`,
`|Δ_h^r (𝓕⁻ F)(x)| ≤ ∫ |e^(2πihξ) - 1|^r |F(ξ)| dξ`, the formula
`Real.iterate_fwdDiff_fourierInv_apply` together with `|𝓕⁻ G(x)| ≤ ∫ |G|`
(`Real.norm_fourierInv_le_integral_norm`). -/
theorem norm_iterate_fwdDiff_fourierInv_le (hF : Integrable F) (r : ℕ) (h x : ℝ) :
    ‖(fwdDiff h)^[r] (𝓕⁻ F) x‖ ≤ ∫ ξ : ℝ, ‖cexp (2 * π * h * ξ * I) - 1‖ ^ r * ‖F ξ‖ := by
  rw [iterate_fwdDiff_fourierInv_apply hF]
  refine (norm_fourierInv_le_integral_norm _ x).trans_eq ?_
  simp_rw [norm_mul, norm_pow]

end Real

namespace Daubechies

/-! ### Pointwise bounds for the differences of the scaling function -/

variable {N : ℕ} (m : Mask N)

/-- **The differences of the scaling function as inverse Fourier transforms**: if the symbol
product `Φ` is integrable, then `Δ_h^r φ(x) = 𝓕⁻[ξ ↦ (e^(2πihξ) - 1)^r Φ(ξ)](x)` for every
`r ∈ ℕ` and all `h, x ∈ ℝ`. This is `Real.iterate_fwdDiff_fourierInv_apply` for `φ = 𝓕⁻ Φ`
(`Daubechies.scalingFun`). -/
theorem higherDiff_scalingFun_eq_fourierInv (hΦ : Integrable (symbolProduct m)) (r : ℕ)
    (h x : ℝ) :
    (fwdDiff h)^[r] (scalingFun m) x =
      𝓕⁻ (fun ξ : ℝ => (cexp (2 * π * h * ξ * I) - 1) ^ r * symbolProduct m ξ) x :=
  Real.iterate_fwdDiff_fourierInv_apply hΦ r h x

/-- **The uniform bound for the differences of the scaling function**: if `Φ` is integrable,
then `|Δ_h^r φ(x)| ≤ ∫ |e^(2πihξ) - 1|^r |Φ(ξ)| dξ` for every `r ∈ ℕ` and all `h, x ∈ ℝ`
(`Real.norm_iterate_fwdDiff_fourierInv_le` for `φ = 𝓕⁻ Φ`). -/
theorem norm_higherDiff_scalingFun_le_integral (hΦ : Integrable (symbolProduct m)) (r : ℕ)
    (h x : ℝ) :
    ‖(fwdDiff h)^[r] (scalingFun m) x‖ ≤
      ∫ ξ : ℝ, ‖cexp (2 * π * h * ξ * I) - 1‖ ^ r * ‖symbolProduct m ξ‖ :=
  Real.norm_iterate_fwdDiff_fourierInv_le hΦ r h x

/-- **The uniform bound for the differences of the scaling function, with an explicit
constant**: let `T^n 1 ≤ C λ^n` be a growth bound for the transfer operator
(`Daubechies.TransferGrowth`), and let `a ∈ ℝ`, `r ∈ ℕ` with `0 ≤ a ≤ r` and
`a < N - log₄ λ - 1/2`. Then for all `h, x ∈ ℝ`,
`|Δ_h^r φ(x)| ≤ (2π)^r (∫ (1 + |ξ|)^a |Φ(ξ)| dξ) |h|^a`.
The multiplier bound `|e^(2πihξ) - 1|^r ≤ (2π)^r |h|^a (1 + |ξ|)^a`
(`Daubechies.norm_exp_sub_one_pow_le_mul_rpow`) inside
`Daubechies.norm_higherDiff_scalingFun_le_integral` gives the estimate; the condition
`a < N - log₄ λ - 1/2` makes `(1 + |ξ|)^a |Φ(ξ)|` integrable
(`Daubechies.integrable_rpow_mul_norm`). -/
theorem norm_higherDiff_scalingFun_le_mul_rpow {lam C a : ℝ} {r : ℕ}
    (hg : TransferGrowth N lam C) (ha0 : 0 ≤ a) (har : a ≤ r)
    (ha : a < N - Real.logb 4 lam - 1 / 2) (h x : ℝ) :
    ‖(fwdDiff h)^[r] (scalingFun m) x‖ ≤
      (2 * π) ^ r * (∫ ξ, (1 + |ξ|) ^ a * ‖symbolProduct m ξ‖) * |h| ^ a := by
  refine (norm_higherDiff_scalingFun_le_integral m
    (integrable_symbolProduct_of_growth m hg (ha0.trans_lt ha)) r h x).trans ?_
  calc ∫ ξ : ℝ, ‖cexp (2 * π * h * ξ * I) - 1‖ ^ r * ‖symbolProduct m ξ‖
      ≤ ∫ ξ, (2 * π) ^ r * |h| ^ a * ((1 + |ξ|) ^ a * ‖symbolProduct m ξ‖) := by
        refine integral_mono_of_nonneg (Eventually.of_forall fun ξ => by positivity)
          ((integrable_rpow_mul_norm m hg ha).const_mul _) (Eventually.of_forall fun ξ => ?_)
        calc ‖cexp (2 * π * h * ξ * I) - 1‖ ^ r * ‖symbolProduct m ξ‖
            ≤ (2 * π) ^ r * (|h| ^ a * (1 + |ξ|) ^ a) * ‖symbolProduct m ξ‖ :=
              mul_le_mul_of_nonneg_right (norm_exp_sub_one_pow_le_mul_rpow ha0 har h ξ)
                (norm_nonneg _)
          _ = (2 * π) ^ r * |h| ^ a * ((1 + |ξ|) ^ a * ‖symbolProduct m ξ‖) := by ring
    _ = (2 * π) ^ r * (∫ ξ, (1 + |ξ|) ^ a * ‖symbolProduct m ξ‖) * |h| ^ a := by
        rw [integral_const_mul]
        ring

/-- **Uniform bounds for the differences of the scaling function**: let `T^n 1 ≤ C λ^n` be a
growth bound for the transfer operator (`Daubechies.TransferGrowth`), and let `a ∈ ℝ`, `r ∈ ℕ`
with `0 ≤ a ≤ r` and `a < N - log₄ λ - 1/2`. Then there is a constant `K` with
`|Δ_h^r φ(x)| ≤ K |h|^a` for all `x, h ∈ ℝ`, namely `K = (2π)^r ∫ (1 + |ξ|)^a |Φ(ξ)| dξ`
(`Daubechies.norm_higherDiff_scalingFun_le_mul_rpow`). -/
theorem norm_higherDiff_scalingFun_le {lam C a : ℝ} {r : ℕ} (hg : TransferGrowth N lam C)
    (ha0 : 0 ≤ a) (har : a ≤ r) (ha : a < N - Real.logb 4 lam - 1 / 2) :
    ∃ K : ℝ, ∀ x h : ℝ, ‖(fwdDiff h)^[r] (scalingFun m) x‖ ≤ K * |h| ^ a :=
  ⟨_, fun x h => norm_higherDiff_scalingFun_le_mul_rpow m hg ha0 har ha h x⟩

/-- **The Hölder estimate of the scaling function** (Fourier route): let `T^n 1 ≤ C λ^n` be a
growth bound for the transfer operator (`Daubechies.TransferGrowth`), and let `0 ≤ a ≤ 1` with
`a < N - log₄ λ - 1/2`. Then there is a constant `K` with `|φ(x) - φ(y)| ≤ K |x - y|^a` for all
`x, y ∈ ℝ`: the case `r = 1` of `Daubechies.norm_higherDiff_scalingFun_le`, with step
`h = x - y` at the point `y`. -/
theorem holder_scalingFun_fourier {lam C a : ℝ} (hg : TransferGrowth N lam C) (ha0 : 0 ≤ a)
    (ha1 : a ≤ 1) (ha : a < N - Real.logb 4 lam - 1 / 2) :
    ∃ K : ℝ, ∀ x y : ℝ, ‖scalingFun m x - scalingFun m y‖ ≤ K * |x - y| ^ a := by
  obtain ⟨K, hK⟩ := norm_higherDiff_scalingFun_le m hg ha0 (r := 1) (by simpa using ha1) ha
  refine ⟨K, fun x y => ?_⟩
  have h := hK y (x - y)
  rwa [Function.iterate_one, fwdDiff, add_sub_cancel] at h

/-! ### The uniform modulus of smoothness -/

/-- **A uniform bound gives an `L^∞` bound**: if `g` is almost everywhere strongly measurable and
`|g(x)| ≤ B` for every `x`, then `‖g‖_∞ ≤ B`. Here `‖g‖_∞` is the essential supremum of `|g|`
(Mathlib's `MeasureTheory.eLpNorm_exponent_top`, `MeasureTheory.eLpNormEssSup_le_of_ae_bound`). -/
theorem eLpNorm_top_le_of_norm_le {α E : Type*} [MeasurableSpace α] {μ : Measure α}
    [NormedAddCommGroup E] {g : α → E} (hg : AEStronglyMeasurable g μ) {B : ℝ}
    (hB : ∀ x, ‖g x‖ ≤ B) : eLpNorm g ∞ μ ≤ ENNReal.ofReal B := by
  rw [eLpNorm_exponent_top hg]
  exact eLpNormEssSup_le_of_ae_bound (Eventually.of_forall hB)

/-- **The uniform modulus from a pointwise bound**: let `f : ℝ → ℂ` be almost everywhere strongly
measurable, `r ∈ ℕ` and `a ≥ 0`, and suppose `|Δ_h^r f(x)| ≤ K |h|^a` for all `x, h ∈ ℝ`. Then
`ω_r(f, t)_∞ ≤ K t^a` for every `t ∈ ℝ`, since every step `|h| ≤ t` has
`‖Δ_h^r f‖_∞ ≤ K |h|^a ≤ K t^a` (`Daubechies.eLpNorm_top_le_of_norm_le`). -/
theorem modulus_top_le_of_norm_le {f : ℝ → ℂ} (hf : AEStronglyMeasurable f) {r : ℕ} {K a : ℝ}
    (ha0 : 0 ≤ a) (hK : ∀ x h : ℝ, ‖(fwdDiff h)^[r] f x‖ ≤ K * |h| ^ a) (t : ℝ) :
    Rd.modulus volume r ∞ f t ≤ ENNReal.ofReal K * ENNReal.ofReal (t ^ a) := by
  refine iSup₂_le fun h hh => ?_
  refine (eLpNorm_top_le_of_norm_le (Rd.aestronglyMeasurable_higherDiff hf r h)
    fun x => hK x h).trans ?_
  rw [ENNReal.ofReal_mul' (by positivity)]
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg h) hh ha0)) _

/-- **The uniform modulus of smoothness of the scaling function**: let `T^n 1 ≤ C λ^n` be a
growth bound for the transfer operator (`Daubechies.TransferGrowth`), and let `a ∈ ℝ`, `r ∈ ℕ`
with `0 ≤ a ≤ r` and `a < N - log₄ λ - 1/2`. Then there is a finite constant `K` with
`ω_r(φ, t)_∞ ≤ K t^a` for all `0 < t ≤ 1` (`Daubechies.modulus_top_le_of_norm_le` with the
pointwise bound `Daubechies.norm_higherDiff_scalingFun_le_mul_rpow`). The scaling function is
continuous as the inverse Fourier transform of the integrable function `Φ`
(`Daubechies.integrable_symbolProduct_of_growth`). -/
theorem modulus_scalingFun_top_le {lam C a : ℝ} {r : ℕ} (hg : TransferGrowth N lam C)
    (ha0 : 0 ≤ a) (har : a ≤ r) (ha : a < N - Real.logb 4 lam - 1 / 2) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r ∞ (scalingFun m) t ≤ K * ENNReal.ofReal (t ^ a) := by
  have hφ : Continuous (scalingFun m) := Real.continuous_fourierInv_of_integrable
    (integrable_symbolProduct_of_growth m hg (ha0.trans_lt ha))
  exact ⟨_, ENNReal.ofReal_ne_top, fun t _ => modulus_top_le_of_norm_le hφ.aestronglyMeasurable
    ha0 (fun x h => norm_higherDiff_scalingFun_le_mul_rpow m hg ha0 har ha h x) t⟩

/-! ### Interpolation between `L²` and `L^∞` -/

/-- **Interpolation between `L²` and `L^∞`** on the line: if `g : ℝ → ℂ` is almost everywhere
strongly measurable with `|g(x)| ≤ M` for every `x` and `‖g‖_2 ≤ B`, then
`‖g‖_p ≤ M^(1 - 2/p) B^(2/p)` for every `2 ≤ p < ∞`. This is the project's
`MeasureTheory.eLpNorm_le_rpow_mul_eLpNorm_rpow` with the smaller exponent `2` and the larger
exponent `p`, followed by `‖g‖_2^(2/p) ≤ B^(2/p)`. -/
theorem eLpNorm_le_rpow_mul_rpow_of_eLpNorm_two_le {g : ℝ → ℂ} (hg : AEStronglyMeasurable g)
    {M B : ℝ≥0∞} (hM : ∀ x, ‖g x‖ₑ ≤ M) (hB : eLpNorm g 2 volume ≤ B) {p : ℝ≥0∞} (hp2 : 2 ≤ p)
    (hp : p ≠ ∞) :
    eLpNorm g p volume ≤ M ^ (1 - 2 / p.toReal) * B ^ (2 / p.toReal) := by
  have h := eLpNorm_le_rpow_mul_eLpNorm_rpow hg (Eventually.of_forall hM) (p := 2) (r := p)
    two_ne_zero hp2 hp
  rw [ENNReal.toReal_ofNat] at h
  exact h.trans (mul_le_mul_right (ENNReal.rpow_le_rpow hB (by positivity)) _)

/-- `(A x^a)^α (B x^s)^β = A^α B^β x^(βs + αa)` in `[0, ∞]`, for nonnegative real exponents
`a, s, α, β` (Mathlib's `ENNReal.mul_rpow_of_nonneg`, `ENNReal.rpow_mul`,
`ENNReal.rpow_add_of_nonneg`). -/
theorem mul_rpow_mul_mul_rpow (A B x : ℝ≥0∞) {a s α β : ℝ} (ha : 0 ≤ a) (hs : 0 ≤ s)
    (hα : 0 ≤ α) (hβ : 0 ≤ β) :
    (A * x ^ a) ^ α * (B * x ^ s) ^ β = A ^ α * B ^ β * x ^ (β * s + α * a) := by
  rw [ENNReal.mul_rpow_of_nonneg _ _ hα, ENNReal.mul_rpow_of_nonneg _ _ hβ, ← ENNReal.rpow_mul,
    ← ENNReal.rpow_mul, show β * s + α * a = a * α + s * β by ring,
    ENNReal.rpow_add_of_nonneg _ _ (mul_nonneg ha hα) (mul_nonneg hs hβ)]
  ring

/-- The weight of the uniform norm in the interpolation inequality is nonnegative:
`1 - 2/p ≥ 0` for `2 ≤ p < ∞`, where `2/p` stands for `2 / p.toReal`. -/
theorem one_sub_two_div_toReal_nonneg {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ∞) :
    0 ≤ 1 - 2 / p.toReal := by
  have h2p : (2 : ℝ) ≤ p.toReal := by
    simpa using ENNReal.toReal_mono hp hp2
  exact sub_nonneg.2 ((div_le_one (by linarith)).2 h2p)

/-- **The `L_p` modulus by interpolation**: let `f : ℝ → ℂ` be almost everywhere strongly
measurable, `r ∈ ℕ`, `a, s ≥ 0`, and suppose that for all `x, h ∈ ℝ` the differences satisfy the
uniform bound `|Δ_h^r f(x)| ≤ K |h|^a` and the `L²` bound `‖Δ_h^r f‖_2 ≤ B |h|^s`. Then for every
`2 ≤ p < ∞` and every `t ∈ ℝ`,
`ω_r(f, t)_p ≤ K^(1 - 2/p) B^(2/p) t^θ` with `θ = (2/p) s + (1 - 2/p) a`.
For each step `h` the interpolation inequality
`‖g‖_p ≤ ‖g‖_∞^(1 - 2/p) ‖g‖_2^(2/p)` (`Daubechies.eLpNorm_le_rpow_mul_rpow_of_eLpNorm_two_le`)
gives `‖Δ_h^r f‖_p ≤ K^(1 - 2/p) B^(2/p) |h|^θ` (`Daubechies.mul_rpow_mul_mul_rpow`), and
`|h|^θ ≤ t^θ` for `|h| ≤ t`. -/
theorem modulus_le_of_norm_le_of_eLpNorm_two_le {f : ℝ → ℂ} (hf : AEStronglyMeasurable f)
    {r : ℕ} {K a s : ℝ} {B : ℝ≥0∞} (ha0 : 0 ≤ a) (hs0 : 0 ≤ s)
    (hK : ∀ x h : ℝ, ‖(fwdDiff h)^[r] f x‖ ≤ K * |h| ^ a)
    (hB : ∀ h : ℝ, eLpNorm ((fwdDiff h)^[r] f) 2 volume ≤ B * ENNReal.ofReal (|h| ^ s))
    {p : ℝ≥0∞} (hp2 : 2 ≤ p) (hp : p ≠ ∞) (t : ℝ) :
    Rd.modulus volume r p f t ≤ ENNReal.ofReal K ^ (1 - 2 / p.toReal) * B ^ (2 / p.toReal) *
      ENNReal.ofReal (t ^ (2 / p.toReal * s + (1 - 2 / p.toReal) * a)) := by
  have hα := one_sub_two_div_toReal_nonneg hp2 hp
  have hβ : 0 ≤ 2 / p.toReal := by positivity
  have hθ : 0 ≤ 2 / p.toReal * s + (1 - 2 / p.toReal) * a :=
    add_nonneg (mul_nonneg hβ hs0) (mul_nonneg hα ha0)
  refine iSup₂_le fun h hh => ?_
  have hM : ∀ y, ‖(fwdDiff h)^[r] f y‖ₑ ≤ ENNReal.ofReal K * ENNReal.ofReal |h| ^ a :=
    fun y => by
      rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg h) ha0, ← ENNReal.ofReal_mul' (by positivity),
        ← ofReal_norm]
      exact ENNReal.ofReal_le_ofReal (hK y h)
  have hB' : eLpNorm ((fwdDiff h)^[r] f) 2 volume ≤ B * ENNReal.ofReal |h| ^ s := by
    rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg h) hs0]
    exact hB h
  refine (eLpNorm_le_rpow_mul_rpow_of_eLpNorm_two_le (Rd.aestronglyMeasurable_higherDiff hf r h)
    hM hB' hp2 hp).trans ?_
  rw [mul_rpow_mul_mul_rpow _ _ _ ha0 hs0 hα hβ, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg h) hθ]
  exact mul_le_mul_right (ENNReal.ofReal_le_ofReal (Real.rpow_le_rpow (abs_nonneg h) hh hθ)) _

/-! ### The `L_p` modulus of the scaling function for `p ≥ 2` -/

/-- **The `L_p` modulus of the scaling function from a uniform bound, `p ≥ 2`**: let `N ≥ 2`, let
`T^n 1 ≤ C λ^n` be a growth bound for the transfer operator (`Daubechies.TransferGrowth`), let
`s ∈ ℝ`, `r ∈ ℕ` with `0 ≤ s ≤ r` and `s < N - log₄ λ`, and suppose that the differences of `φ`
satisfy a uniform bound `|Δ_h^r φ(x)| ≤ K₀ |h|^a` for all `x, h ∈ ℝ`, with `a ≥ 0`. Then for
every `p ∈ [2, ∞]` there is a finite constant `K` with `ω_r(φ, t)_p ≤ K t^θ` for all
`0 < t ≤ 1`, where `θ = (2/p) s + (1 - 2/p) a`; for `p = ∞` the weight `2/p` is `0` (in Lean,
`(∞ : ℝ≥0∞).toReal = 0`), so `θ = a`. For `p < ∞` this is the interpolation
`Daubechies.modulus_le_of_norm_le_of_eLpNorm_two_le` with the `L²` bound
`Daubechies.eLpNorm_two_higherDiff_scalingFun_le`; for `p = ∞` it is
`Daubechies.modulus_top_le_of_norm_le`. -/
theorem modulus_scalingFun_interp_of_norm_le (hN : 2 ≤ N) {p : ℝ≥0∞} (hp2 : 2 ≤ p)
    {lam C s a K₀ : ℝ} {r : ℕ} (hg : TransferGrowth N lam C) (hs0 : 0 ≤ s)
    (hs : s < N - Real.logb 4 lam) (hsr : s ≤ r) (ha0 : 0 ≤ a)
    (hK : ∀ x h : ℝ, ‖(fwdDiff h)^[r] (scalingFun m) x‖ ≤ K₀ * |h| ^ a) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r p (scalingFun m) t ≤
        K * ENNReal.ofReal (t ^ (2 / p.toReal * s + (1 - 2 / p.toReal) * a)) := by
  have hφ : AEStronglyMeasurable (scalingFun m) := (continuous_scalingFun m hN).aestronglyMeasurable
  rcases eq_or_ne p ∞ with rfl | hp
  · refine ⟨ENNReal.ofReal K₀, ENNReal.ofReal_ne_top, fun t _ => ?_⟩
    rw [ENNReal.toReal_top, div_zero, zero_mul, zero_add, sub_zero, one_mul]
    exact modulus_top_le_of_norm_le hφ ha0 hK t
  · refine ⟨ENNReal.ofReal K₀ ^ (1 - 2 / p.toReal) * ENNReal.ofReal ((2 * π) ^ r *
      √(∫ ξ, (1 + |ξ|) ^ (2 * s) * ‖symbolProduct m ξ‖ ^ 2)) ^ (2 / p.toReal),
      ENNReal.mul_ne_top (ENNReal.rpow_ne_top_of_nonneg (one_sub_two_div_toReal_nonneg hp2 hp)
        ENNReal.ofReal_ne_top) (ENNReal.rpow_ne_top_of_nonneg (by positivity)
        ENNReal.ofReal_ne_top), fun t _ => ?_⟩
    exact modulus_le_of_norm_le_of_eLpNorm_two_le hφ ha0 hs0 hK
      (eLpNorm_two_higherDiff_scalingFun_le m hN hg hs0 hs hsr) hp2 hp t

/-- **The `L_p` modulus of the scaling function, `p ≥ 2`** (Fourier route): let `N ≥ 2`, let
`T^n 1 ≤ C λ^n` be a growth bound for the transfer operator (`Daubechies.TransferGrowth`), and
let `s, a ∈ ℝ`, `r ∈ ℕ` with `0 ≤ s ≤ r`, `s < N - log₄ λ`, `0 ≤ a ≤ r` and
`a < N - log₄ λ - 1/2`. Then for every `p ∈ [2, ∞]` there is a finite constant `K` with
`ω_r(φ, t)_p ≤ K t^θ` for all `0 < t ≤ 1`, where `θ = (2/p) s + (1 - 2/p) a` interpolates between
the `L²` exponent `s` (`p = 2`) and the uniform exponent `a` (`p = ∞`, where `2/p = 0`). The
uniform bound is `Daubechies.norm_higherDiff_scalingFun_le`, and
`Daubechies.modulus_scalingFun_interp_of_norm_le` interpolates. -/
theorem modulus_scalingFun_interp (hN : 2 ≤ N) {p : ℝ≥0∞} (hp2 : 2 ≤ p) {lam C s a : ℝ} {r : ℕ}
    (hg : TransferGrowth N lam C) (hs0 : 0 ≤ s) (hs : s < N - Real.logb 4 lam) (hsr : s ≤ r)
    (ha0 : 0 ≤ a) (har : a ≤ r) (ha : a < N - Real.logb 4 lam - 1 / 2) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r p (scalingFun m) t ≤
        K * ENNReal.ofReal (t ^ (2 / p.toReal * s + (1 - 2 / p.toReal) * a)) := by
  obtain ⟨K₀, hK⟩ := norm_higherDiff_scalingFun_le m hg ha0 har ha
  exact modulus_scalingFun_interp_of_norm_le m hN hp2 hg hs0 hs hsr ha0 hK

/-! ### Hölder estimates from other sources -/

/-- **Higher differences of a Hölder function**: if `|f(x) - f(y)| ≤ K |x - y|^a` for all
`x, y ∈ ℝ`, then `|Δ_h^(r+1) f(x)| ≤ 2^r K |h|^a` for every `r ∈ ℕ` and all `x, h ∈ ℝ`. By
induction on `r`: the case `r = 0` is the Hölder estimate at `x + h` and `x`, and
`Δ_h^(r+2) f(x) = Δ_h^(r+1) f(x + h) - Δ_h^(r+1) f(x)`. -/
theorem norm_iterate_fwdDiff_le_of_holder {E : Type*} [NormedAddCommGroup E] {f : ℝ → E}
    {K a : ℝ} (hf : ∀ x y, ‖f x - f y‖ ≤ K * |x - y| ^ a) (r : ℕ) (h x : ℝ) :
    ‖(fwdDiff h)^[r + 1] f x‖ ≤ 2 ^ r * K * |h| ^ a := by
  induction r generalizing x with
  | zero =>
    have h0 := hf (x + h) x
    rw [add_sub_cancel_left] at h0
    rw [zero_add, Function.iterate_one, pow_zero, one_mul]
    exact h0
  | succ r ih =>
    rw [Function.iterate_succ_apply']
    calc ‖fwdDiff h ((fwdDiff h)^[r + 1] f) x‖
        = ‖(fwdDiff h)^[r + 1] f (x + h) - (fwdDiff h)^[r + 1] f x‖ := rfl
      _ ≤ ‖(fwdDiff h)^[r + 1] f (x + h)‖ + ‖(fwdDiff h)^[r + 1] f x‖ := norm_sub_le _ _
      _ ≤ 2 ^ r * K * |h| ^ a + 2 ^ r * K * |h| ^ a := add_le_add (ih (x + h)) (ih x)
      _ = 2 ^ (r + 1) * K * |h| ^ a := by ring

/-- **The `L_p` modulus of the scaling function from a Hölder estimate, `p ≥ 2`**: let `N ≥ 2`,
let `T^n 1 ≤ C λ^n` be a growth bound for the transfer operator (`Daubechies.TransferGrowth`), let
`s ∈ ℝ` and an order `r ≥ 1` with `0 ≤ s ≤ r` and `s < N - log₄ λ`, and suppose
`|φ(x) - φ(y)| ≤ K₀ |x - y|^a` for all `x, y ∈ ℝ`, with `a ≥ 0`. Then for every `p ∈ [2, ∞]`
there is a finite constant `K` with `ω_r(φ, t)_p ≤ K t^θ` for all `0 < t ≤ 1`, where
`θ = (2/p) s + (1 - 2/p) a`. The Hölder estimate bounds the differences,
`|Δ_h^r φ(x)| ≤ 2^(r-1) K₀ |h|^a` (`Daubechies.norm_iterate_fwdDiff_le_of_holder`), and
`Daubechies.modulus_scalingFun_interp_of_norm_le` interpolates. The Hölder exponent may come from
any source, such as the matrix method for the mask D4. -/
theorem modulus_scalingFun_interp_of_holder (hN : 2 ≤ N) {p : ℝ≥0∞} (hp2 : 2 ≤ p)
    {lam C s a K₀ : ℝ} {r : ℕ} (hr : 1 ≤ r) (hg : TransferGrowth N lam C) (hs0 : 0 ≤ s)
    (hs : s < N - Real.logb 4 lam) (hsr : s ≤ r) (ha0 : 0 ≤ a)
    (hK : ∀ x y : ℝ, ‖scalingFun m x - scalingFun m y‖ ≤ K₀ * |x - y| ^ a) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r p (scalingFun m) t ≤
        K * ENNReal.ofReal (t ^ (2 / p.toReal * s + (1 - 2 / p.toReal) * a)) := by
  obtain ⟨k, rfl⟩ : ∃ k, r = k + 1 := ⟨r - 1, by omega⟩
  exact modulus_scalingFun_interp_of_norm_le m hN hp2 hg hs0 hs hsr ha0 (K₀ := 2 ^ k * K₀)
    fun x h => norm_iterate_fwdDiff_le_of_holder hK k h x

/-! ### Orders two and three -/

/-- `log₂ 3 > 3/2`, since `2^3 = 8 < 9 = 3^2` (Mathlib's `Real.log_lt_log`, `Real.log_pow`).
Hence the exponent `5/2 - log₂ 3 ≈ 0.915` of order three lies below `1`. -/
theorem three_halves_lt_logb_two_three : 3 / 2 < Real.logb 2 3 := by
  rw [← Real.log_div_log, lt_div_iff₀ (Real.log_pos one_lt_two)]
  have h : Real.log (2 ^ 3) < Real.log (3 ^ 2) := Real.log_lt_log (by norm_num) (by norm_num)
  rw [Real.log_pow, Real.log_pow] at h
  push_cast at h
  linarith

/-- **The Hölder estimate of the scaling function of order two** (Fourier route): for every
Daubechies mask of order `N = 2` and every `0 ≤ a < 1/2` there is a constant `K` with
`|φ(x) - φ(y)| ≤ K |x - y|^a` for all `x, y ∈ ℝ`. The growth bound `T^n 1 ≤ 4^n`
(`Daubechies.transferGrowth_two`) gives `N - log₄ λ - 1/2 = 2 - 1 - 1/2 = 1/2`
(`Daubechies.two_sub_logb_four_four`), so `Daubechies.holder_scalingFun_fourier` applies. -/
theorem holder_scalingFun_order_two (m : Mask 2) {a : ℝ} (ha0 : 0 ≤ a) (ha : a < 1 / 2) :
    ∃ K : ℝ, ∀ x y : ℝ, ‖scalingFun m x - scalingFun m y‖ ≤ K * |x - y| ^ a :=
  holder_scalingFun_fourier m transferGrowth_two ha0 (by linarith)
    (by rw [Nat.cast_ofNat, two_sub_logb_four_four]; linarith)

/-- **The Hölder estimate of the scaling function of order three** (Fourier route): for every
Daubechies mask of order `N = 3` and every `0 ≤ a < 5/2 - log₂ 3 ≈ 0.915` there is a constant `K`
with `|φ(x) - φ(y)| ≤ K |x - y|^a` for all `x, y ∈ ℝ`. The growth bound `T^n 1 ≤ 2 · 9^n`
(`Daubechies.transferGrowth_three`) gives `N - log₄ λ - 1/2 = 3 - log₂ 3 - 1/2`
(`Daubechies.three_sub_logb_four_nine`), and `a < 1` by
`Daubechies.three_halves_lt_logb_two_three`, so `Daubechies.holder_scalingFun_fourier`
applies. -/
theorem holder_scalingFun_order_three (m : Mask 3) {a : ℝ} (ha0 : 0 ≤ a)
    (ha : a < 5 / 2 - Real.logb 2 3) :
    ∃ K : ℝ, ∀ x y : ℝ, ‖scalingFun m x - scalingFun m y‖ ≤ K * |x - y| ^ a :=
  holder_scalingFun_fourier m transferGrowth_three ha0
    (by linarith [three_halves_lt_logb_two_three])
    (by rw [Nat.cast_ofNat, three_sub_logb_four_nine]; linarith)

/-- **The `L_p` modulus of the scaling function of order two, `p ≥ 2`**: for every Daubechies
mask of order `N = 2`, every `p ∈ [2, ∞]`, all real `s, a` with `0 ≤ s < 1` and `0 ≤ a < 1/2`,
and every order `r ∈ ℕ` with `r ≥ s` and `r ≥ a`, there is a finite constant `K` with
`ω_r(φ, t)_p ≤ K t^θ` for all `0 < t ≤ 1`, where `θ = (2/p) s + (1 - 2/p) a`
(`Daubechies.modulus_scalingFun_interp` with the growth bound `Daubechies.transferGrowth_two`,
whose exponents are `2 - log₄ 4 = 1` and `1 - 1/2 = 1/2`). -/
theorem modulus_scalingFun_interp_order_two (m : Mask 2) {p : ℝ≥0∞} (hp2 : 2 ≤ p) {s a : ℝ}
    {r : ℕ} (hs0 : 0 ≤ s) (hs : s < 1) (hsr : s ≤ r) (ha0 : 0 ≤ a) (har : a ≤ r)
    (ha : a < 1 / 2) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r p (scalingFun m) t ≤
        K * ENNReal.ofReal (t ^ (2 / p.toReal * s + (1 - 2 / p.toReal) * a)) :=
  modulus_scalingFun_interp m le_rfl hp2 transferGrowth_two hs0
    (by rw [Nat.cast_ofNat, two_sub_logb_four_four]; exact hs) hsr ha0 har
    (by rw [Nat.cast_ofNat, two_sub_logb_four_four]; linarith)

/-- **The `L_p` modulus of the scaling function of order three, `p ≥ 2`**: for every Daubechies
mask of order `N = 3`, every `p ∈ [2, ∞]`, all real `s, a` with `0 ≤ s < 3 - log₂ 3` and
`0 ≤ a < 5/2 - log₂ 3`, and every order `r ∈ ℕ` with `r ≥ s` and `r ≥ a`, there is a finite
constant `K` with `ω_r(φ, t)_p ≤ K t^θ` for all `0 < t ≤ 1`, where `θ = (2/p) s + (1 - 2/p) a`
(`Daubechies.modulus_scalingFun_interp` with the growth bound `Daubechies.transferGrowth_three`,
whose exponent is `3 - log₄ 9 = 3 - log₂ 3`). -/
theorem modulus_scalingFun_interp_order_three (m : Mask 3) {p : ℝ≥0∞} (hp2 : 2 ≤ p) {s a : ℝ}
    {r : ℕ} (hs0 : 0 ≤ s) (hs : s < 3 - Real.logb 2 3) (hsr : s ≤ r) (ha0 : 0 ≤ a) (har : a ≤ r)
    (ha : a < 5 / 2 - Real.logb 2 3) :
    ∃ K : ℝ≥0∞, K ≠ ∞ ∧ ∀ t ∈ Set.Ioc (0 : ℝ) 1,
      Rd.modulus volume r p (scalingFun m) t ≤
        K * ENNReal.ofReal (t ^ (2 / p.toReal * s + (1 - 2 / p.toReal) * a)) :=
  modulus_scalingFun_interp m (by norm_num) hp2 transferGrowth_three hs0
    (by rw [Nat.cast_ofNat, three_sub_logb_four_nine]; exact hs) hsr ha0 har
    (by rw [Nat.cast_ofNat, three_sub_logb_four_nine]; linarith)

end Daubechies
