/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.FourierIntegrable
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.SymbolDecay

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Daubechies scaling function

For a Daubechies mask of order `N` with filter coefficients `c_k` (`Daubechies.coeff`), symbol
`m_0(ξ) = (1/2) ∑_k c_k e^(-2πikξ)` (`Daubechies.symbol`) and symbol product
`Φ(ξ) = ∏_{j ≥ 0} m_0(ξ/2^(j+1))` (`Daubechies.symbolProduct`), the **scaling function** is the
inverse Fourier transform of `Φ`,

`φ(x) = 𝓕⁻ Φ(x) = ∫ Φ(ξ) e^(2πixξ) dξ` (`Daubechies.scalingFun`,
`Daubechies.scalingFun_eq_integral`).

For `N ≥ 2` the symbol product is integrable (`Daubechies.integrable_symbolProduct`), so `φ` is
continuous (`Daubechies.continuous_scalingFun`), and `|φ(x)| ≤ ∫ |Φ|` for every `x`
(`Daubechies.norm_scalingFun_le`). The file `FunctionSpaces.Wavelets.Examples.Daubechies.Cascade`
proves that `φ` has compact support, by the cascade algorithm, and then that `𝓕 φ = Φ`, by Fourier
inversion.

**The refinement equation.** For `N ≥ 2` and every `x ∈ ℝ`,

`φ(x) = ∑_{k=0}^{2N-1} c_k φ(2x - k)` (`Daubechies.scalingFun_refine`).

On the Fourier side it is the identity `Φ(2ξ) = m_0(ξ) Φ(ξ) = (1/2) ∑_k c_k e^(-2πikξ) Φ(ξ)`
(`Daubechies.symbolProduct_two_mul_eq_sum`). The dilation rule gives `φ(x) = 2 𝓕⁻[Φ(2 ·)](2x)`
(`Daubechies.scalingFun_eq_two_mul_fourierInv`), the inverse transform is linear on the
integrable summands `(c_k/2) e^(-2πikξ) Φ(ξ)` (`Daubechies.integrable_expFreq_mul`), and the
modulation rule `𝓕⁻[e^(-2πia ·) f](y) = 𝓕⁻ f(y - a)` (`Daubechies.fourierInv_expFreq_mul_apply`)
turns the `k`-th summand into `(c_k/2) φ(2x - k)`.

**The scaling function is real.** `Φ(-ξ) = conj Φ(ξ)` (`Daubechies.symbolProduct_neg`), so
`conj φ(x) = 𝓕[conj ∘ Φ](x) = 𝓕[Φ(-·)](x) = 𝓕⁻ Φ(x) = φ(x)` (`Daubechies.conj_scalingFun`);
hence `φ(x)` has imaginary part `0` (`Daubechies.im_scalingFun`) and equals its real part
(`Daubechies.ofReal_re_scalingFun`).
-/

@[expose] public section

open Filter MeasureTheory
open scoped Real FourierTransform ComplexConjugate

namespace Daubechies

/-! ### Modulation by `e^(-2πiaξ)` -/

/-- `e^(-2πiaξ) = exp(2π(-a)ξ i)`, the form of the exponential in the modulation rule
`Real.fourierInv_exp_mul_apply`. -/
theorem expFreq_mul_eq_exp (a ξ : ℝ) :
    expFreq (a * ξ) = Complex.exp (2 * π * ((-a : ℝ) : ℂ) * ξ * Complex.I) := by
  rw [expFreq]
  congr 1
  push_cast
  ring

/-- **Modulation by `e^(-2πiaξ)` is translation by `a`** for the inverse Fourier transform:
`𝓕⁻[ξ ↦ e^(-2πiaξ) f(ξ)](x) = 𝓕⁻ f(x - a)` for every `f : ℝ → ℂ` and all real `a`, `x`
(`Real.fourierInv_exp_mul_apply` with `b = -a`). -/
theorem fourierInv_expFreq_mul_apply (f : ℝ → ℂ) (a x : ℝ) :
    𝓕⁻ (fun ξ => expFreq (a * ξ) * f ξ) x = 𝓕⁻ f (x - a) := by
  simp_rw [expFreq_mul_eq_exp]
  rw [Real.fourierInv_exp_mul_apply, sub_eq_add_neg]

/-- An integrable `f : ℝ → ℂ` stays integrable after multiplication by `e^(-2πiaξ)`, a continuous
function of modulus `1` (Mathlib's `MeasureTheory.Integrable.bdd_mul`). -/
theorem integrable_expFreq_mul {f : ℝ → ℂ} (hf : Integrable f) (a : ℝ) :
    Integrable (fun ξ => expFreq (a * ξ) * f ξ) :=
  hf.bdd_mul (c := 1)
    (continuous_expFreq.comp (continuous_const.mul continuous_id)).aestronglyMeasurable
    (Eventually.of_forall fun ξ => (norm_expFreq (a * ξ)).le)

/-! ### The scaling function -/

variable {N : ℕ} (m : Mask N)

/-- **The scaling function** of a Daubechies mask: the inverse Fourier transform
`φ(x) = 𝓕⁻ Φ(x) = ∫ Φ(ξ) e^(2πixξ) dξ` of the symbol product `Φ` (`Daubechies.symbolProduct`).
It is defined for every mask; for order `N ≥ 2` the symbol product is integrable, and then `φ`
is continuous (`Daubechies.continuous_scalingFun`) and satisfies the refinement equation
(`Daubechies.scalingFun_refine`). -/
noncomputable def scalingFun : ℝ → ℂ := 𝓕⁻ (symbolProduct m)

/-- **The scaling function as an integral**: `φ(x) = ∫ e^(2πixξ) Φ(ξ) dξ` for every `x ∈ ℝ`
(Mathlib's `Real.fourierInv_eq'`). -/
theorem scalingFun_eq_integral (x : ℝ) :
    scalingFun m x = ∫ ξ : ℝ, Complex.exp (2 * π * x * ξ * Complex.I) * symbolProduct m ξ := by
  rw [scalingFun, Real.fourierInv_eq']
  congr 1 with ξ
  rw [Real.inner_apply, smul_eq_mul]
  congr 2
  push_cast
  ring

/-- **The scaling function is continuous** for `N ≥ 2`: the inverse Fourier transform of the
integrable function `Φ` (`Daubechies.integrable_symbolProduct`) is continuous
(`Real.continuous_fourierInv_of_integrable`). -/
theorem continuous_scalingFun (hN : 2 ≤ N) : Continuous (scalingFun m) :=
  Real.continuous_fourierInv_of_integrable (integrable_symbolProduct m hN)

/-- **The uniform bound** `|φ(x)| ≤ ∫ |Φ(ξ)| dξ` for every `x ∈ ℝ`
(`Real.norm_fourierInv_le_integral_norm`). For `N ≥ 2` the right side is finite
(`Daubechies.integrable_symbolProduct`); the bound holds for every order, since Lean assigns
the value `0` to the integral of a non-integrable function. -/
theorem norm_scalingFun_le (x : ℝ) : ‖scalingFun m x‖ ≤ ∫ ξ, ‖symbolProduct m ξ‖ :=
  Real.norm_fourierInv_le_integral_norm _ x

/-! ### The refinement equation -/

/-- **The refinement identity on the Fourier side**:
`Φ(2ξ) = m_0(ξ) Φ(ξ) = ∑_{k<2N} (c_k/2) e^(-2πikξ) Φ(ξ)` for every `ξ ∈ ℝ`
(`Daubechies.symbolProduct_two_mul` and `Daubechies.symbol_eq_sum`). -/
theorem symbolProduct_two_mul_eq_sum (ξ : ℝ) :
    symbolProduct m (2 * ξ) = ∑ k ∈ Finset.range (2 * N),
      (coeff m k : ℂ) / 2 * (expFreq (k * ξ) * symbolProduct m ξ) := by
  rw [symbolProduct_two_mul, symbol_eq_sum, Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expFreq_pow]
  ring

/-- **The dilation step**: `φ(x) = 2 𝓕⁻[ξ ↦ Φ(2ξ)](2x)` for every `x ∈ ℝ`, the dilation rule
`𝓕⁻[f(2 ·)](y) = 𝓕⁻ f(y/2)/2` (`Real.fourierInv_comp_mul_left_apply`) at `y = 2x`. -/
theorem scalingFun_eq_two_mul_fourierInv (x : ℝ) :
    scalingFun m x = 2 * 𝓕⁻ (fun ξ => symbolProduct m (2 * ξ)) (2 * x) := by
  rw [Real.fourierInv_comp_mul_left_apply (symbolProduct m) two_pos (2 * x),
    mul_div_cancel_left₀ x two_ne_zero, scalingFun]
  push_cast
  rw [← mul_assoc, mul_inv_cancel₀ two_ne_zero, one_mul]

/-- **The refinement equation** `φ(x) = ∑_{k=0}^{2N-1} c_k φ(2x - k)` for every `x ∈ ℝ` and every
mask of order `N ≥ 2`. By the dilation step (`Daubechies.scalingFun_eq_two_mul_fourierInv`) and
the Fourier-side identity `Φ(2ξ) = ∑_k (c_k/2) e^(-2πikξ) Φ(ξ)`
(`Daubechies.symbolProduct_two_mul_eq_sum`),
`φ(x) = 2 𝓕⁻[∑_k (c_k/2) e^(-2πik ·) Φ](2x) = ∑_k c_k 𝓕⁻[e^(-2πik ·) Φ](2x) = ∑_k c_k φ(2x - k)`:
the inverse transform is linear on the integrable summands (`Φ ∈ L¹` for `N ≥ 2`,
`Daubechies.integrable_symbolProduct`), and modulation by `e^(-2πikξ)` is translation by `k`
(`Daubechies.fourierInv_expFreq_mul_apply`). -/
theorem scalingFun_refine (hN : 2 ≤ N) (x : ℝ) :
    scalingFun m x =
      ∑ k ∈ Finset.range (2 * N), (coeff m k : ℂ) * scalingFun m (2 * x - k) := by
  have hΦ := integrable_symbolProduct m hN
  rw [scalingFun_eq_two_mul_fourierInv, funext (symbolProduct_two_mul_eq_sum m),
    Real.fourierInv_sum_apply, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun k _ => ?_
    rw [Real.fourierInv_const_mul_apply, fourierInv_expFreq_mul_apply, scalingFun]
    ring
  · intro k _
    exact (integrable_expFreq_mul hΦ k).const_mul _

/-! ### The scaling function is real -/

/-- **The scaling function is real**: `conj φ(x) = φ(x)` for every `x ∈ ℝ`. Conjugation turns the
inverse transform into the transform of the conjugate (`Real.conj_fourierInv`),
`conj Φ(ξ) = Φ(-ξ)` (`Daubechies.symbolProduct_neg`), and `𝓕[Φ(-·)] = 𝓕⁻ Φ` (Mathlib's
`Real.fourierInv_eq_fourier_comp_neg`). -/
theorem conj_scalingFun (x : ℝ) : conj (scalingFun m x) = scalingFun m x := by
  have h : (fun ξ => conj (symbolProduct m ξ)) = fun ξ => symbolProduct m (-ξ) :=
    funext fun ξ => (symbolProduct_neg m ξ).symm
  rw [scalingFun, Real.conj_fourierInv, h, Real.fourierInv_eq_fourier_comp_neg]

/-- The imaginary part of `φ(x)` is `0`, for every `x ∈ ℝ`. -/
theorem im_scalingFun (x : ℝ) : (scalingFun m x).im = 0 :=
  Complex.conj_eq_iff_im.1 (conj_scalingFun m x)

/-- `φ(x)` equals its real part: `Re φ(x) = φ(x)` as complex numbers, for every `x ∈ ℝ`. -/
theorem ofReal_re_scalingFun (x : ℝ) : ((scalingFun m x).re : ℂ) = scalingFun m x :=
  Complex.conj_eq_iff_re.1 (conj_scalingFun m x)

end Daubechies
