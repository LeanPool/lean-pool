/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Cascade
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.FilterIdentities

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Orthonormality of the integer translates of the scaling function

For a Daubechies mask of order `N ≥ 2` with symbol `m_0` (`Daubechies.symbol`), symbol product
`Φ(ξ) = ∏_{j ≥ 0} m_0(ξ/2^(j+1))` (`Daubechies.symbolProduct`) and scaling function `φ = 𝓕⁻ Φ`
(`Daubechies.scalingFun`), this file proves that the integer translates of `φ` are orthonormal:

`∫ φ(x - k) conj φ(x - l) dx = δ_(kl)` for all `k, l ∈ ℤ`
(`Daubechies.integral_scalingFun_translate_mul_conj_translate`), where `δ_(kl)` is `1` for `k = l`
and `0` otherwise.

* **Truncated products.** The functions
  `Φ_n(ξ) = ∏_{j<n} m_0(ξ/2^(j+1)) · 1_[-2^n/2, 2^n/2)(ξ)` (`Daubechies.truncProduct`) satisfy
  `Φ_0 = 1_[-1/2, 1/2)` and `Φ_(n+1)(ξ) = m_0(ξ/2) Φ_n(ξ/2)` (`Daubechies.truncProduct_succ`).
* **The integral identity.** For every continuous `1`-periodic `w : ℝ → ℂ` and every `n`,
  `∫ w(ξ) |Φ_n(ξ)|² dξ = ∫_0^1 w(ξ) dξ` (`Daubechies.integral_periodic_mul_normSq_truncProduct`).
  The proof is an induction on `n`. For `n = 0` the left side is the integral of `w` over an
  interval of length `1`. For the step, the substitution `ξ = 2ζ` gives
  `2 ∫ w(2ζ) |m_0(ζ)|² |Φ_n(ζ)|² dζ`; the function `ζ ↦ w(2ζ) |m_0(ζ)|²` is continuous and
  `1`-periodic, so by the induction hypothesis this is `2 ∫_0^1 w(2ζ) |m_0(ζ)|² dζ`. The two halves
  of `[0, 1]`, the periodicity of `w` and the quadrature mirror filter identity
  `|m_0(ζ)|² + |m_0(ζ + 1/2)|² = 1` (`Daubechies.qmf`) reduce it to `2 ∫_0^(1/2) w(2ζ) dζ`, which
  is `∫_0^1 w` (`Daubechies.two_mul_intervalIntegral_comp_two_mul_mul_normSq_symbol`).
* **The limit.** With `κ > 0` a lower bound of `|Φ|` on `[-1/2, 1/2]`, `|Φ_n| ≤ |Φ|/κ`
  (`Daubechies.norm_truncProduct_le`), since `Φ(ξ) = Φ_n(ξ) Φ(ξ/2^n)` for `ξ ∈ [-2^n/2, 2^n/2)`,
  and `Φ_n → Φ` pointwise (`Daubechies.tendsto_truncProduct`). As `|Φ|²` is integrable, dominated
  convergence gives `∫ w(ξ) |Φ(ξ)|² dξ = ∫_0^1 w(ξ) dξ`
  (`Daubechies.integral_periodic_mul_normSq_symbolProduct`). For `w(ξ) = e^(-2πikξ)` this says
  `∫ |Φ(ξ)|² e^(-2πikξ) dξ = δ_(k0)` for `k ∈ ℤ`
  (`Daubechies.integral_normSq_symbolProduct_mul_expFreq`).
* **Orthonormality.** Parseval's identity for integrable functions with integrable transforms
  (`Real.integral_mul_conj_eq_integral_fourier`), `𝓕 φ = Φ` (`Daubechies.fourier_scalingFun`) and
  the translation rule `𝓕[φ(· - k)](ξ) = e^(-2πikξ) Φ(ξ)` (`Real.fourier_comp_sub_right_apply`)
  give `∫ φ(x - k) conj φ(x) dx = ∫ e^(-2πikξ) |Φ(ξ)|² dξ = δ_(k0)`
  (`Daubechies.integral_scalingFun_translate_mul_conj`). The substitution `x ↦ x + l` gives the
  form for two translates, and since `φ` is real, also `∫ φ(x - k) φ(x - l) dx = δ_(kl)`
  (`Daubechies.integral_scalingFun_translate_mul_translate`).
-/

@[expose] public section

open Filter MeasureTheory Topology
open scoped Real FourierTransform ComplexConjugate

namespace Daubechies

/-! ### Substitutions -/

/-- **Splitting a period into two halves**: `∫_0^1 g(ζ) dζ = ∫_0^(1/2) (g(ζ) + g(ζ + 1/2)) dζ`
for every continuous `g : ℝ → ℂ`. The integral over `[1/2, 1]` is the integral of `g(· + 1/2)`
over `[0, 1/2]` (Mathlib's `intervalIntegral.integral_comp_add_right`). -/
theorem intervalIntegral_zero_one_eq_add_half {g : ℝ → ℂ} (hg : Continuous g) :
    ∫ ζ in (0 : ℝ)..1, g ζ = ∫ ζ in (0 : ℝ)..1 / 2, (g ζ + g (ζ + 1 / 2)) := by
  have hg' : Continuous fun ζ => g (ζ + 1 / 2) := hg.comp (continuous_id.add continuous_const)
  rw [intervalIntegral.integral_add (hg.intervalIntegrable _ _) (hg'.intervalIntegrable _ _),
    intervalIntegral.integral_comp_add_right g (1 / 2), zero_add, add_halves,
    intervalIntegral.integral_add_adjacent_intervals (hg.intervalIntegrable _ _)
      (hg.intervalIntegrable _ _)]

/-- **The doubling substitution on a half period**: `2 ∫_0^(1/2) w(2ζ) dζ = ∫_0^1 w(ξ) dξ` for
every `w : ℝ → ℂ`, by the substitution `ξ = 2ζ` (Mathlib's
`intervalIntegral.smul_integral_comp_mul_left`). -/
theorem two_mul_intervalIntegral_comp_two_mul (w : ℝ → ℂ) :
    2 * ∫ ζ in (0 : ℝ)..1 / 2, w (2 * ζ) = ∫ ξ in (0 : ℝ)..1, w ξ := by
  have h := intervalIntegral.smul_integral_comp_mul_left w (2 : ℝ) (a := 0) (b := 1 / 2)
  rw [mul_zero, mul_one_div_cancel two_ne_zero, Complex.real_smul] at h
  exact_mod_cast h

/-- **The doubling substitution on the line**: `∫ F(ξ/2) dξ = 2 ∫ F(ζ) dζ` for every
`F : ℝ → ℂ`, by the substitution `ξ = 2ζ` (Mathlib's `MeasureTheory.Measure.integral_comp_div`).
The identity holds for every `F`, integrable or not: Lean assigns the value `0` to the integral
of a non-integrable function, on both sides. -/
theorem integral_comp_div_two (F : ℝ → ℂ) : ∫ ξ, F (ξ / 2) = 2 * ∫ ζ, F ζ := by
  rw [Measure.integral_comp_div, abs_two, Complex.real_smul]
  norm_num

variable {N : ℕ} (m : Mask N)

/-- **Halving against the squared symbol**: for every continuous `1`-periodic `w : ℝ → ℂ`,
`2 ∫_0^1 w(2ζ) |m_0(ζ)|² dζ = ∫_0^1 w(ξ) dξ`. Split `[0, 1]` into its two halves
(`Daubechies.intervalIntegral_zero_one_eq_add_half`); since `w(2ζ + 1) = w(2ζ)`, the integrand
on `[0, 1/2]` becomes `w(2ζ) (|m_0(ζ)|² + |m_0(ζ + 1/2)|²) = w(2ζ)` by the quadrature mirror
filter identity (`Daubechies.qmf`), and `2 ∫_0^(1/2) w(2ζ) dζ = ∫_0^1 w`
(`Daubechies.two_mul_intervalIntegral_comp_two_mul`). -/
theorem two_mul_intervalIntegral_comp_two_mul_mul_normSq_symbol {w : ℝ → ℂ}
    (hw : Continuous w) (hper : Function.Periodic w 1) :
    2 * ∫ ζ in (0 : ℝ)..1, w (2 * ζ) * ((‖symbol m ζ‖ ^ 2 : ℝ) : ℂ) =
      ∫ ξ in (0 : ℝ)..1, w ξ := by
  have hs := continuous_symbol m
  have hc : Continuous fun ζ => w (2 * ζ) * ((‖symbol m ζ‖ ^ 2 : ℝ) : ℂ) := by fun_prop
  rw [intervalIntegral_zero_one_eq_add_half hc, ← two_mul_intervalIntegral_comp_two_mul w]
  congr 1
  refine intervalIntegral.integral_congr fun ζ _ => ?_
  rw [show 2 * (ζ + 1 / 2) = 2 * ζ + 1 by ring, hper (2 * ζ), ← mul_add, ← Complex.ofReal_add,
    qmf m ζ, Complex.ofReal_one, mul_one]

/-- For a `1`-periodic `w : ℝ → ℂ`, the function `ζ ↦ w(2ζ) |m_0(ζ)|²` is `1`-periodic again:
`w(2ζ + 2) = w(2ζ)`, and `m_0` has period `1` (`Daubechies.symbol_periodic`). -/
theorem periodic_comp_two_mul_mul_normSq_symbol {w : ℝ → ℂ} (hper : Function.Periodic w 1) :
    Function.Periodic (fun ζ => w (2 * ζ) * ((‖symbol m ζ‖ ^ 2 : ℝ) : ℂ)) 1 := fun ζ => by
  simp only
  rw [show 2 * (ζ + 1) = 2 * ζ + 1 + 1 by ring, hper, hper, symbol_periodic m ζ]

/-! ### The truncated symbol products -/

/-- **The truncated symbol products**
`Φ_n(ξ) = ∏_{j<n} m_0(ξ/2^(j+1)) · 1_[-2^n/2, 2^n/2)(ξ)`: the first `n` factors of the symbol
product `Φ`, cut off outside the interval `[-2^n/2, 2^n/2)`. They satisfy
`Φ_(n+1)(ξ) = m_0(ξ/2) Φ_n(ξ/2)` (`Daubechies.truncProduct_succ`), converge to `Φ` pointwise
(`Daubechies.tendsto_truncProduct`), and `∫ w |Φ_n|² = ∫_0^1 w` for every continuous `1`-periodic
`w` (`Daubechies.integral_periodic_mul_normSq_truncProduct`). -/
noncomputable def truncProduct (n : ℕ) (ξ : ℝ) : ℂ :=
  (∏ j ∈ Finset.range n, symbol m (ξ / 2 ^ (j + 1))) *
    (Set.Ico (-(2 ^ n / 2 : ℝ)) (2 ^ n / 2)).indicator 1 ξ

/-- `Φ_0 = 1_[-1/2, 1/2)`, the indicator function of `[-1/2, 1/2)`: the product is empty. -/
theorem truncProduct_zero (ξ : ℝ) :
    truncProduct m 0 ξ = (Set.Ico (-(1 / 2 : ℝ)) (1 / 2)).indicator 1 ξ := by
  rw [truncProduct, Finset.prod_range_zero, one_mul, pow_zero]

/-- The cut-off intervals double from one level to the next:
`ξ ∈ [-2^(n+1)/2, 2^(n+1)/2)` if and only if `ξ/2 ∈ [-2^n/2, 2^n/2)`. -/
theorem mem_Ico_two_pow_succ_iff (n : ℕ) (ξ : ℝ) :
    ξ ∈ Set.Ico (-(2 ^ (n + 1) / 2 : ℝ)) (2 ^ (n + 1) / 2) ↔
      ξ / 2 ∈ Set.Ico (-(2 ^ n / 2 : ℝ)) (2 ^ n / 2) := by
  simp only [Set.mem_Ico, pow_succ]
  constructor <;> rintro ⟨h1, h2⟩ <;> constructor <;> linarith

/-- **The recursion of the truncated products**: `Φ_(n+1)(ξ) = m_0(ξ/2) Φ_n(ξ/2)` for every `n`
and every `ξ ∈ ℝ`. Split off the first factor of the product
(`Daubechies.prod_range_succ_symbol`); `ξ` lies in the cut-off interval of level `n + 1` exactly
when `ξ/2` lies in the one of level `n` (`Daubechies.mem_Ico_two_pow_succ_iff`). -/
theorem truncProduct_succ (n : ℕ) (ξ : ℝ) :
    truncProduct m (n + 1) ξ = symbol m (ξ / 2) * truncProduct m n (ξ / 2) := by
  have h : (Set.Ico (-(2 ^ (n + 1) / 2 : ℝ)) (2 ^ (n + 1) / 2)).indicator (1 : ℝ → ℂ) ξ =
      (Set.Ico (-(2 ^ n / 2 : ℝ)) (2 ^ n / 2)).indicator 1 (ξ / 2) := by
    by_cases hξ : ξ / 2 ∈ Set.Ico (-(2 ^ n / 2 : ℝ)) (2 ^ n / 2)
    · rw [Set.indicator_of_mem ((mem_Ico_two_pow_succ_iff n ξ).2 hξ), Set.indicator_of_mem hξ,
        Pi.one_apply, Pi.one_apply]
    · rw [Set.indicator_of_notMem (fun h' => hξ ((mem_Ico_two_pow_succ_iff n ξ).1 h')),
        Set.indicator_of_notMem hξ]
  rw [truncProduct, truncProduct, prod_range_succ_symbol, h, mul_assoc]

/-- The recursion for the squared moduli:
`|Φ_(n+1)(ξ)|² = |m_0(ξ/2)|² |Φ_n(ξ/2)|²` (`Daubechies.truncProduct_succ`). -/
theorem normSq_truncProduct_succ (n : ℕ) (ξ : ℝ) :
    ‖truncProduct m (n + 1) ξ‖ ^ 2 =
      ‖symbol m (ξ / 2)‖ ^ 2 * ‖truncProduct m n (ξ / 2)‖ ^ 2 := by
  rw [truncProduct_succ, norm_mul, mul_pow]

/-- The truncated products are measurable: a continuous function times the indicator function
of an interval. -/
theorem measurable_truncProduct (n : ℕ) : Measurable (truncProduct m n) := by
  have h : Continuous fun ξ : ℝ => ∏ j ∈ Finset.range n, symbol m (ξ / 2 ^ (j + 1)) :=
    continuous_finsetProd _ fun j _ => (continuous_symbol m).comp (continuous_id.div_const _)
  exact h.measurable.mul (measurable_one.indicator measurableSet_Ico)

/-! ### The integral identity for the truncated products -/

/-- **The integral identity for `n = 0`**: `∫ w(ξ) |Φ_0(ξ)|² dξ = ∫_0^1 w(ξ) dξ` for every
`1`-periodic `w : ℝ → ℂ`. Since `|Φ_0|² = 1_[-1/2, 1/2)`, the left side is `∫_(-1/2)^(1/2) w`,
and the integral of a `1`-periodic function is the same over every interval of length `1`
(Mathlib's `Function.Periodic.intervalIntegral_add_eq`). -/
theorem integral_mul_normSq_truncProduct_zero {w : ℝ → ℂ} (hper : Function.Periodic w 1) :
    ∫ ξ, w ξ * ((‖truncProduct m 0 ξ‖ ^ 2 : ℝ) : ℂ) = ∫ ξ in (0 : ℝ)..1, w ξ := by
  have h : ∀ ξ, w ξ * ((‖truncProduct m 0 ξ‖ ^ 2 : ℝ) : ℂ) =
      (Set.Ico (-(1 / 2 : ℝ)) (1 / 2)).indicator w ξ := fun ξ => by
    rw [truncProduct_zero]
    by_cases hξ : ξ ∈ Set.Ico (-(1 / 2 : ℝ)) (1 / 2)
    · rw [Set.indicator_of_mem hξ, Set.indicator_of_mem hξ]
      simp
    · rw [Set.indicator_of_notMem hξ, Set.indicator_of_notMem hξ]
      simp
  simp_rw [h]
  rw [integral_indicator measurableSet_Ico, integral_Ico_eq_integral_Ioc,
    ← intervalIntegral.integral_of_le (by norm_num)]
  have h1 := hper.intervalIntegral_add_eq (-(1 / 2)) 0
  rwa [show -(1 / 2 : ℝ) + 1 = 1 / 2 by norm_num, zero_add] at h1

/-- **The substitution step**: for every `w : ℝ → ℂ` and every `n`,
`∫ w(ξ) |Φ_(n+1)(ξ)|² dξ = 2 ∫ w(2ζ) |m_0(ζ)|² |Φ_n(ζ)|² dζ`, by the recursion
`|Φ_(n+1)(ξ)|² = |m_0(ξ/2)|² |Φ_n(ξ/2)|²` (`Daubechies.normSq_truncProduct_succ`) and the
substitution `ξ = 2ζ` (`Daubechies.integral_comp_div_two`). -/
theorem integral_mul_normSq_truncProduct_succ (w : ℝ → ℂ) (n : ℕ) :
    ∫ ξ, w ξ * ((‖truncProduct m (n + 1) ξ‖ ^ 2 : ℝ) : ℂ) =
      2 * ∫ ζ, w (2 * ζ) * ((‖symbol m ζ‖ ^ 2 : ℝ) : ℂ) *
        ((‖truncProduct m n ζ‖ ^ 2 : ℝ) : ℂ) := by
  rw [← integral_comp_div_two]
  congr 1 with ξ
  rw [show 2 * (ξ / 2) = ξ by ring, normSq_truncProduct_succ, Complex.ofReal_mul, mul_assoc]

/-- **The integral identity for the truncated products**: for every continuous `1`-periodic
`w : ℝ → ℂ` and every `n`, `∫ w(ξ) |Φ_n(ξ)|² dξ = ∫_0^1 w(ξ) dξ`. Induction on `n`, for all such
`w` at once. The case `n = 0` is `Daubechies.integral_mul_normSq_truncProduct_zero`. For the step,
the substitution `ξ = 2ζ` (`Daubechies.integral_mul_normSq_truncProduct_succ`) and the induction
hypothesis for the continuous `1`-periodic function `ζ ↦ w(2ζ) |m_0(ζ)|²`
(`Daubechies.periodic_comp_two_mul_mul_normSq_symbol`) give `2 ∫_0^1 w(2ζ) |m_0(ζ)|² dζ`, which
is `∫_0^1 w` (`Daubechies.two_mul_intervalIntegral_comp_two_mul_mul_normSq_symbol`). -/
theorem integral_periodic_mul_normSq_truncProduct {w : ℝ → ℂ} (hw : Continuous w)
    (hper : Function.Periodic w 1) (n : ℕ) :
    ∫ ξ, w ξ * ((‖truncProduct m n ξ‖ ^ 2 : ℝ) : ℂ) = ∫ ξ in (0 : ℝ)..1, w ξ := by
  induction n generalizing w with
  | zero => exact integral_mul_normSq_truncProduct_zero m hper
  | succ n ih =>
    have hs := continuous_symbol m
    have hc : Continuous fun ζ => w (2 * ζ) * ((‖symbol m ζ‖ ^ 2 : ℝ) : ℂ) := by fun_prop
    rw [integral_mul_normSq_truncProduct_succ,
      ih hc (periodic_comp_two_mul_mul_normSq_symbol m hper),
      two_mul_intervalIntegral_comp_two_mul_mul_normSq_symbol m hw hper]

/-! ### Convergence of the truncated products -/

/-- **The truncated products are dominated by the symbol product**: if `κ > 0` and
`κ ≤ |Φ(ξ)|` for all `|ξ| ≤ 1/2` (such a `κ` exists by
`Daubechies.exists_pos_le_norm_symbolProduct`), then `|Φ_n(ξ)| ≤ |Φ(ξ)|/κ` for every `n` and
every `ξ ∈ ℝ`. Outside `[-2^n/2, 2^n/2)` the left side is `0`. Inside, `|ξ/2^n| ≤ 1/2` and
`Φ(ξ) = ∏_{j<n} m_0(ξ/2^(j+1)) · Φ(ξ/2^n)` (`Daubechies.symbolProduct_eq_prod_mul`), so
`|Φ(ξ)| ≥ |Φ_n(ξ)| κ`. -/
theorem norm_truncProduct_le {κ : ℝ} (hκ : 0 < κ)
    (h : ∀ ξ : ℝ, |ξ| ≤ 1 / 2 → κ ≤ ‖symbolProduct m ξ‖) (n : ℕ) (ξ : ℝ) :
    ‖truncProduct m n ξ‖ ≤ ‖symbolProduct m ξ‖ / κ := by
  by_cases hξ : ξ ∈ Set.Ico (-(2 ^ n / 2 : ℝ)) (2 ^ n / 2)
  · have h1 : |ξ / 2 ^ n| ≤ 1 / 2 := by
      rw [abs_div, abs_of_pos (by positivity : (0 : ℝ) < 2 ^ n), div_le_iff₀ (by positivity),
        abs_le]
      constructor <;> linarith [hξ.1, hξ.2]
    rw [truncProduct, Set.indicator_of_mem hξ, Pi.one_apply, mul_one, le_div_iff₀ hκ,
      symbolProduct_eq_prod_mul m ξ n, norm_mul]
    exact mul_le_mul_of_nonneg_left (h _ h1) (norm_nonneg _)
  · rw [truncProduct, Set.indicator_of_notMem hξ, mul_zero, norm_zero]
    exact div_nonneg (norm_nonneg _) hκ.le

/-- Every `ξ ∈ ℝ` lies in the cut-off interval `[-2^n/2, 2^n/2)` for all sufficiently large `n`,
since `2^n → ∞`. -/
theorem eventually_mem_Ico_two_pow (ξ : ℝ) :
    ∀ᶠ n : ℕ in atTop, ξ ∈ Set.Ico (-(2 ^ n / 2 : ℝ)) (2 ^ n / 2) := by
  have h := tendsto_pow_atTop_atTop_of_one_lt (one_lt_two : (1 : ℝ) < 2)
  filter_upwards [h.eventually_gt_atTop (2 * |ξ|)] with n hn
  constructor <;> linarith [neg_abs_le ξ, le_abs_self ξ]

/-- **The truncated products converge to the symbol product**: `Φ_n(ξ) → Φ(ξ)` as `n → ∞`, for
every `ξ ∈ ℝ`. For large `n` the cut-off factor at `ξ` is `1`
(`Daubechies.eventually_mem_Ico_two_pow`), and the partial products converge to `Φ(ξ)`
(`Daubechies.tendsto_prod_symbol`). -/
theorem tendsto_truncProduct (ξ : ℝ) :
    Tendsto (fun n => truncProduct m n ξ) atTop (𝓝 (symbolProduct m ξ)) := by
  refine (tendsto_prod_symbol m ξ).congr' ?_
  filter_upwards [eventually_mem_Ico_two_pow ξ] with n hn
  rw [truncProduct, Set.indicator_of_mem hn, Pi.one_apply, mul_one]

/-! ### The integral identity for the symbol product -/

/-- **`|Φ|²` is integrable** for every mask of order `N ≥ 2`, since `Φ ∈ L²`
(`Daubechies.memLp_symbolProduct_two`). -/
theorem integrable_normSq_symbolProduct (hN : 2 ≤ N) :
    Integrable (fun ξ => ‖symbolProduct m ξ‖ ^ 2) :=
  (memLp_two_iff_integrable_sq_norm (continuous_symbolProduct m).aestronglyMeasurable).1
    (memLp_symbolProduct_two m hN)

/-- **The integral identity for the symbol product**: for a mask of order `N ≥ 2` and every
continuous `1`-periodic `w : ℝ → ℂ`, `∫ w(ξ) |Φ(ξ)|² dξ = ∫_0^1 w(ξ) dξ`. The integrands
`w |Φ_n|²` converge pointwise to `w |Φ|²` (`Daubechies.tendsto_truncProduct`) and are bounded by
`(B/κ²) |Φ|²` (`Daubechies.norm_truncProduct_le`), where `B` bounds the continuous periodic
function `|w|` (Mathlib's `Function.Periodic.isBounded_of_continuous`) and `κ > 0` bounds `|Φ|`
from below on `[-1/2, 1/2]`; this bound is integrable
(`Daubechies.integrable_normSq_symbolProduct`). Dominated convergence (Mathlib's
`MeasureTheory.tendsto_integral_of_dominated_convergence`) and `∫ w |Φ_n|² = ∫_0^1 w` for every
`n` (`Daubechies.integral_periodic_mul_normSq_truncProduct`) give the identity. -/
theorem integral_periodic_mul_normSq_symbolProduct (hN : 2 ≤ N) {w : ℝ → ℂ}
    (hw : Continuous w) (hper : Function.Periodic w 1) :
    ∫ ξ, w ξ * ((‖symbolProduct m ξ‖ ^ 2 : ℝ) : ℂ) = ∫ ξ in (0 : ℝ)..1, w ξ := by
  obtain ⟨κ, hκ, hκle⟩ := exists_pos_le_norm_symbolProduct m
  obtain ⟨B, hB⟩ := (hper.isBounded_of_continuous one_ne_zero hw).exists_norm_le
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB _ (Set.mem_range_self 0))
  have hlim : Tendsto (fun n => ∫ ξ, w ξ * ((‖truncProduct m n ξ‖ ^ 2 : ℝ) : ℂ)) atTop
      (𝓝 (∫ ξ, w ξ * ((‖symbolProduct m ξ‖ ^ 2 : ℝ) : ℂ))) := by
    refine tendsto_integral_of_dominated_convergence
      (fun ξ => B / κ ^ 2 * ‖symbolProduct m ξ‖ ^ 2)
      (fun n => (hw.measurable.mul (Complex.measurable_ofReal.comp
        ((measurable_truncProduct m n).norm.pow_const 2))).aestronglyMeasurable)
      ((integrable_normSq_symbolProduct m hN).const_mul _)
      (fun n => Eventually.of_forall fun ξ => ?_)
      (Eventually.of_forall fun ξ =>
        (((tendsto_truncProduct m ξ).norm.pow 2).ofReal).const_mul (w ξ))
    rw [norm_mul, Complex.norm_real, Real.norm_of_nonneg (sq_nonneg _)]
    calc ‖w ξ‖ * ‖truncProduct m n ξ‖ ^ 2 ≤ B * (‖symbolProduct m ξ‖ / κ) ^ 2 :=
          mul_le_mul (hB _ (Set.mem_range_self ξ))
            (pow_le_pow_left₀ (norm_nonneg _) (norm_truncProduct_le m hκ hκle n ξ) 2)
            (sq_nonneg _) hB0
      _ = B / κ ^ 2 * ‖symbolProduct m ξ‖ ^ 2 := by ring
  simp only [integral_periodic_mul_normSq_truncProduct m hw hper] at hlim
  exact tendsto_nhds_unique hlim tendsto_const_nhds

/-! ### Orthonormality -/

/-- **The Fourier coefficients of `|Φ|²` at the integers**: for a mask of order `N ≥ 2` and every
`k ∈ ℤ`, `∫ |Φ(ξ)|² e^(-2πikξ) dξ` is `1` for `k = 0` and `0` otherwise. This is the integral
identity `Daubechies.integral_periodic_mul_normSq_symbolProduct` for `w(ξ) = e^(-2πikξ)`,
together with `∫_0^1 e^(-2πikξ) dξ = δ_(k0)` (`Daubechies.integral_expFreq_intCast_mul`). -/
theorem integral_normSq_symbolProduct_mul_expFreq (hN : 2 ≤ N) (k : ℤ) :
    ∫ ξ, ((‖symbolProduct m ξ‖ ^ 2 : ℝ) : ℂ) * expFreq (k * ξ) = if k = 0 then 1 else 0 := by
  have h := integral_periodic_mul_normSq_symbolProduct m hN (continuous_expFreq_mul (k : ℝ))
    (periodic_expFreq_intCast_mul k)
  rw [integral_expFreq_intCast_mul] at h
  rw [← h]
  congr 1 with ξ
  ring

/-- **Orthonormality of the integer translates of the scaling function**: for a mask of order
`N ≥ 2` and every `k ∈ ℤ`, `∫ φ(x - k) conj φ(x) dx` is `1` for `k = 0` and `0` otherwise.
Parseval's identity (`Real.integral_mul_conj_eq_integral_fourier`; `φ` is continuous and
integrable, with integrable transform `𝓕 φ = Φ` by `Daubechies.fourier_scalingFun`) and the
translation rule `𝓕[φ(· - k)](ξ) = e^(-2πikξ) Φ(ξ)` (`Real.fourier_comp_sub_right_apply`) turn the
integral into `∫ e^(-2πikξ) |Φ(ξ)|² dξ`, which is
`Daubechies.integral_normSq_symbolProduct_mul_expFreq`. -/
theorem integral_scalingFun_translate_mul_conj (hN : 2 ≤ N) (k : ℤ) :
    ∫ x, scalingFun m (x - k) * conj (scalingFun m x) = if k = 0 then 1 else 0 := by
  have hφ := integrable_scalingFun m hN
  have hF : Integrable (𝓕 (scalingFun m)) := by
    rw [fourier_scalingFun m hN]
    exact integrable_symbolProduct m hN
  rw [Real.integral_mul_conj_eq_integral_fourier (hφ.comp_sub_right (k : ℝ))
    (continuous_scalingFun m hN) hφ hF, ← integral_normSq_symbolProduct_mul_expFreq m hN k]
  congr 1 with ξ
  rw [Real.fourier_comp_sub_right_apply (scalingFun m) k ξ, fourier_scalingFun m hN, mul_assoc,
    Complex.mul_conj', ← Complex.ofReal_pow, mul_comm, expFreq]
  congr 2
  push_cast
  ring

/-- **Orthonormality of the integer translates, for two translates**: for a mask of order
`N ≥ 2` and all `k, l ∈ ℤ`, `∫ φ(x - k) conj φ(x - l) dx` is `1` for `k = l` and `0` otherwise.
The substitution `x ↦ x + l` (Mathlib's `MeasureTheory.integral_add_right_eq_self`) reduces it to
`Daubechies.integral_scalingFun_translate_mul_conj` for `k - l`. -/
theorem integral_scalingFun_translate_mul_conj_translate (hN : 2 ≤ N) (k l : ℤ) :
    ∫ x, scalingFun m (x - k) * conj (scalingFun m (x - l)) = if k = l then 1 else 0 := by
  rw [← integral_add_right_eq_self _ (l : ℝ)]
  have h : ∀ x : ℝ, scalingFun m (x + l - k) * conj (scalingFun m (x + l - l)) =
      scalingFun m (x - ((k - l : ℤ) : ℝ)) * conj (scalingFun m x) := fun x => by
    rw [add_sub_cancel_right, Int.cast_sub, show x + (l : ℝ) - k = x - (k - l) by ring]
  simp only [h, integral_scalingFun_translate_mul_conj m hN, sub_eq_zero]

/-- **Orthonormality of the integer translates, real form**: for a mask of order `N ≥ 2` and all
`k, l ∈ ℤ`, `∫ φ(x - k) φ(x - l) dx` is `1` for `k = l` and `0` otherwise, since `φ` is real
(`Daubechies.conj_scalingFun`). -/
theorem integral_scalingFun_translate_mul_translate (hN : 2 ≤ N) (k l : ℤ) :
    ∫ x, scalingFun m (x - k) * scalingFun m (x - l) = if k = l then 1 else 0 := by
  rw [← integral_scalingFun_translate_mul_conj_translate m hN k l]
  simp only [conj_scalingFun]

end Daubechies
