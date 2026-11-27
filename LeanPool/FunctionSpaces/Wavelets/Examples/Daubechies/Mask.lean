/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.DaubechiesPolynomial
public import Mathlib.Analysis.Calculus.ContDiff.Polynomial
public import Mathlib.Analysis.SpecialFunctions.ExpDeriv

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Daubechies masks

A **Daubechies mask of order `N`** (`Daubechies.Mask`) is given by a real polynomial `L` of
degree `< N` with `L(1) = 1` and `|L(e^(-2πiξ))|² = P(ξ)` for all `ξ ∈ ℝ`, where
`P(ξ) = P_N(sin²(πξ))` is the trigonometric Daubechies polynomial (`Daubechies.daubFun`). Every
mask has order `N ≥ 1` (`Daubechies.Mask.one_le`). From `L` one builds

* the **mask polynomial** `m(z) = ((1 + z)/2)^N L(z)` (`Daubechies.maskPoly`), with
  `deg m ≤ 2N - 1` (`Daubechies.natDegree_maskPoly_le`) and `(z + 1)^N ∣ m(z)`
  (`Daubechies.X_add_one_pow_dvd_maskPoly`);
* the **filter coefficients** `c_k = 2 [z^k] m(z)` for `k ∈ ℤ` (`Daubechies.coeff`), with
  `c_k = 0` for `k < 0` and for `k ≥ 2N` (`Daubechies.coeff_eq_zero`) and
  `∑_{k<2N} c_k = 2 m(1) = 2` (`Daubechies.sum_coeff`);
* the **symbol** `m_0(ξ) = m(e^(-2πiξ)) = (1/2) ∑_k c_k e^(-2πikξ)` (`Daubechies.symbol`,
  `Daubechies.symbol_eq_sum`), a smooth function of period `1` with `m_0(0) = 1`
  (`Daubechies.contDiff_symbol`, `Daubechies.symbol_periodic`, `Daubechies.symbol_zero`).

The point `z = e^(-2πiξ)` of the unit circle is `Daubechies.expFreq ξ`. There the factor
`(1 + z)/2` equals `e^(-πiξ) cos(πξ)` (`Daubechies.one_add_expFreq_div_two`), so

`|m_0(ξ)|² = cos(πξ)^(2N) P(ξ)` (`Daubechies.normSq_symbol`).

Together with the trigonometric Bézout identity `cos(πξ)^(2N) P(ξ) + sin(πξ)^(2N) P(ξ + 1/2) = 1`
(`Daubechies.daubFun_bezout`) this gives the **quadrature mirror filter identity**

`|m_0(ξ)|² + |m_0(ξ + 1/2)|² = 1` (`Daubechies.qmf`),

and hence `|m_0(ξ)| ≤ 1` for every `ξ` (`Daubechies.norm_symbol_le_one`). Since `P ≥ 1` and
`cos(πξ) > 0` for `|ξ| < 1/2`, the symbol has no zeros in `(-1/2, 1/2)`
(`Daubechies.symbol_ne_zero`), while `m_0(1/2 + n) = 0` for every `n ∈ ℤ`
(`Daubechies.symbol_half_add_int`), where `z = -1`. The mask polynomial has real coefficients,
so `m_0(-ξ) = conj (m_0(ξ))` (`Daubechies.symbol_neg`). Finally `m_0` is Lipschitz at `0`:
`|m_0(ξ) - 1| ≤ π ∑_{k<2N} k |c_k| · |ξ|` (`Daubechies.norm_symbol_sub_one_le`), where the
constant `π ∑_{k<2N} k |c_k|` is `Daubechies.symbolLip`. The bound follows from
`m_0(ξ) - 1 = (1/2) ∑_k c_k (e^(-2πikξ) - 1)` and `|e^(-2πikξ) - 1| ≤ 2πk|ξ|`.
-/

@[expose] public section

open Polynomial
open scoped Real ComplexConjugate

namespace Daubechies

/-! ### The point `e^(-2πiξ)` of the unit circle -/

/-- **The point `e^(-2πiξ)` of the unit circle.** The symbol of a mask is its mask polynomial
evaluated at `z = e^(-2πiξ)`; the sign of the exponent is the one of Mathlib's Fourier transform
`𝓕 f(ξ) = ∫ e^(-2πixξ) f(x) dx`. -/
noncomputable def expFreq (ξ : ℝ) : ℂ := Complex.exp (((-(2 * π * ξ)) : ℝ) * Complex.I)

/-- `|e^(-2πiξ)| = 1`. -/
@[simp]
theorem norm_expFreq (ξ : ℝ) : ‖expFreq ξ‖ = 1 :=
  Complex.norm_exp_ofReal_mul_I _

/-- `e^(-2πiξ) ≠ 0`. -/
theorem expFreq_ne_zero (ξ : ℝ) : expFreq ξ ≠ 0 :=
  Complex.exp_ne_zero _

/-- `e^(-2πiξ) = exp(cξ)` with the complex constant `c = -2πi`, the form in which `ξ` enters
linearly into the exponent. -/
theorem expFreq_eq_exp_mul (ξ : ℝ) : expFreq ξ = Complex.exp (-(2 * π * Complex.I) * ξ) := by
  rw [expFreq]
  congr 1
  push_cast
  ring

/-- The real part of `e^(-2πiξ)` is `cos(2πξ)`. -/
theorem expFreq_re (ξ : ℝ) : (expFreq ξ).re = Real.cos (2 * π * ξ) := by
  rw [expFreq, Complex.exp_ofReal_mul_I_re, Real.cos_neg]

/-- The imaginary part of `e^(-2πiξ)` is `-sin(2πξ)`. -/
theorem expFreq_im (ξ : ℝ) : (expFreq ξ).im = -Real.sin (2 * π * ξ) := by
  rw [expFreq, Complex.exp_ofReal_mul_I_im, Real.sin_neg]

/-- `e^(-2πi · 0) = 1`. -/
@[simp]
theorem expFreq_zero : expFreq 0 = 1 := by
  simp [expFreq]

/-- `e^(-2πi(ξ + η)) = e^(-2πiξ) e^(-2πiη)`. -/
theorem expFreq_add (ξ η : ℝ) : expFreq (ξ + η) = expFreq ξ * expFreq η := by
  rw [expFreq, expFreq, expFreq, ← Complex.exp_add]
  congr 1
  push_cast
  ring

/-- `(e^(-2πiξ))^k = e^(-2πikξ)` for every `k ∈ ℕ`. -/
theorem expFreq_pow (ξ : ℝ) (k : ℕ) : expFreq ξ ^ k = expFreq (k * ξ) := by
  rw [expFreq, expFreq, ← Complex.exp_nat_mul]
  congr 1
  push_cast
  ring

/-- `e^(-2πin) = 1` for every integer `n`. -/
theorem expFreq_intCast (n : ℤ) : expFreq n = 1 := by
  rw [expFreq, ← Complex.exp_int_mul_two_pi_mul_I (-n)]
  congr 1
  push_cast
  ring

/-- `e^(-2πi) = 1`. -/
theorem expFreq_one : expFreq 1 = 1 := by
  simpa using expFreq_intCast 1

/-- `ξ ↦ e^(-2πiξ)` has period `1`. -/
theorem expFreq_periodic : Function.Periodic expFreq 1 := fun ξ => by
  rw [expFreq_add, expFreq_one, mul_one]

/-- `e^(-2πi(1/2 + n)) = e^(-πi) = -1` for every integer `n`. -/
theorem expFreq_half_add_int (n : ℤ) : expFreq (1 / 2 + n) = -1 := by
  rw [expFreq_add, expFreq_intCast, mul_one, expFreq,
    show (((-(2 * π * (1 / 2))) : ℝ) : ℂ) * Complex.I = -(π * Complex.I) by push_cast; ring]
  exact Complex.exp_neg_pi_mul_I

/-- `conj (e^(-2πiξ)) = e^(2πiξ) = e^(-2πi(-ξ))`. -/
theorem conj_expFreq (ξ : ℝ) : conj (expFreq ξ) = expFreq (-ξ) := by
  rw [expFreq, expFreq, ← Complex.exp_conj, map_mul, Complex.conj_ofReal, Complex.conj_I]
  congr 1
  push_cast
  ring

/-- `ξ ↦ e^(-2πiξ)` is smooth: it is `C^n` for every `n`, including `n = ∞` and the analytic
case `n = ω`. -/
theorem contDiff_expFreq {n : WithTop ℕ∞} : ContDiff ℝ n expFreq :=
  Complex.contDiff_exp.comp ((Complex.ofRealCLM.contDiff.comp
    (contDiff_const.mul contDiff_id).neg).mul contDiff_const)

/-- `ξ ↦ e^(-2πiξ)` is continuous. -/
theorem continuous_expFreq : Continuous expFreq :=
  (contDiff_expFreq (n := 0)).continuous

/-- `|e^(-2πiξ) - 1| ≤ 2π|ξ|`, from Mathlib's `Real.norm_exp_I_mul_ofReal_sub_one_le`:
`|e^(ix) - 1| ≤ |x|` for real `x`. -/
theorem norm_expFreq_sub_one_le (ξ : ℝ) : ‖expFreq ξ - 1‖ ≤ 2 * π * |ξ| := by
  rw [expFreq, mul_comm]
  calc ‖Complex.exp (Complex.I * ((-(2 * π * ξ) : ℝ) : ℂ)) - 1‖ ≤ ‖(-(2 * π * ξ) : ℝ)‖ :=
        Real.norm_exp_I_mul_ofReal_sub_one_le
    _ = 2 * π * |ξ| := by
        rw [Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_two, abs_of_pos Real.pi_pos]

/-- `|e^(-2πikξ) - 1| ≤ 2πk|ξ|` for every `k ∈ ℕ`. -/
theorem norm_expFreq_pow_sub_one_le (ξ : ℝ) (k : ℕ) :
    ‖expFreq ξ ^ k - 1‖ ≤ 2 * π * k * |ξ| := by
  rw [expFreq_pow]
  calc ‖expFreq (k * ξ) - 1‖ ≤ 2 * π * |k * ξ| := norm_expFreq_sub_one_le _
    _ = 2 * π * k * |ξ| := by rw [abs_mul, Nat.abs_cast]; ring

/-- **The factor `(1 + z)/2` on the unit circle**: `(1 + e^(-2πiξ))/2 = e^(-πiξ) cos(πξ)`, since
`2 cos(πξ) = e^(πiξ) + e^(-πiξ)` (Mathlib's `Complex.two_cos`). -/
theorem one_add_expFreq_div_two (ξ : ℝ) :
    (1 + expFreq ξ) / 2 = expFreq (ξ / 2) * (Real.cos (π * ξ) : ℂ) := by
  have h : expFreq (ξ / 2) * (2 * Complex.cos ((π * ξ : ℝ) : ℂ)) = 1 + expFreq ξ := by
    rw [Complex.two_cos, mul_add, expFreq, expFreq, ← Complex.exp_add, ← Complex.exp_add]
    congr 1
    · rw [← Complex.exp_zero]
      congr 1
      push_cast
      ring
    · congr 1
      push_cast
      ring
  rw [Complex.ofReal_cos, ← h]
  ring

/-- `|(1 + e^(-2πiξ))/2| = |cos(πξ)|`. -/
theorem norm_one_add_expFreq_div_two (ξ : ℝ) :
    ‖(1 + expFreq ξ) / 2‖ = |Real.cos (π * ξ)| := by
  rw [one_add_expFreq_div_two, norm_mul, norm_expFreq, one_mul, Complex.norm_real,
    Real.norm_eq_abs]

/-- `|(1 + e^(-2πiξ))/2|² = cos²(πξ)`. -/
theorem normSq_one_add_expFreq_div_two (ξ : ℝ) :
    ‖(1 + expFreq ξ) / 2‖ ^ 2 = Real.cos (π * ξ) ^ 2 := by
  rw [norm_one_add_expFreq_div_two, sq_abs]

/-! ### Masks -/

/-- **A Daubechies mask of order `N`**, given by its polynomial factor: a real polynomial `L` of
degree `< N` with `L(1) = 1` and `|L(e^(-2πiξ))|² = P(ξ) = P_N(sin²(πξ))` for every `ξ ∈ ℝ`
(`Daubechies.daubFun`). The mask polynomial is `m(z) = ((1 + z)/2)^N L(z)`
(`Daubechies.maskPoly`). Every mask has order `N ≥ 1` (`Daubechies.Mask.one_le`). -/
structure Mask (N : ℕ) where
  /-- The polynomial factor `L` of the mask. -/
  L : ℝ[X]
  /-- `L` has degree `< N`, so that the mask polynomial has degree `< 2N`. -/
  natDegree_L_lt : L.natDegree < N
  /-- `L(1) = 1`, which normalises the symbol to `m_0(0) = 1`. -/
  eval_L_one : L.eval 1 = 1
  /-- `|L(e^(-2πiξ))|² = P_N(sin²(πξ))` for every `ξ ∈ ℝ`. -/
  normSq_L : ∀ ξ : ℝ, ‖aeval (expFreq ξ) L‖ ^ 2 = daubFun N ξ

/-- Every mask has order `N ≥ 1`: the degree of `L` is a natural number `< N`. -/
theorem Mask.one_le {N : ℕ} (m : Mask N) : 1 ≤ N := by
  have := m.natDegree_L_lt
  omega

variable {N : ℕ} (m : Mask N)

/-! ### The mask polynomial and the filter coefficients -/

/-- **The mask polynomial** `m(z) = ((1 + z)/2)^N L(z)` of a mask of order `N`. -/
noncomputable def maskPoly : ℝ[X] := (C (1 / 2 : ℝ) * (1 + X)) ^ N * m.L

/-- **The filter coefficients** `c_k = 2 [z^k] m(z)` of a mask, for `k ∈ ℤ`: twice the
coefficients of the mask polynomial for `k ≥ 0`, and `0` for `k < 0`. They vanish outside
`0 ≤ k < 2N` (`Daubechies.coeff_eq_zero`) and add up to `2` (`Daubechies.sum_coeff`). -/
noncomputable def coeff (k : ℤ) : ℝ :=
  if 0 ≤ k then 2 * (maskPoly m).coeff k.toNat else 0

/-- **The symbol** `m_0(ξ) = m(e^(-2πiξ))` of a mask, the mask polynomial evaluated on the unit
circle; it equals `(1/2) ∑_k c_k e^(-2πikξ)` (`Daubechies.symbol_eq_sum`). -/
noncomputable def symbol (ξ : ℝ) : ℂ := aeval (expFreq ξ) (maskPoly m)

/-- **The Lipschitz constant of the symbol at `0`**, `π ∑_{k < 2N} k |c_k|`: by
`Daubechies.norm_symbol_sub_one_le`, `|m_0(ξ) - 1| ≤ π ∑_k k |c_k| · |ξ|`. -/
noncomputable def symbolLip : ℝ :=
  π * ∑ k ∈ Finset.range (2 * N), (k : ℝ) * |coeff m k|

/-- The mask polynomial is divisible by `(z + 1)^N`: `m(z) = (z + 1)^N · 2^(-N) L(z)`. This is the
source of the sum rules of the filter coefficients. -/
theorem X_add_one_pow_dvd_maskPoly : (X + 1) ^ N ∣ maskPoly m :=
  ⟨C (1 / 2 : ℝ) ^ N * m.L, by rw [maskPoly, mul_pow, add_comm X]; ring⟩

/-- The mask polynomial has degree `≤ 2N - 1`: `N` factors of degree `1` and `deg L ≤ N - 1`. -/
theorem natDegree_maskPoly_le : (maskPoly m).natDegree ≤ 2 * N - 1 := by
  have h1 : (C (1 / 2 : ℝ) * (1 + X)).natDegree ≤ 1 :=
    (natDegree_C_mul_le _ _).trans ((natDegree_add_le _ _).trans (by simp))
  have h2 : ((C (1 / 2 : ℝ) * (1 + X)) ^ N).natDegree ≤ N := by
    simpa using natDegree_pow_le_of_le N h1
  have h3 := m.natDegree_L_lt
  calc (maskPoly m).natDegree
      ≤ ((C (1 / 2 : ℝ) * (1 + X)) ^ N).natDegree + m.L.natDegree := natDegree_mul_le
    _ ≤ 2 * N - 1 := by omega

/-- The mask polynomial has degree `< 2N`. -/
theorem natDegree_maskPoly_lt : (maskPoly m).natDegree < 2 * N := by
  have := natDegree_maskPoly_le m
  have := m.one_le
  omega

/-- For `k ∈ ℕ` the filter coefficient is `c_k = 2 [z^k] m(z)`. -/
theorem coeff_natCast (k : ℕ) : coeff m k = 2 * (maskPoly m).coeff k := by
  simp [coeff]

/-- The filter coefficients vanish outside `0 ≤ k < 2N`: for `k < 0` by definition, for
`k ≥ 2N` since the mask polynomial has degree `< 2N`. -/
theorem coeff_eq_zero {k : ℤ} (hk : k < 0 ∨ 2 * (N : ℤ) ≤ k) : coeff m k = 0 := by
  rcases hk with hk | hk
  · simp only [coeff, not_le.2 hk, ↓reduceIte]
  · lift k to ℕ using (by omega)
    have := natDegree_maskPoly_lt m
    rw [coeff_natCast, coeff_eq_zero_of_natDegree_lt (by omega), mul_zero]

/-- `m(1) = 1`: `((1 + 1)/2)^N L(1) = 1`. -/
theorem eval_one_maskPoly : (maskPoly m).eval 1 = 1 := by
  norm_num [maskPoly, m.eval_L_one]

/-- **The filter coefficients add up to `2`**: `∑_{k < 2N} c_k = 2 m(1) = 2`. -/
theorem sum_coeff : ∑ k ∈ Finset.range (2 * N), coeff m k = 2 := by
  have h := eval_eq_sum_range' (natDegree_maskPoly_lt m) (1 : ℝ)
  simp only [eval_one_maskPoly, one_pow, mul_one] at h
  simp only [coeff_natCast, ← Finset.mul_sum, ← h, mul_one]

/-! ### The symbol -/

/-- The symbol factors as `m_0(ξ) = ((1 + e^(-2πiξ))/2)^N L(e^(-2πiξ))`. -/
theorem symbol_eq_mul (ξ : ℝ) :
    symbol m ξ = ((1 + expFreq ξ) / 2) ^ N * aeval (expFreq ξ) m.L := by
  simp only [symbol, maskPoly, map_mul, map_pow, map_add, map_one, aeval_C, aeval_X,
    Complex.coe_algebraMap]
  congr 2
  push_cast
  ring

/-- **The symbol as a trigonometric polynomial**:
`m_0(ξ) = (1/2) ∑_{k < 2N} c_k e^(-2πikξ)`, with `e^(-2πikξ) = (e^(-2πiξ))^k`. -/
theorem symbol_eq_sum (ξ : ℝ) :
    symbol m ξ = 1 / 2 * ∑ k ∈ Finset.range (2 * N), (coeff m k : ℂ) * expFreq ξ ^ k := by
  rw [symbol, aeval_eq_sum_range' (natDegree_maskPoly_lt m), Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_natCast, Complex.real_smul]
  push_cast
  ring

/-- `m_0(0) = m(1) = 1`. -/
theorem symbol_zero : symbol m 0 = 1 := by
  rw [symbol, expFreq_zero, aeval_def, eval₂_at_one, eval_one_maskPoly, map_one]

/-- **The squared modulus of the symbol**: `|m_0(ξ)|² = cos(πξ)^(2N) P(ξ)`, from
`|(1 + e^(-2πiξ))/2|² = cos²(πξ)` and `|L(e^(-2πiξ))|² = P(ξ)`. -/
theorem normSq_symbol (ξ : ℝ) :
    ‖symbol m ξ‖ ^ 2 = Real.cos (π * ξ) ^ (2 * N) * daubFun N ξ := by
  rw [symbol_eq_mul, norm_mul, mul_pow, norm_pow, ← pow_mul, mul_comm N 2, pow_mul,
    normSq_one_add_expFreq_div_two, m.normSq_L, ← pow_mul]

/-- **The quadrature mirror filter identity** `|m_0(ξ)|² + |m_0(ξ + 1/2)|² = 1`: with
`cos(π(ξ + 1/2)) = -sin(πξ)` it is the trigonometric Bézout identity
`cos(πξ)^(2N) P(ξ) + sin(πξ)^(2N) P(ξ + 1/2) = 1` (`Daubechies.daubFun_bezout`). -/
theorem qmf (ξ : ℝ) : ‖symbol m ξ‖ ^ 2 + ‖symbol m (ξ + 1 / 2)‖ ^ 2 = 1 := by
  rw [normSq_symbol, normSq_symbol, show π * (ξ + 1 / 2) = π * ξ + π / 2 by ring,
    Real.cos_add_pi_div_two, Even.neg_pow (even_two_mul N)]
  exact daubFun_bezout m.one_le ξ

/-- `|m_0(ξ)| ≤ 1`, from the quadrature mirror filter identity. -/
theorem norm_symbol_le_one (ξ : ℝ) : ‖symbol m ξ‖ ≤ 1 := by
  have h := qmf m ξ
  nlinarith [norm_nonneg (symbol m ξ), sq_nonneg ‖symbol m (ξ + 1 / 2)‖]

/-- The symbol has period `1`. -/
theorem symbol_periodic : Function.Periodic (symbol m) 1 := fun ξ => by
  rw [symbol, symbol, expFreq_periodic ξ]

/-- `m_0(-ξ) = conj (m_0(ξ))`: the mask polynomial has real coefficients, and
`e^(-2πi(-ξ)) = conj (e^(-2πiξ))`. -/
theorem symbol_neg (ξ : ℝ) : symbol m (-ξ) = conj (symbol m ξ) := by
  have h := aeval_algHom_apply Complex.conjAe (expFreq ξ) (maskPoly m)
  rw [Complex.conjAe_coe, conj_expFreq] at h
  exact h

/-- **The symbol has no zeros in `(-1/2, 1/2)`**: there `cos(πξ) > 0`, and `P(ξ) ≥ 1`
(`Daubechies.one_le_daubFun`), so `|m_0(ξ)|² = cos(πξ)^(2N) P(ξ) > 0`. -/
theorem symbol_ne_zero {ξ : ℝ} (h : |ξ| < 1 / 2) : symbol m ξ ≠ 0 := by
  have hcos : 0 < Real.cos (π * ξ) := by
    apply Real.cos_pos_of_mem_Ioo
    rw [abs_lt] at h
    constructor <;> nlinarith [Real.pi_pos]
  have hpos : 0 < ‖symbol m ξ‖ ^ 2 := by
    rw [normSq_symbol]
    exact mul_pos (pow_pos hcos _) (lt_of_lt_of_le one_pos (one_le_daubFun m.one_le ξ))
  intro h0
  rw [h0, norm_zero] at hpos
  norm_num at hpos

/-- `m_0(1/2 + n) = 0` for every integer `n`: there `e^(-2πiξ) = -1`, so the factor
`((1 + z)/2)^N` vanishes (`N ≥ 1`). -/
theorem symbol_half_add_int (n : ℤ) : symbol m (1 / 2 + n) = 0 := by
  have := m.one_le
  rw [symbol_eq_mul, expFreq_half_add_int, add_neg_cancel, zero_div, zero_pow (by omega),
    zero_mul]

/-- `m_0(1/2) = 0`. -/
theorem symbol_half : symbol m (1 / 2) = 0 := by
  simpa using symbol_half_add_int m 0

/-- The constant `π ∑_k k |c_k|` is nonnegative. -/
theorem symbolLip_nonneg : 0 ≤ symbolLip m :=
  mul_nonneg Real.pi_pos.le
    (Finset.sum_nonneg fun k _ => mul_nonneg (Nat.cast_nonneg k) (abs_nonneg _))

/-- **The symbol is Lipschitz at `0`**: `|m_0(ξ) - 1| ≤ π ∑_k k |c_k| · |ξ|`. Since
`∑_k c_k = 2`, `m_0(ξ) - 1 = (1/2) ∑_k c_k (e^(-2πikξ) - 1)`, and
`|e^(-2πikξ) - 1| ≤ 2πk|ξ|`. -/
theorem norm_symbol_sub_one_le (ξ : ℝ) : ‖symbol m ξ - 1‖ ≤ symbolLip m * |ξ| := by
  have hsum : ∑ k ∈ Finset.range (2 * N), (coeff m k : ℂ) = 2 := by
    exact_mod_cast sum_coeff m
  have h : symbol m ξ - 1 =
      1 / 2 * ∑ k ∈ Finset.range (2 * N), (coeff m k : ℂ) * (expFreq ξ ^ k - 1) := by
    simp only [symbol_eq_sum, mul_sub, mul_one, Finset.sum_sub_distrib, hsum]
    ring
  have hhalf : ‖(1 / 2 : ℂ)‖ = 1 / 2 := by norm_num
  rw [h, norm_mul, hhalf]
  calc 1 / 2 * ‖∑ k ∈ Finset.range (2 * N), (coeff m k : ℂ) * (expFreq ξ ^ k - 1)‖
      ≤ 1 / 2 * ∑ k ∈ Finset.range (2 * N), |coeff m k| * (2 * π * k * |ξ|) := by
        gcongr
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun k _ => ?_)
        rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
        exact mul_le_mul_of_nonneg_left (norm_expFreq_pow_sub_one_le ξ k) (abs_nonneg _)
    _ = symbolLip m * |ξ| := by
        rw [symbolLip, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring

/-- **The symbol is smooth**: `C^n` for every `n`, including `n = ∞` and the analytic case
`n = ω`, as a polynomial (Mathlib's `Polynomial.contDiff_aeval`) composed with the smooth map
`ξ ↦ e^(-2πiξ)`. -/
theorem contDiff_symbol {n : WithTop ℕ∞} : ContDiff ℝ n (symbol m) :=
  (((maskPoly m).contDiff_aeval n).restrict_scalars ℝ).comp contDiff_expFreq

/-- The symbol is continuous. -/
theorem continuous_symbol : Continuous (symbol m) :=
  (contDiff_symbol m (n := 0)).continuous

end Daubechies
