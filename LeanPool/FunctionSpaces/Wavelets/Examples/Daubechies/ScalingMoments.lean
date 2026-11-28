/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Cascade
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.FilterIdentities
public import Mathlib.Analysis.Calculus.IteratedDeriv.Lemmas
public import Mathlib.Analysis.Fourier.FourierTransformDeriv
public import Mathlib.Analysis.Fourier.PoissonSummation

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Smoothness of the symbol product and the moments of the scaling function

For a Daubechies mask of order `N ≥ 2` with symbol `m_0` (`Daubechies.symbol`), symbol product
`Φ(ξ) = ∏_{j ≥ 0} m_0(ξ/2^(j+1))` (`Daubechies.symbolProduct`) and scaling function `φ = 𝓕⁻ Φ`
(`Daubechies.scalingFun`), this file proves that the periodised moments of `φ` are constant:

`∑_{k ∈ ℤ} (x - k)^l φ(x - k) = ∫ y^l φ(y) dy` for every `x ∈ ℝ` and every `l < N`
(`Daubechies.periodization_moment_eq`),

in particular the **partition of unity** `∑_{k ∈ ℤ} φ(x - k) = 1`
(`Daubechies.sum_scalingFun_translate`).

* **Smoothness of `Φ`.** The scaling function is continuous with compact support, so every
  moment `∫ |x|^n |φ(x)| dx` is finite, and `Φ = 𝓕 φ` (`Daubechies.fourier_scalingFun`) is smooth
  (`Daubechies.contDiff_symbolProduct`, Mathlib's `Real.contDiff_fourier`). Its derivatives are
  the Fourier transforms of the moments, `Φ^(l) = (-2πi)^l 𝓕[x^l φ]`
  (`Daubechies.iteratedDeriv_symbolProduct_eq_fourier`, Mathlib's `Real.iteratedDeriv_fourier`).
* **Derivatives at the nonzero integers.** The Leibniz rule applied to `Φ(2ξ) = m_0(ξ) Φ(ξ)`
  gives `2^l Φ^(l)(2ξ) = ∑_{i ≤ l} C(l, i) m_0^(i)(ξ) Φ^(l-i)(ξ)`
  (`Daubechies.iteratedDeriv_symbolProduct_two_mul`). For `l < N` the derivatives
  `m_0^(i)(1/2 + n)` with `i ≤ l` vanish (`Daubechies.iteratedDeriv_symbol_half_add_int`), so
  `Φ^(l)(2n + 1) = 0`; at an even integer `2j` the derivatives `Φ^(i)(j)` vanish by induction on
  `|j|`. Hence `Φ^(l)(j) = 0` for every integer `j ≠ 0` and every `l < N`
  (`Daubechies.iteratedDeriv_symbolProduct_int`), and `𝓕[x^l φ](j) = 0`
  (`Daubechies.fourier_pow_mul_scalingFun_int`).
* **Periodisation.** The periodisation `∑_n f(x + n)` of a continuous function `f` with compact
  support has the Fourier coefficients `𝓕 f(n)`, `n ∈ ℤ`. If they vanish for `n ≠ 0`, Poisson
  summation (Mathlib's `Real.tsum_eq_tsum_fourier`) shows that the periodisation is the constant
  `𝓕 f(0) = ∫ f` (`Real.tsum_comp_add_int_eq_integral`). Applied to `f(y) = y^l φ(y)` this gives
  the periodised moments.
* **Finite sums.** Since `φ` vanishes outside `[0, 2N - 1]`, only the indices
  `⌊x⌋ - (2N - 1) ≤ k ≤ ⌊x⌋` contribute to a sum `∑_k a(k) φ(x - k)`
  (`Daubechies.scalingFun_sub_eq_zero`, `Daubechies.tsum_mul_scalingFun_sub_eq_sum`).
-/

@[expose] public section

open Filter MeasureTheory
open scoped Real FourierTransform

namespace Real

/-! ### Poisson summation with vanishing Fourier coefficients -/

/-- For a continuous function `f : ℝ → E` vanishing outside a bounded interval `[a, b]` and a
compact set `K ⊆ ℝ`, the sup norms over `K` of the translates `x ↦ f(x + n)`, `n ∈ ℤ`, are
summable: only the finitely many `n` with `K + n` meeting `[a, b]` give a translate that is
nonzero on `K`. This is the hypothesis of Mathlib's Poisson summation formula
`Real.tsum_eq_tsum_fourier`. -/
theorem summable_norm_restrict_comp_addRight {E : Type*} [NormedAddCommGroup E] {f : C(ℝ, E)}
    {a b : ℝ} (hf : ∀ x ∉ Set.Icc a b, f x = 0) (K : TopologicalSpace.Compacts ℝ) :
    Summable fun n : ℤ => ‖(f.comp (ContinuousMap.addRight (n : ℝ))).restrict K‖ := by
  obtain ⟨R, hR⟩ := K.isCompact.isBounded.exists_norm_le
  refine summable_of_ne_finset_zero (s := Finset.Icc ⌈a - R⌉ ⌊b + R⌋) fun n hn => ?_
  refine le_antisymm ((ContinuousMap.norm_le _ le_rfl).2 fun y => ?_) (norm_nonneg _)
  have hy : |(y : ℝ)| ≤ R := hR y y.2
  rw [abs_le] at hy
  have hmem : (y : ℝ) + n ∉ Set.Icc a b := fun h => hn (by
    rw [Finset.mem_Icc, Int.ceil_le, Int.le_floor]
    exact ⟨by linarith [h.1], by linarith [h.2]⟩)
  rw [ContinuousMap.restrict_apply, ContinuousMap.comp_apply, ContinuousMap.coe_addRight,
    hf _ hmem, norm_zero]

/-- **Poisson summation when the Fourier transform vanishes at the nonzero integers**: let
`f : ℝ → ℂ` be continuous and vanish outside a bounded interval `[a, b]`, with `𝓕 f(n) = 0` for
every integer `n ≠ 0`. Then the periodisation of `f` is the constant `∫ f`:
`∑_{n ∈ ℤ} f(x + n) = ∫ f(y) dy` for every `x ∈ ℝ`. Poisson summation (Mathlib's
`Real.tsum_eq_tsum_fourier`) writes the periodisation as the Fourier series
`∑_n 𝓕 f(n) e^(2πinx)`, whose only nonzero term is `𝓕 f(0) = ∫ f` (`Real.fourier_apply_zero`). -/
theorem tsum_comp_add_int_eq_integral {f : ℝ → ℂ} (hf : Continuous f) {a b : ℝ}
    (hab : ∀ x ∉ Set.Icc a b, f x = 0) (hF : ∀ n : ℤ, n ≠ 0 → 𝓕 f n = 0) (x : ℝ) :
    ∑' n : ℤ, f (x + n) = ∫ y, f y := by
  have hsum : Summable fun n : ℤ => 𝓕 f n :=
    summable_of_ne_finset_zero (s := {0}) fun n hn => hF n (Finset.notMem_singleton.1 hn)
  have h := tsum_eq_tsum_fourier (f := ⟨f, hf⟩)
    (summable_norm_restrict_comp_addRight (f := ⟨f, hf⟩) hab) hsum x
  have h0 : ∑' n : ℤ, 𝓕 f n * fourier n (x : UnitAddCircle) = ∫ y, f y := by
    rw [tsum_eq_single 0, Int.cast_zero, _root_.fourier_zero, mul_one, fourier_apply_zero]
    intro n hn
    rw [hF n hn, zero_mul]
  simp only [ContinuousMap.coe_mk] at h
  rw [h, h0]

end Real

namespace Daubechies

variable {N : ℕ} (m : Mask N)

/-! ### Smoothness of the symbol product -/

/-- For `N ≥ 2` and every `n ∈ ℕ` the function `x ↦ |x|^n |φ(x)|` is integrable: it is
continuous and vanishes outside `[0, 2N - 1]` (`Daubechies.hasCompactSupport_scalingFun`). -/
theorem integrable_norm_pow_mul_norm_scalingFun (hN : 2 ≤ N) (n : ℕ) :
    Integrable fun x : ℝ => ‖x‖ ^ n * ‖scalingFun m x‖ :=
  ((continuous_norm.pow n).mul (continuous_scalingFun m hN).norm).integrable_of_hasCompactSupport
    (hasCompactSupport_scalingFun m hN).norm.mul_left

/-- **The symbol product is smooth** for `N ≥ 2`: `Φ = 𝓕 φ` (`Daubechies.fourier_scalingFun`)
is `C^∞`, since every moment `∫ |x|^n |φ(x)| dx` is finite (Mathlib's
`Real.contDiff_fourier`). -/
theorem contDiff_symbolProduct (hN : 2 ≤ N) :
    ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (symbolProduct m) := by
  rw [← fourier_scalingFun m hN]
  exact Real.contDiff_fourier fun n _ => integrable_norm_pow_mul_norm_scalingFun m hN n

/-- For `N ≥ 2` the symbol product is `C^n` for every `n ∈ ℕ`
(`Daubechies.contDiff_symbolProduct`). -/
theorem contDiff_nat_symbolProduct (hN : 2 ≤ N) (n : ℕ) : ContDiff ℝ n (symbolProduct m) :=
  (contDiff_symbolProduct m hN).of_le (by exact_mod_cast le_top)

/-! ### Derivatives of the refinement identity -/

/-- **The derivatives of the refinement identity** `Φ(2ξ) = m_0(ξ) Φ(ξ)`: for `N ≥ 2`, every
`l ∈ ℕ` and every `ξ ∈ ℝ`,
`2^l Φ^(l)(2ξ) = ∑_{i=0}^{l} C(l, i) m_0^(i)(ξ) Φ^(l-i)(ξ)`.
The left side is the `l`-th derivative of `ξ ↦ Φ(2ξ)` (chain rule, Mathlib's
`iteratedDeriv_comp_const_smul`), the right side that of `m_0 · Φ` (Leibniz rule, Mathlib's
`iteratedDeriv_fun_mul`); both factors are smooth (`Daubechies.contDiff_symbol`,
`Daubechies.contDiff_symbolProduct`). -/
theorem iteratedDeriv_symbolProduct_two_mul (hN : 2 ≤ N) (l : ℕ) (ξ : ℝ) :
    (2 : ℂ) ^ l * iteratedDeriv l (symbolProduct m) (2 * ξ) =
      ∑ i ∈ Finset.range (l + 1), (l.choose i : ℂ) * iteratedDeriv i (symbol m) ξ *
        iteratedDeriv (l - i) (symbolProduct m) ξ := by
  have h : iteratedDeriv l (fun x => symbolProduct m (2 * x)) ξ =
      (2 : ℝ) ^ l • iteratedDeriv l (symbolProduct m) (2 * ξ) :=
    congrFun (iteratedDeriv_comp_const_smul (contDiff_nat_symbolProduct m hN l) (2 : ℝ)) ξ
  simp only [symbolProduct_two_mul] at h
  rw [iteratedDeriv_fun_mul (contDiff_symbol m).contDiffAt
    (contDiff_nat_symbolProduct m hN l).contDiffAt, Complex.real_smul] at h
  rw [h]
  push_cast
  ring

/-- If all derivatives `Φ^(i)`, `i ≤ l`, vanish at a point `ξ`, then `Φ^(l)(2ξ) = 0` (for
`N ≥ 2`): every term of the Leibniz sum in `Daubechies.iteratedDeriv_symbolProduct_two_mul`
contains a factor `Φ^(l-i)(ξ) = 0`. -/
theorem iteratedDeriv_symbolProduct_two_mul_eq_zero (hN : 2 ≤ N) {l : ℕ} {ξ : ℝ}
    (h : ∀ i ≤ l, iteratedDeriv i (symbolProduct m) ξ = 0) :
    iteratedDeriv l (symbolProduct m) (2 * ξ) = 0 := by
  have h' := iteratedDeriv_symbolProduct_two_mul m hN l ξ
  have h0 : ∑ i ∈ Finset.range (l + 1), (l.choose i : ℂ) * iteratedDeriv i (symbol m) ξ *
      iteratedDeriv (l - i) (symbolProduct m) ξ = 0 :=
    Finset.sum_eq_zero fun i _ => by rw [h (l - i) (Nat.sub_le l i), mul_zero]
  rw [h0] at h'
  exact (mul_eq_zero.1 h').resolve_left (pow_ne_zero _ two_ne_zero)

/-- **`Φ^(l)` vanishes at the odd integers** for `l < N` (and `N ≥ 2`): `Φ^(l)(2n + 1) = 0` for
every `n ∈ ℤ`. In the Leibniz sum of `Daubechies.iteratedDeriv_symbolProduct_two_mul` at
`ξ = 1/2 + n` every derivative `m_0^(i)(1/2 + n)`, `i ≤ l < N`, vanishes
(`Daubechies.iteratedDeriv_symbol_half_add_int`, a consequence of the sum rules). -/
theorem iteratedDeriv_symbolProduct_two_mul_add_one (hN : 2 ≤ N) {l : ℕ} (hl : l < N) (n : ℤ) :
    iteratedDeriv l (symbolProduct m) (2 * n + 1) = 0 := by
  have h := iteratedDeriv_symbolProduct_two_mul m hN l (1 / 2 + n)
  have h0 : ∑ i ∈ Finset.range (l + 1), (l.choose i : ℂ) *
      iteratedDeriv i (symbol m) (1 / 2 + n) *
      iteratedDeriv (l - i) (symbolProduct m) (1 / 2 + n) = 0 :=
    Finset.sum_eq_zero fun i hi => by
      rw [iteratedDeriv_symbol_half_add_int m
        ((Nat.lt_succ_iff.1 (Finset.mem_range.1 hi)).trans_lt hl) n, mul_zero, zero_mul]
  rw [h0, show 2 * (1 / 2 + (n : ℝ)) = 2 * n + 1 by ring] at h
  exact (mul_eq_zero.1 h).resolve_left (pow_ne_zero _ two_ne_zero)

/-- **The derivatives of `Φ` vanish at the nonzero integers**: for `N ≥ 2`, every integer
`j ≠ 0` and every `l < N`, `Φ^(l)(j) = 0`. By induction on `|j|`, for all `l < N` at once: an
odd `j` is covered by `Daubechies.iteratedDeriv_symbolProduct_two_mul_add_one`; for even
`j = 2j'` the integer `j' ≠ 0` is smaller in absolute value, so `Φ^(i)(j') = 0` for every
`i ≤ l`, and `Daubechies.iteratedDeriv_symbolProduct_two_mul_eq_zero` gives `Φ^(l)(2j') = 0`. -/
theorem iteratedDeriv_symbolProduct_int (hN : 2 ≤ N) (j : ℤ) (hj : j ≠ 0) (l : ℕ) (hl : l < N) :
    iteratedDeriv l (symbolProduct m) j = 0 := by
  suffices h : ∀ n : ℕ, ∀ j : ℤ, j.natAbs ≤ n → j ≠ 0 → ∀ l < N,
      iteratedDeriv l (symbolProduct m) j = 0 from h _ j le_rfl hj l hl
  intro n
  induction n with
  | zero =>
    intro j hj hj0
    exact absurd (by omega : j = 0) hj0
  | succ n ih =>
    intro j hjn hj0 l hl
    obtain ⟨i, rfl | rfl⟩ := Int.even_or_odd' j
    · have hi : i ≠ 0 := by
        rintro rfl
        simp at hj0
      push_cast
      exact iteratedDeriv_symbolProduct_two_mul_eq_zero m hN fun k hk =>
        ih i (by omega) hi k (hk.trans_lt hl)
    · push_cast
      exact iteratedDeriv_symbolProduct_two_mul_add_one m hN hl i

/-! ### The Fourier transforms of the moments -/

/-- For `N ≥ 2` and every `n ∈ ℕ` the moment function `x ↦ x^n φ(x)` is integrable: it is
continuous with compact support. It is written with the real scalar multiplication
`x^n • φ(x)`, the form of the hypothesis of Mathlib's `Real.iteratedDeriv_fourier`. -/
theorem integrable_pow_smul_scalingFun (hN : 2 ≤ N) (n : ℕ) :
    Integrable fun x : ℝ => x ^ n • scalingFun m x :=
  ((continuous_pow n).smul (continuous_scalingFun m hN)).integrable_of_hasCompactSupport
    (hasCompactSupport_scalingFun m hN).smul_left

/-- **The derivatives of `Φ` are the Fourier transforms of the moments**: for `N ≥ 2`, every
`l ∈ ℕ` and every `ξ ∈ ℝ`, `Φ^(l)(ξ) = (-2πi)^l 𝓕[x^l φ](ξ)`. This is differentiation under the
integral sign in `Φ = 𝓕 φ` (Mathlib's `Real.iteratedDeriv_fourier`), legitimate since every
moment of `φ` is integrable. -/
theorem iteratedDeriv_symbolProduct_eq_fourier (hN : 2 ≤ N) (l : ℕ) (ξ : ℝ) :
    iteratedDeriv l (symbolProduct m) ξ =
      (-2 * π * Complex.I) ^ l * 𝓕 (fun x : ℝ => (x : ℂ) ^ l * scalingFun m x) ξ := by
  rw [← fourier_scalingFun m hN, Real.iteratedDeriv_fourier (N := l)
    (fun n _ => integrable_pow_smul_scalingFun m hN n) le_rfl, ← Real.fourier_const_mul_apply]
  simp only [smul_eq_mul, mul_pow, mul_assoc]

/-- **The Fourier transforms of the moments vanish at the nonzero integers**: for `N ≥ 2`,
`l < N` and every integer `j ≠ 0`, `𝓕[x^l φ](j) = 0`, since
`(-2πi)^l 𝓕[x^l φ](j) = Φ^(l)(j) = 0` (`Daubechies.iteratedDeriv_symbolProduct_eq_fourier`,
`Daubechies.iteratedDeriv_symbolProduct_int`). -/
theorem fourier_pow_mul_scalingFun_int (hN : 2 ≤ N) {l : ℕ} (hl : l < N) {j : ℤ} (hj : j ≠ 0) :
    𝓕 (fun x : ℝ => (x : ℂ) ^ l * scalingFun m x) j = 0 := by
  have h := iteratedDeriv_symbolProduct_eq_fourier m hN l j
  rw [iteratedDeriv_symbolProduct_int m hN j hj l hl] at h
  refine (mul_eq_zero.1 h.symm).resolve_left (pow_ne_zero _ ?_)
  simp [Real.pi_ne_zero, Complex.I_ne_zero]

/-! ### The periodised moments -/

/-- For `N ≥ 2` the moment function `x ↦ x^l φ(x)` is continuous. -/
theorem continuous_pow_mul_scalingFun (hN : 2 ≤ N) (l : ℕ) :
    Continuous fun x : ℝ => (x : ℂ) ^ l * scalingFun m x :=
  (Complex.continuous_ofReal.pow l).mul (continuous_scalingFun m hN)

/-- **The periodised moments are constant**: for `N ≥ 2`, `l < N` and every `x ∈ ℝ`,
`∑_{k ∈ ℤ} (x - k)^l φ(x - k) = ∫ y^l φ(y) dy`. The function `f(y) = y^l φ(y)` is continuous,
vanishes outside `[0, 2N - 1]`, and `𝓕 f(n) = 0` for every integer `n ≠ 0`
(`Daubechies.fourier_pow_mul_scalingFun_int`), so Poisson summation
(`Real.tsum_comp_add_int_eq_integral`) gives `∑_n f(x + n) = ∫ f`; the substitution `k = -n`
turns this into the sum over the points `x - k`. -/
theorem periodization_moment_eq (hN : 2 ≤ N) {l : ℕ} (hl : l < N) (x : ℝ) :
    ∑' k : ℤ, ((x - k : ℝ) : ℂ) ^ l * scalingFun m (x - k) =
      ∫ y : ℝ, (y : ℂ) ^ l * scalingFun m y := by
  have h : ∑' k : ℤ, ((x - k : ℝ) : ℂ) ^ l * scalingFun m (x - k) =
      ∑' n : ℤ, ((x + n : ℝ) : ℂ) ^ l * scalingFun m (x + n) := by
    rw [← (Equiv.neg ℤ).tsum_eq]
    simp only [Equiv.neg_apply, Int.cast_neg, sub_neg_eq_add]
  rw [h]
  exact Real.tsum_comp_add_int_eq_integral (a := 0) (b := 2 * N - 1)
    (continuous_pow_mul_scalingFun m hN l) (fun y hy => by simp [scalingFun_eq_zero m hN hy])
    (fun n hn => fourier_pow_mul_scalingFun_int m hN hl hn) x

/-- **The periodised moments are constant**, in existential form: for `N ≥ 2` and `l < N` there
is a constant `c` with `∑_{k ∈ ℤ} (x - k)^l φ(x - k) = c` for every `x ∈ ℝ`, namely
`c = ∫ y^l φ(y) dy` (`Daubechies.periodization_moment_eq`). -/
theorem periodization_moment_const (hN : 2 ≤ N) {l : ℕ} (hl : l < N) :
    ∃ c : ℂ, ∀ x : ℝ, ∑' k : ℤ, ((x - k : ℝ) : ℂ) ^ l * scalingFun m (x - k) = c :=
  ⟨_, periodization_moment_eq m hN hl⟩

/-- **Partition of unity**: `∑_{k ∈ ℤ} φ(x - k) = 1` for every `x ∈ ℝ` (for `N ≥ 2`), the case
`l = 0` of `Daubechies.periodization_moment_eq` together with `∫ φ = 1`
(`Daubechies.integral_scalingFun`). -/
theorem sum_scalingFun_translate (hN : 2 ≤ N) (x : ℝ) : ∑' k : ℤ, scalingFun m (x - k) = 1 := by
  have h := periodization_moment_eq m hN (l := 0) (by omega) x
  simp only [pow_zero, one_mul] at h
  rw [h, integral_scalingFun m hN]

/-! ### Sums over the translates are finite -/

/-- **Only finitely many translates are nonzero at a point**: for `N ≥ 2`, `x ∈ ℝ` and an
integer `k` outside `[⌊x⌋ - (2N - 1), ⌊x⌋]`, `φ(x - k) = 0`. Indeed `φ(x - k) ≠ 0` forces
`x - k ∈ [0, 2N - 1]` (`Daubechies.scalingFun_eq_zero`), hence `k ≤ x`, so `k ≤ ⌊x⌋`, and
`k ≥ x - (2N - 1) ≥ ⌊x⌋ - (2N - 1)`. The index set depends only on `⌊x⌋`. -/
theorem scalingFun_sub_eq_zero (hN : 2 ≤ N) {x : ℝ} {k : ℤ}
    (hk : k ∉ Finset.Icc (⌊x⌋ - (2 * N - 1)) ⌊x⌋) : scalingFun m (x - k) = 0 := by
  refine scalingFun_eq_zero m hN fun h => hk ?_
  obtain ⟨h0, h1⟩ := h
  have hfl := Int.floor_le x
  have hk2 : ((⌊x⌋ - (2 * N - 1) : ℤ) : ℝ) ≤ k := by
    push_cast
    linarith
  exact Finset.mem_Icc.2 ⟨by exact_mod_cast hk2, Int.le_floor.2 (by linarith)⟩

/-- **Sums against the translates of `φ` are finite**: for `N ≥ 2`, `x ∈ ℝ` and coefficients
`a : ℤ → ℂ`, `∑_{k ∈ ℤ} a(k) φ(x - k) = ∑_{k = ⌊x⌋ - (2N - 1)}^{⌊x⌋} a(k) φ(x - k)`
(`Daubechies.scalingFun_sub_eq_zero`). -/
theorem tsum_mul_scalingFun_sub_eq_sum (hN : 2 ≤ N) (a : ℤ → ℂ) (x : ℝ) :
    ∑' k : ℤ, a k * scalingFun m (x - k) =
      ∑ k ∈ Finset.Icc (⌊x⌋ - (2 * N - 1)) ⌊x⌋, a k * scalingFun m (x - k) :=
  tsum_eq_sum fun k hk => by rw [scalingFun_sub_eq_zero m hN hk, mul_zero]

/-- The sums `∑_{k ∈ ℤ} a(k) φ(x - k)` converge (for `N ≥ 2`): only finitely many terms are
nonzero (`Daubechies.scalingFun_sub_eq_zero`). -/
theorem summable_mul_scalingFun_sub (hN : 2 ≤ N) (a : ℤ → ℂ) (x : ℝ) :
    Summable fun k : ℤ => a k * scalingFun m (x - k) :=
  summable_of_ne_finset_zero fun k hk => by rw [scalingFun_sub_eq_zero m hN hk, mul_zero]

/-- The sum of the translates of `φ` at a point is finite: for `N ≥ 2` and `x ∈ ℝ`,
`∑_{k ∈ ℤ} φ(x - k) = ∑_{k = ⌊x⌋ - (2N - 1)}^{⌊x⌋} φ(x - k)`
(`Daubechies.scalingFun_sub_eq_zero`). -/
theorem tsum_scalingFun_sub_eq_sum (hN : 2 ≤ N) (x : ℝ) :
    ∑' k : ℤ, scalingFun m (x - k) =
      ∑ k ∈ Finset.Icc (⌊x⌋ - (2 * N - 1)) ⌊x⌋, scalingFun m (x - k) :=
  tsum_eq_sum fun _ hk => scalingFun_sub_eq_zero m hN hk

/-- **Partition of unity as a finite sum**: for `N ≥ 2` and `x ∈ ℝ`,
`∑_{k = ⌊x⌋ - (2N - 1)}^{⌊x⌋} φ(x - k) = 1` (`Daubechies.sum_scalingFun_translate`,
`Daubechies.tsum_scalingFun_sub_eq_sum`). -/
theorem sum_Icc_scalingFun_sub (hN : 2 ≤ N) (x : ℝ) :
    ∑ k ∈ Finset.Icc (⌊x⌋ - (2 * N - 1)) ⌊x⌋, scalingFun m (x - k) = 1 := by
  rw [← tsum_scalingFun_sub_eq_sum m hN, sum_scalingFun_translate m hN]

end Daubechies
