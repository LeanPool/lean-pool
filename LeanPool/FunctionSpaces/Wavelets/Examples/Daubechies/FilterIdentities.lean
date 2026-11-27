/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.Mask
public import Mathlib.Algebra.BigOperators.Finprod
public import Mathlib.Algebra.FiniteSupport.Basic
public import Mathlib.Analysis.Calculus.IteratedDeriv.Defs
public import Mathlib.Analysis.SpecialFunctions.Integrals.Basic
public import Mathlib.MeasureTheory.Integral.IntervalIntegral.Periodic

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Filter identities of Daubechies masks

For a Daubechies mask of order `N` with filter coefficients `c_k` (`Daubechies.coeff`, zero
outside `0 ≤ k < 2N`) and symbol `m_0(ξ) = (1/2) ∑_k c_k e^(-2πikξ)` this file proves the
identities between the coefficients that the scaling function and the wavelet are built on.

**Sums over `ℤ`.** All sums run over `k ∈ ℤ` and are Mathlib's `finsum`, written `∑ᶠ k : ℤ`:
the sum of the finitely many nonzero terms, with the value `0` by convention when infinitely many
terms are nonzero. The filter coefficients have finite support
(`Daubechies.finite_support_coeff`), so every sum here has finitely many nonzero terms. Three
conversions connect these sums with the other notations: a sum whose terms vanish wherever `c_k`
vanishes is the finite sum `∑_{k<2N}` (`Daubechies.finsum_eq_sum_range_of_coeff`), a sum whose
terms vanish wherever `g_k` vanishes is the finite sum `∑_{2-2N ≤ k ≤ 1}`
(`Daubechies.finsum_eq_sum_Icc_of_dualCoeff`), and a series `∑'` with finitely many nonzero terms
is the `finsum` (Mathlib's `tsum_eq_finsum`).

* **Orthogonality of the even shifts**: `∑_k c_k c_(k+2j) = 2 δ_(j0)` for every `j ∈ ℤ`
  (`Daubechies.sum_coeff_mul_coeff_add`). The proof integrates the quadrature mirror filter
  identity `|m_0(ξ)|² + |m_0(ξ + 1/2)|² = 1` against `e^(2πi·2jξ)` over `[0, 1]`. The
  exponentials `e^(-2πikξ)` are orthonormal there (`Daubechies.integral_finsum_mul_conj_finsum`),
  so the `2j`-th Fourier coefficient of `|m_0|²` is `(1/4) ∑_k c_k c_(k+2j)`; the substitution
  `η = ξ + 1/2` and the period `1` give the same `2j`-th Fourier coefficient for
  `|m_0(ξ + 1/2)|²`.
* **Sum rules**: `∑_k (-1)^k k^l c_k = 0` for `l < N` (`Daubechies.sum_rule`), and more generally
  `∑_k (-1)^k Q(k) c_k = 0` for every polynomial `Q` of degree `< N`
  (`Daubechies.sum_rule_poly`). The mask polynomial is divisible by `(z + 1)^N`. The Euler
  operator `p ↦ z p'` multiplies the `k`-th coefficient by `k` and lowers the power of `z + 1`
  dividing `p` by at most one, and a polynomial divisible by `z + 1` vanishes at `z = -1`.
* **Parity sums and first moments**: `∑_i c_(2i+r) = 1` for every `r ∈ ℤ`
  (`Daubechies.sum_coeff_two_mul_add`) and, for `N ≥ 2`, `∑_i (2i + r) c_(2i+r) = μ` with
  `μ = (1/2) ∑_k k c_k` (`Daubechies.firstMoment`, `Daubechies.sum_two_mul_add_mul_coeff`): by
  the sum rules for `l = 0` and `l = 1` the even and the odd indices contribute equally. Together
  they give `∑_i i c_(2i+r) = (μ - r)/2` (`Daubechies.sum_mul_coeff_two_mul_add`).
* **Derivatives of the symbol at the half-integers**: `m_0^(l)(1/2 + n) = 0` for `l < N` and
  `n ∈ ℤ` (`Daubechies.iteratedDeriv_symbol_half_add_int`), since
  `m_0^(l)(ξ) = (1/2) ∑_k c_k (-2πik)^l e^(-2πikξ)` (`Daubechies.iteratedDeriv_symbol`) and
  `e^(-2πik(1/2 + n)) = (-1)^k`.
* **The dual filter** `g_k = (-1)^k c_(1-k)` (`Daubechies.dualCoeff`), the filter of the wavelet.
  Each of its identities comes from an identity for `c_k` by a substitution:
  - `∑_k g_k g_(k+2j) = 2 δ_(j0)` (`Daubechies.sum_dualCoeff_mul_dualCoeff_add`): `k ↦ 1 - 2j - k`
    turns the sum into `∑_k c_k c_(k+2j)`;
  - `∑_k c_k g_(k+2j) = 0` (`Daubechies.sum_coeff_mul_dualCoeff_add`): `k ↦ 1 - 2j - k` turns the
    sum into its negative;
  - `∑_j (c_(a-2j) c_(b-2j) + g_(a-2j) g_(b-2j)) = 2 δ_(ab)` for all `a, b ∈ ℤ`
    (`Daubechies.sum_coeff_mul_add_dual`): `j ↦ -j` turns both sums into sums over one parity
    class of `h(k) = c_(k+(a-b)) c_k`; for `a - b` even the two classes are complementary and
    add up to `∑_k c_k c_(k+(a-b))`, for `a - b` odd they cancel;
  - the vanishing moments `∑_k g_k k^l = 0` for `l < N` (`Daubechies.sum_dualCoeff_mul_pow`):
    `k ↦ 1 - k` turns the sum into `-∑_k (-1)^k (1 - k)^l c_k`, a sum rule for the polynomial
    `(1 - X)^l`.
-/

@[expose] public section

open Polynomial
open scoped Real ComplexConjugate

namespace Daubechies

/-! ### Finite sums over `ℤ` -/

/-- A sum over `k ∈ ℤ` of a function that vanishes outside `0 ≤ k < n` is the finite sum over
`k = 0, …, n - 1`. -/
theorem finsum_eq_sum_range_of_eq_zero {M : Type*} [AddCommMonoid M] {f : ℤ → M} {n : ℕ}
    (hf : ∀ k : ℤ, k < 0 ∨ (n : ℤ) ≤ k → f k = 0) :
    ∑ᶠ k : ℤ, f k = ∑ k ∈ Finset.range n, f k := by
  rw [finsum_eq_sum_of_support_subset f (s := (Finset.range n).map Nat.castEmbedding),
    Finset.sum_map]
  · rfl
  · intro k hk
    have h0 : 0 ≤ k := by
      by_contra h
      exact hk (hf k (Or.inl (not_le.1 h)))
    have h1 : k < n := by
      by_contra h
      exact hk (hf k (Or.inr (not_lt.1 h)))
    simp only [Finset.coe_map, Nat.castEmbedding_apply, Set.mem_image, Finset.mem_coe,
      Finset.mem_range]
    exact ⟨k.toNat, by omega, by omega⟩

/-- **Splitting a sum over `ℤ` by parity**: `∑_i g(2i) + ∑_i g(2i + 1) = ∑_k g(k)` for every
function `g` with finite support. -/
theorem finsum_two_mul_add_finsum_two_mul_add_one {M : Type*} [AddCommMonoid M] {g : ℤ → M}
    (hg : (Function.support g).Finite) :
    ∑ᶠ i : ℤ, g (2 * i) + ∑ᶠ i : ℤ, g (2 * i + 1) = ∑ᶠ k : ℤ, g k := by
  have he : ∑ᶠ k ∈ Set.range (fun i : ℤ => 2 * i), g k = ∑ᶠ i : ℤ, g (2 * i) :=
    finsum_mem_range fun i j h => by omega
  have ho : ∑ᶠ k ∈ Set.range (fun i : ℤ => 2 * i + 1), g k = ∑ᶠ i : ℤ, g (2 * i + 1) :=
    finsum_mem_range fun i j h => by omega
  have hdisj : Disjoint (Set.range fun i : ℤ => 2 * i) (Set.range fun i : ℤ => 2 * i + 1) := by
    rw [Set.disjoint_left]
    rintro k ⟨i, rfl⟩ ⟨j, hj⟩
    simp only at hj
    omega
  have hunion : (Set.range fun i : ℤ => 2 * i) ∪ Set.range (fun i : ℤ => 2 * i + 1) =
      Set.univ := by
    refine Set.eq_univ_of_forall fun k => ?_
    obtain ⟨i, hi | hi⟩ := Int.even_or_odd' k
    · exact Or.inl ⟨i, hi.symm⟩
    · exact Or.inr ⟨i, hi.symm⟩
  rw [← he, ← ho, ← finsum_mem_union' hdisj (hg.subset Set.inter_subset_right)
    (hg.subset Set.inter_subset_right), hunion, finsum_mem_univ]

/-- Splitting a sum over `ℤ` by parity, shifted by `r ∈ ℤ`:
`∑_i g(2i + r) + ∑_i g(2i + r + 1) = ∑_k g(k)` for every function `g` with finite support. -/
theorem finsum_two_mul_add_add_finsum {M : Type*} [AddCommMonoid M] {g : ℤ → M}
    (hg : (Function.support g).Finite) (r : ℤ) :
    ∑ᶠ i : ℤ, g (2 * i + r) + ∑ᶠ i : ℤ, g (2 * i + (r + 1)) = ∑ᶠ k : ℤ, g k := by
  have hg' : (Function.support fun k : ℤ => g (k + r)).Finite :=
    Function.HasFiniteSupport.fun_comp_of_injective (add_left_injective r) hg
  calc ∑ᶠ i : ℤ, g (2 * i + r) + ∑ᶠ i : ℤ, g (2 * i + (r + 1))
      = ∑ᶠ i : ℤ, g (2 * i + r) + ∑ᶠ i : ℤ, g (2 * i + 1 + r) := by
        simp only [show ∀ i : ℤ, 2 * i + (r + 1) = 2 * i + 1 + r from fun i => by ring]
    _ = ∑ᶠ k : ℤ, g (k + r) := finsum_two_mul_add_finsum_two_mul_add_one hg'
    _ = ∑ᶠ k : ℤ, g k := finsum_comp_equiv (Equiv.addRight r)

/-- The sum `∑_i g(2i + r)` over one parity class depends only on the parity of `r`:
`∑_i g(2i + r + 2q) = ∑_i g(2i + r)` for all `r, q ∈ ℤ`. -/
theorem finsum_two_mul_add_add_two_mul {M : Type*} [AddCommMonoid M] (g : ℤ → M) (r q : ℤ) :
    ∑ᶠ i : ℤ, g (2 * i + (r + 2 * q)) = ∑ᶠ i : ℤ, g (2 * i + r) := by
  calc ∑ᶠ i : ℤ, g (2 * i + (r + 2 * q)) = ∑ᶠ i : ℤ, g (2 * (i + q) + r) := by
        simp only [show ∀ i : ℤ, 2 * i + (r + 2 * q) = 2 * (i + q) + r from fun i => by ring]
    _ = ∑ᶠ i : ℤ, g (2 * i + r) :=
        finsum_comp_equiv (Equiv.addRight q) (f := fun i => g (2 * i + r))

/-- `(-1)^a = (-1)^b` for integers `a, b` of the same parity. -/
theorem neg_one_zpow_eq_of_even_sub {a b : ℤ} (h : Even (a - b)) :
    (-1 : ℝ) ^ a = (-1) ^ b := by
  obtain ⟨t, ht⟩ := h
  rw [show a = b + (t + t) by omega, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0),
    Even.neg_one_zpow ⟨t, rfl⟩, mul_one]

/-- `(-1)^a = -(-1)^b` for integers `a, b` of different parity. -/
theorem neg_one_zpow_eq_neg_of_odd_sub {a b : ℤ} (h : Odd (a - b)) :
    (-1 : ℝ) ^ a = -(-1) ^ b := by
  obtain ⟨t, ht⟩ := h
  rw [show a = b + (2 * t + 1) by omega, zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0),
    Odd.neg_one_zpow ⟨t, rfl⟩, mul_neg_one]

/-- **Equal parity sums.** If `g : ℤ → ℝ` has finite support and alternating sum
`∑_k (-1)^k g(k) = 0`, then each parity class carries half of the total:
`∑_i g(2i + r) = (1/2) ∑_k g(k)` for every `r ∈ ℤ`. -/
theorem finsum_two_mul_add_eq_half {g : ℤ → ℝ} (hg : (Function.support g).Finite)
    (halt : ∑ᶠ k : ℤ, (-1 : ℝ) ^ k * g k = 0) (r : ℤ) :
    ∑ᶠ i : ℤ, g (2 * i + r) = (∑ᶠ k : ℤ, g k) / 2 := by
  have hsplit := finsum_two_mul_add_add_finsum hg r
  have hg' : (Function.support fun k : ℤ => (-1 : ℝ) ^ k * g k).Finite :=
    hg.subset (Function.support_mul_subset_right _ _)
  have hsplit' := finsum_two_mul_add_add_finsum hg' r
  have he : ∀ i : ℤ, (-1 : ℝ) ^ (2 * i + r) = (-1) ^ r := fun i =>
    neg_one_zpow_eq_of_even_sub ⟨i, by ring⟩
  have ho : ∀ i : ℤ, (-1 : ℝ) ^ (2 * i + (r + 1)) = -(-1) ^ r := fun i =>
    neg_one_zpow_eq_neg_of_odd_sub ⟨i, by ring⟩
  simp only [he, ho, neg_mul, finsum_neg_distrib, ← mul_finsum] at hsplit'
  rw [halt] at hsplit'
  have hne : (-1 : ℝ) ^ r ≠ 0 := zpow_ne_zero _ (by norm_num)
  have hprod : (-1 : ℝ) ^ r * (∑ᶠ i : ℤ, g (2 * i + r) - ∑ᶠ i : ℤ, g (2 * i + (r + 1))) = 0 := by
    rw [mul_sub]
    linarith
  have heq := sub_eq_zero.1 ((mul_eq_zero.1 hprod).resolve_left hne)
  linarith

variable {N : ℕ} (m : Mask N)

/-! ### The filter coefficients as a function on `ℤ` -/

/-- The filter coefficients have finite support: they vanish outside `0 ≤ k < 2N`. -/
theorem finite_support_coeff : (Function.support (coeff m)).Finite :=
  (Set.finite_Ico 0 (2 * (N : ℤ))).subset fun k hk => by
    by_contra h
    simp only [Set.mem_Ico, not_and_or, not_le, not_lt] at h
    exact hk (coeff_eq_zero m h)

/-- A sum over `k ∈ ℤ` of a function that vanishes wherever the filter coefficients vanish is the
finite sum over `k = 0, …, 2N - 1`. -/
theorem finsum_eq_sum_range_of_coeff {M : Type*} [AddCommMonoid M] (f : ℤ → M)
    (hf : ∀ k : ℤ, coeff m k = 0 → f k = 0) :
    ∑ᶠ k : ℤ, f k = ∑ k ∈ Finset.range (2 * N), f k :=
  finsum_eq_sum_range_of_eq_zero fun k hk => hf k (coeff_eq_zero m (by push_cast at hk; exact hk))

/-- `∑_k c_k = 2`, as a sum over `k ∈ ℤ`. -/
theorem finsum_coeff : ∑ᶠ k : ℤ, coeff m k = 2 := by
  rw [finsum_eq_sum_range_of_coeff m (coeff m) fun k hk => hk, sum_coeff]

/-- **The symbol as a sum over `ℤ`**: `m_0(ξ) = (1/2) ∑_{k ∈ ℤ} c_k e^(-2πikξ)`. -/
theorem symbol_eq_finsum (ξ : ℝ) :
    symbol m ξ = 1 / 2 * ∑ᶠ k : ℤ, (coeff m k : ℂ) * expFreq (k * ξ) := by
  rw [symbol_eq_sum, finsum_eq_sum_range_of_coeff m _ fun k hk => by simp [hk]]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expFreq_pow, Int.cast_natCast]

/-! ### Trigonometric polynomials on `[0, 1]` -/

/-- `ξ ↦ e^(-2πicξ)` is continuous for every `c ∈ ℝ`. -/
theorem continuous_expFreq_mul (c : ℝ) : Continuous fun ξ : ℝ => expFreq (c * ξ) :=
  continuous_expFreq.comp (continuous_const_mul c)

/-- **Integrals of the exponentials over a period**: `∫_0^1 e^(-2πinξ) dξ` is `1` for `n = 0`
and `0` for every other integer `n`. -/
theorem integral_expFreq_intCast_mul (n : ℤ) :
    ∫ ξ in (0 : ℝ)..1, expFreq (n * ξ) = if n = 0 then 1 else 0 := by
  by_cases hn : n = 0
  · simp [hn]
  · have hc : -(2 * π * Complex.I) * n ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero, hn]
    have h : ∀ ξ : ℝ, expFreq (n * ξ) = Complex.exp (-(2 * π * Complex.I) * n * ξ) :=
      fun ξ => by
        rw [expFreq_eq_exp_mul]
        congr 1
        push_cast
        ring
    have h1 : Complex.exp (-(2 * π * Complex.I) * n * ((1 : ℝ) : ℂ)) = 1 := by
      rw [← h, mul_one, expFreq_intCast]
    simp_rw [h]
    rw [integral_exp_mul_complex hc, h1]
    simp [hn]

/-- **Orthonormality of the exponentials `e^(-2πikξ)` on `[0, 1]`**, for finite sums over a
finite set `u ⊆ ℤ` with coefficients `a, b : ℤ → ℂ`:
`∫_0^1 (∑_{k ∈ u} a_k e^(-2πikξ)) conj (∑_{k ∈ u} b_k e^(-2πikξ)) dξ = ∑_{k ∈ u} a_k conj b_k`. -/
theorem integral_sum_mul_conj_sum (u : Finset ℤ) (a b : ℤ → ℂ) :
    ∫ ξ in (0 : ℝ)..1, (∑ k ∈ u, a k * expFreq (k * ξ)) *
        conj (∑ k ∈ u, b k * expFreq (k * ξ)) = ∑ k ∈ u, a k * conj (b k) := by
  have hprod : ∀ ξ : ℝ, (∑ k ∈ u, a k * expFreq (k * ξ)) *
      conj (∑ k ∈ u, b k * expFreq (k * ξ)) =
      ∑ k ∈ u, ∑ l ∈ u, a k * conj (b l) * expFreq (((k - l : ℤ) : ℝ) * ξ) := fun ξ => by
    rw [map_sum, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    rw [map_mul, conj_expFreq, show ((k - l : ℤ) : ℝ) * ξ = k * ξ + -(l * ξ) by push_cast; ring,
      expFreq_add]
    ring
  have hcont : ∀ k l : ℤ,
      Continuous fun ξ : ℝ => a k * conj (b l) * expFreq (((k - l : ℤ) : ℝ) * ξ) :=
    fun k l => continuous_const.fun_mul (continuous_expFreq_mul _)
  simp_rw [hprod]
  rw [intervalIntegral.integral_finsetSum]
  · refine Finset.sum_congr rfl fun k hk => ?_
    rw [intervalIntegral.integral_finsetSum]
    · simp_rw [intervalIntegral.integral_const_mul, integral_expFreq_intCast_mul, sub_eq_zero,
        mul_ite, mul_one, mul_zero]
      rw [Finset.sum_ite_eq]
      simp only [hk, ↓reduceIte]
    · exact fun l _ => (hcont k l).intervalIntegrable _ _
  · exact fun k _ => (continuous_finsetSum _ fun l _ => hcont k l).intervalIntegrable _ _

/-- **Orthonormality of the exponentials `e^(-2πikξ)` on `[0, 1]`**, for coefficient sequences
`a, b : ℤ → ℂ` with finite support:
`∫_0^1 (∑_k a_k e^(-2πikξ)) conj (∑_k b_k e^(-2πikξ)) dξ = ∑_k a_k conj b_k`. -/
theorem integral_finsum_mul_conj_finsum {a b : ℤ → ℂ} (ha : (Function.support a).Finite)
    (hb : (Function.support b).Finite) :
    ∫ ξ in (0 : ℝ)..1, (∑ᶠ k : ℤ, a k * expFreq (k * ξ)) *
        conj (∑ᶠ k : ℤ, b k * expFreq (k * ξ)) = ∑ᶠ k : ℤ, a k * conj (b k) := by
  obtain ⟨u, hau, hbu⟩ : ∃ u : Finset ℤ,
      Function.support a ⊆ u ∧ Function.support b ⊆ u :=
    ⟨ha.toFinset ∪ hb.toFinset, by simp, by simp⟩
  have hA : ∀ ξ : ℝ, ∑ᶠ k : ℤ, a k * expFreq (k * ξ) = ∑ k ∈ u, a k * expFreq (k * ξ) :=
    fun ξ => finsum_eq_sum_of_support_subset _
      ((Function.support_mul_subset_left _ _).trans hau)
  have hB : ∀ ξ : ℝ, ∑ᶠ k : ℤ, b k * expFreq (k * ξ) = ∑ k ∈ u, b k * expFreq (k * ξ) :=
    fun ξ => finsum_eq_sum_of_support_subset _
      ((Function.support_mul_subset_left _ _).trans hbu)
  simp_rw [hA, hB]
  rw [integral_sum_mul_conj_sum]
  exact (finsum_eq_sum_of_support_subset _
    ((Function.support_mul_subset_left _ _).trans hau)).symm

/-- **Fourier coefficients of `|T|²`** for a trigonometric polynomial
`T(ξ) = ∑_k a_k e^(-2πikξ)` with finitely many nonzero `a_k ∈ ℂ`:
`∫_0^1 e^(-2πinξ) |T(ξ)|² dξ = ∑_k a_(k-n) conj a_k` for every `n ∈ ℤ`. -/
theorem integral_expFreq_mul_normSq_finsum {a : ℤ → ℂ} (ha : (Function.support a).Finite)
    (n : ℤ) :
    ∫ ξ in (0 : ℝ)..1, expFreq (n * ξ) * ((‖∑ᶠ k : ℤ, a k * expFreq (k * ξ)‖ ^ 2 : ℝ) : ℂ) =
      ∑ᶠ k : ℤ, a (k - n) * conj (a k) := by
  have ha' : (Function.support fun k : ℤ => a (k - n)).Finite :=
    Function.HasFiniteSupport.fun_comp_of_injective (sub_left_injective (b := n)) ha
  have hshift : ∀ ξ : ℝ, expFreq (n * ξ) * ∑ᶠ k : ℤ, a k * expFreq (k * ξ) =
      ∑ᶠ k : ℤ, a (k - n) * expFreq (k * ξ) := fun ξ => by
    rw [mul_finsum]
    calc ∑ᶠ k : ℤ, expFreq (n * ξ) * (a k * expFreq (k * ξ))
        = ∑ᶠ k : ℤ, a (k + n - n) * expFreq (((k + n : ℤ) : ℝ) * ξ) := by
          refine finsum_congr fun k => ?_
          rw [add_sub_cancel_right, mul_left_comm, ← expFreq_add]
          congr 2
          push_cast
          ring
      _ = ∑ᶠ k : ℤ, a (k - n) * expFreq (k * ξ) :=
          finsum_comp_equiv (Equiv.addRight n) (f := fun k : ℤ => a (k - n) * expFreq (k * ξ))
  have hnorm : ∀ ξ : ℝ,
      expFreq (n * ξ) * ((‖∑ᶠ k : ℤ, a k * expFreq (k * ξ)‖ ^ 2 : ℝ) : ℂ) =
      (∑ᶠ k : ℤ, a (k - n) * expFreq (k * ξ)) * conj (∑ᶠ k : ℤ, a k * expFreq (k * ξ)) :=
    fun ξ => by rw [Complex.ofReal_pow, ← Complex.mul_conj', ← mul_assoc, hshift]
  simp_rw [hnorm]
  exact integral_finsum_mul_conj_finsum ha' ha

/-! ### Orthogonality of the even shifts -/

/-- `|z/2|² = |z|²/4` for `z ∈ ℂ`. -/
theorem norm_half_mul_sq (z : ℂ) : ‖(1 / 2 : ℂ) * z‖ ^ 2 = 1 / 4 * ‖z‖ ^ 2 := by
  rw [norm_mul, mul_pow]
  norm_num

/-- **Fourier coefficients of `|m_0|²`**: for every `n ∈ ℤ`,
`∫_0^1 e^(-2πinξ) |m_0(ξ)|² dξ = (1/4) ∑_k c_(k-n) c_k`. -/
theorem integral_expFreq_mul_normSq_symbol (n : ℤ) :
    ∫ ξ in (0 : ℝ)..1, expFreq (n * ξ) * ((‖symbol m ξ‖ ^ 2 : ℝ) : ℂ) =
      1 / 4 * ∑ᶠ k : ℤ, ((coeff m (k - n) * coeff m k : ℝ) : ℂ) := by
  have hfin : (Function.support fun k : ℤ => (coeff m k : ℂ)).Finite :=
    (finite_support_coeff m).subset fun k hk => by simpa using hk
  have hsym : ∀ ξ : ℝ, expFreq (n * ξ) * ((‖symbol m ξ‖ ^ 2 : ℝ) : ℂ) = 1 / 4 *
      (expFreq (n * ξ) * ((‖∑ᶠ k : ℤ, (coeff m k : ℂ) * expFreq (k * ξ)‖ ^ 2 : ℝ) : ℂ)) :=
    fun ξ => by
      rw [symbol_eq_finsum, norm_half_mul_sq]
      push_cast
      ring
  simp_rw [hsym, intervalIntegral.integral_const_mul]
  rw [integral_expFreq_mul_normSq_finsum hfin n]
  congr 1
  refine finsum_congr fun k => ?_
  rw [Complex.conj_ofReal]
  push_cast
  ring

/-- For every integer `k`, the function `ξ ↦ e^(-2πikξ)` has period `1`, since `e^(-2πik) = 1`
(`Daubechies.expFreq_intCast`). -/
theorem periodic_expFreq_intCast_mul (k : ℤ) :
    Function.Periodic (fun ξ : ℝ => expFreq (k * ξ)) 1 := fun ξ => by
  simp only
  rw [mul_add, mul_one, expFreq_add, expFreq_intCast, mul_one]

/-- **Fourier coefficients of `|m_0(· + 1/2)|²`**: for every `n ∈ ℤ`,
`∫_0^1 e^(-2πinξ) |m_0(ξ + 1/2)|² dξ = (1/4) e^(πin) ∑_k c_(k-n) c_k`. The substitution
`η = ξ + 1/2` (Mathlib's `intervalIntegral.integral_comp_add_right`) gives the factor
`e^(-2πin(-1/2)) = e^(πin)` and the integral over `[1/2, 3/2]`, which is the integral over
`[0, 1]` since `η ↦ e^(-2πinη) |m_0(η)|²` has period `1`
(`Daubechies.periodic_expFreq_intCast_mul`, `Daubechies.symbol_periodic`, Mathlib's
`Function.Periodic.intervalIntegral_add_eq`); then `Daubechies.integral_expFreq_mul_normSq_symbol`
applies. -/
theorem integral_expFreq_mul_normSq_symbol_add_half (n : ℤ) :
    ∫ ξ in (0 : ℝ)..1, expFreq (n * ξ) * ((‖symbol m (ξ + 1 / 2)‖ ^ 2 : ℝ) : ℂ) =
      1 / 4 * expFreq (-(n : ℝ) / 2) * ∑ᶠ k : ℤ, ((coeff m (k - n) * coeff m k : ℝ) : ℂ) := by
  have hshift : ∀ ξ : ℝ, expFreq (n * ξ) * ((‖symbol m (ξ + 1 / 2)‖ ^ 2 : ℝ) : ℂ) =
      expFreq (-(n : ℝ) / 2) *
        (expFreq (n * (ξ + 1 / 2)) * ((‖symbol m (ξ + 1 / 2)‖ ^ 2 : ℝ) : ℂ)) := fun ξ => by
    rw [← mul_assoc, ← expFreq_add]
    congr 2
    ring
  have hper : Function.Periodic
      (fun η : ℝ => expFreq (n * η) * ((‖symbol m η‖ ^ 2 : ℝ) : ℂ)) 1 :=
    (periodic_expFreq_intCast_mul n).mul
      ((symbol_periodic m).comp fun z => ((‖z‖ ^ 2 : ℝ) : ℂ))
  simp_rw [hshift, intervalIntegral.integral_const_mul]
  rw [intervalIntegral.integral_comp_add_right
      (fun η : ℝ => expFreq (n * η) * ((‖symbol m η‖ ^ 2 : ℝ) : ℂ)), zero_add,
    add_comm (1 : ℝ), hper.intervalIntegral_add_eq (1 / 2) 0, zero_add,
    integral_expFreq_mul_normSq_symbol m n]
  ring

/-- **Orthogonality of the even shifts of the filter**: `∑_k c_k c_(k+2j) = 2 δ_(j0)` for every
`j ∈ ℤ`. Integrating the quadrature mirror filter identity
`|m_0(ξ)|² + |m_0(ξ + 1/2)|² = 1` (`Daubechies.qmf`) against `e^(2πi·2jξ)` over `[0, 1]` gives
`(1/4) ∑_k c_k c_(k+2j) + (1/4) ∑_k c_k c_(k+2j) = δ_(j0)`. -/
theorem sum_coeff_mul_coeff_add (j : ℤ) :
    ∑ᶠ k : ℤ, coeff m k * coeff m (k + 2 * j) = if j = 0 then 2 else 0 := by
  have hc1 : Continuous fun ξ : ℝ =>
      expFreq (((-(2 * j) : ℤ) : ℝ) * ξ) * ((‖symbol m ξ‖ ^ 2 : ℝ) : ℂ) :=
    (continuous_expFreq_mul _).mul
      (Complex.continuous_ofReal.comp ((continuous_symbol m).norm.pow 2))
  have hc2 : Continuous fun ξ : ℝ =>
      expFreq (((-(2 * j) : ℤ) : ℝ) * ξ) * ((‖symbol m (ξ + 1 / 2)‖ ^ 2 : ℝ) : ℂ) :=
    (continuous_expFreq_mul _).mul (Complex.continuous_ofReal.comp
      (((continuous_symbol m).comp (continuous_add_const (1 / 2))).norm.pow 2))
  have h : (∫ ξ in (0 : ℝ)..1,
        expFreq (((-(2 * j) : ℤ) : ℝ) * ξ) * ((‖symbol m ξ‖ ^ 2 : ℝ) : ℂ)) +
      (∫ ξ in (0 : ℝ)..1,
        expFreq (((-(2 * j) : ℤ) : ℝ) * ξ) * ((‖symbol m (ξ + 1 / 2)‖ ^ 2 : ℝ) : ℂ)) =
      if -(2 * j) = 0 then 1 else 0 := by
    rw [← intervalIntegral.integral_add (hc1.intervalIntegrable 0 1) (hc2.intervalIntegrable 0 1),
      ← integral_expFreq_intCast_mul]
    refine intervalIntegral.integral_congr fun ξ _ => ?_
    rw [← mul_add, ← Complex.ofReal_add, qmf, Complex.ofReal_one, mul_one]
  have hE : expFreq (-(((-(2 * j) : ℤ) : ℝ)) / 2) = 1 := by
    rw [show -(((-(2 * j) : ℤ) : ℝ)) / 2 = ((j : ℤ) : ℝ) by push_cast; ring]
    exact expFreq_intCast j
  have hS : ∑ᶠ k : ℤ, ((coeff m (k - -(2 * j)) * coeff m k : ℝ) : ℂ) =
      ((∑ᶠ k : ℤ, coeff m k * coeff m (k + 2 * j) : ℝ) : ℂ) := by
    rw [finsum_eq_sum_range_of_coeff m
        (fun k : ℤ => ((coeff m (k - -(2 * j)) * coeff m k : ℝ) : ℂ)) fun k hk => by simp [hk],
      finsum_eq_sum_range_of_coeff m (fun k : ℤ => coeff m k * coeff m (k + 2 * j))
        fun k hk => by simp [hk], Complex.ofReal_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [sub_neg_eq_add, mul_comm]
  have hite : (if -(2 * j) = 0 then (1 : ℂ) else 0) =
      ((if j = 0 then 2 else 0 : ℝ) : ℂ) / 2 := by
    by_cases hj : j = 0
    · norm_num [hj]
    · simp [hj, show -(2 * j) ≠ 0 by omega]
  rw [integral_expFreq_mul_normSq_symbol, integral_expFreq_mul_normSq_symbol_add_half, hE,
    mul_one, hS, hite] at h
  have h2 : ((∑ᶠ k : ℤ, coeff m k * coeff m (k + 2 * j) : ℝ) : ℂ) =
      ((if j = 0 then 2 else 0 : ℝ) : ℂ) := by
    linear_combination 2 * h
  exact_mod_cast h2

/-! ### Sum rules -/

/-- **The Euler operator on coefficients**: the `k`-th coefficient of `X p'` is `k` times the
`k`-th coefficient of `p`. -/
theorem coeff_X_mul_derivative (p : ℝ[X]) (k : ℕ) :
    (X * derivative p).coeff k = k * p.coeff k := by
  cases k with
  | zero => simp
  | succ k =>
    rw [coeff_X_mul, coeff_derivative]
    push_cast
    ring

/-- The `l`-th iterate of the Euler operator `p ↦ X p'` multiplies the `k`-th coefficient by
`k^l`. -/
theorem coeff_iterate_X_mul_derivative (p : ℝ[X]) (l k : ℕ) :
    ((fun q : ℝ[X] => X * derivative q)^[l] p).coeff k = (k : ℝ) ^ l * p.coeff k := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [Function.iterate_succ_apply', coeff_X_mul_derivative, ih]
    ring

/-- If `(X + 1)^j` divides `p`, then `(X + 1)^(j - l)` divides the `l`-th iterate of the Euler
operator `p ↦ X p'` applied to `p`: each step differentiates once (Mathlib's
`Polynomial.pow_sub_one_dvd_derivative_of_pow_dvd`) and multiplies by `X`. -/
theorem pow_dvd_iterate_X_mul_derivative {p : ℝ[X]} {j : ℕ} (h : (X + 1) ^ j ∣ p) (l : ℕ) :
    (X + 1) ^ (j - l) ∣ (fun q : ℝ[X] => X * derivative q)^[l] p := by
  induction l with
  | zero => simpa using h
  | succ l ih =>
    rw [Function.iterate_succ_apply', show j - (l + 1) = j - l - 1 by omega]
    exact (pow_sub_one_dvd_derivative_of_pow_dvd ih).mul_left X

/-- **Sum rules for polynomials divisible by `(X + 1)^j`**: if `(X + 1)^j ∣ p`, `l < j` and
`deg p < n`, then `∑_{k < n} (-1)^k k^l [X^k] p = 0`. The sum is the value at `-1` of the `l`-th
iterate of the Euler operator `p ↦ X p'`, which is still divisible by `X + 1`. -/
theorem sum_range_neg_one_pow_mul_pow_mul_coeff {p : ℝ[X]} {j l n : ℕ} (h : (X + 1) ^ j ∣ p)
    (hl : l < j) (hn : p.natDegree < n) :
    ∑ k ∈ Finset.range n, (-1) ^ k * (k : ℝ) ^ l * p.coeff k = 0 := by
  have hdeg : ((fun q : ℝ[X] => X * derivative q)^[l] p).natDegree < n := by
    refine lt_of_le_of_lt ?_ hn
    rw [natDegree_le_iff_coeff_eq_zero]
    intro k hk
    rw [coeff_iterate_X_mul_derivative, coeff_eq_zero_of_natDegree_lt hk, mul_zero]
  have hdvd : X - C (-1) ∣ (fun q : ℝ[X] => X * derivative q)^[l] p := by
    rw [C_neg, C_1, sub_neg_eq_add]
    exact (dvd_pow_self (X + 1) (by omega)).trans (pow_dvd_iterate_X_mul_derivative h l)
  have hroot := (dvd_iff_isRoot.1 hdvd).eq_zero
  rw [eval_eq_sum_range' hdeg] at hroot
  refine Eq.trans (Finset.sum_congr rfl fun k _ => ?_) hroot
  rw [coeff_iterate_X_mul_derivative]
  ring

/-- **The sum rules** as finite sums over `k = 0, …, 2N - 1`:
`∑_{k < 2N} (-1)^k k^l c_k = 0` for `l < N`. -/
theorem sum_range_rule {l : ℕ} (hl : l < N) :
    ∑ k ∈ Finset.range (2 * N), (-1) ^ k * (k : ℝ) ^ l * coeff m k = 0 := by
  have h := sum_range_neg_one_pow_mul_pow_mul_coeff (X_add_one_pow_dvd_maskPoly m) hl
    (natDegree_maskPoly_lt m)
  calc ∑ k ∈ Finset.range (2 * N), (-1) ^ k * (k : ℝ) ^ l * coeff m k
      = 2 * ∑ k ∈ Finset.range (2 * N), (-1) ^ k * (k : ℝ) ^ l * (maskPoly m).coeff k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [coeff_natCast]
        ring
    _ = 0 := by rw [h, mul_zero]

/-- **The sum rules** `∑_k (-1)^k k^l c_k = 0` for `l < N`, as a sum over `k ∈ ℤ`. They express
that the mask polynomial is divisible by `(z + 1)^N` (`Daubechies.X_add_one_pow_dvd_maskPoly`). -/
theorem sum_rule {l : ℕ} (hl : l < N) :
    ∑ᶠ k : ℤ, (-1 : ℝ) ^ k * (k : ℝ) ^ l * coeff m k = 0 := by
  rw [finsum_eq_sum_range_of_coeff m _ fun k hk => by rw [hk, mul_zero]]
  simpa only [zpow_natCast, Int.cast_natCast] using sum_range_rule m hl

/-- **The sum rules for polynomials**: `∑_k (-1)^k Q(k) c_k = 0` for every real polynomial `Q`
of degree `< N`, a linear combination of the sum rules `Daubechies.sum_rule`. -/
theorem sum_rule_poly {Q : ℝ[X]} (hQ : Q.natDegree < N) :
    ∑ᶠ k : ℤ, (-1 : ℝ) ^ k * Q.eval (k : ℝ) * coeff m k = 0 := by
  rw [finsum_eq_sum_range_of_coeff m _ fun k hk => by rw [hk, mul_zero]]
  simp only [zpow_natCast, Int.cast_natCast, eval_eq_sum_range' hQ, Finset.mul_sum,
    Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_eq_zero fun i hi => ?_
  calc ∑ k ∈ Finset.range (2 * N), (-1) ^ k * (Q.coeff i * (k : ℝ) ^ i) * coeff m k
      = Q.coeff i * ∑ k ∈ Finset.range (2 * N), (-1) ^ k * (k : ℝ) ^ i * coeff m k := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        ring
    _ = 0 := by rw [sum_range_rule m (Finset.mem_range.1 hi), mul_zero]

/-! ### Parity sums and first moments -/

/-- The alternating sum of the filter coefficients vanishes: `∑_k (-1)^k c_k = 0`, the sum rule
for `l = 0`; equivalently `m_0(1/2) = 0`. -/
theorem finsum_neg_one_zpow_mul_coeff : ∑ᶠ k : ℤ, (-1 : ℝ) ^ k * coeff m k = 0 := by
  simpa using sum_rule m (l := 0) m.one_le

/-- **The parity sums** `∑_i c_(2i+r) = 1` for every `r ∈ ℤ`: the filter coefficients with even
and with odd indices each add up to `1`, since `∑_k c_k = 2` and `∑_k (-1)^k c_k = 0`. -/
theorem sum_coeff_two_mul_add (r : ℤ) : ∑ᶠ i : ℤ, coeff m (2 * i + r) = 1 := by
  rw [finsum_two_mul_add_eq_half (finite_support_coeff m) (finsum_neg_one_zpow_mul_coeff m) r,
    finsum_coeff]
  norm_num

/-- The filter coefficients with even indices add up to `1`: `∑_i c_(2i) = 1`. -/
theorem sum_coeff_two_mul : ∑ᶠ i : ℤ, coeff m (2 * i) = 1 := by
  simpa using sum_coeff_two_mul_add m 0

/-- The filter coefficients with odd indices add up to `1`: `∑_i c_(2i+1) = 1`. -/
theorem sum_coeff_two_mul_add_one : ∑ᶠ i : ℤ, coeff m (2 * i + 1) = 1 :=
  sum_coeff_two_mul_add m 1

/-- **The first moment** `μ = (1/2) ∑_k k c_k` of the filter coefficients. -/
noncomputable def firstMoment : ℝ := 1 / 2 * ∑ᶠ k : ℤ, (k : ℝ) * coeff m k

/-- **The first moments of the two parity classes** (`N ≥ 2`): `∑_i (2i + r) c_(2i+r) = μ` for
every `r ∈ ℤ`, where `μ = (1/2) ∑_k k c_k`. By the sum rule for `l = 1`, the even and the odd
indices contribute equally to `∑_k k c_k = 2μ`. -/
theorem sum_two_mul_add_mul_coeff (hN : 2 ≤ N) (r : ℤ) :
    ∑ᶠ i : ℤ, (2 * (i : ℝ) + r) * coeff m (2 * i + r) = firstMoment m := by
  have hfin : (Function.support fun k : ℤ => (k : ℝ) * coeff m k).Finite :=
    (finite_support_coeff m).subset (Function.support_mul_subset_right _ _)
  have halt : ∑ᶠ k : ℤ, (-1 : ℝ) ^ k * ((k : ℝ) * coeff m k) = 0 := by
    simpa only [pow_one, mul_assoc] using sum_rule m (l := 1) (by omega)
  calc ∑ᶠ i : ℤ, (2 * (i : ℝ) + r) * coeff m (2 * i + r)
      = ∑ᶠ i : ℤ, ((2 * i + r : ℤ) : ℝ) * coeff m (2 * i + r) :=
        finsum_congr fun i => by push_cast; ring
    _ = (∑ᶠ k : ℤ, (k : ℝ) * coeff m k) / 2 := finsum_two_mul_add_eq_half hfin halt r
    _ = firstMoment m := by rw [firstMoment]; ring

/-- **The index moments of the two parity classes** (`N ≥ 2`): `∑_i i c_(2i+r) = (μ - r)/2` for
every `r ∈ ℤ`, where `μ = (1/2) ∑_k k c_k`. It follows from `∑_i (2i + r) c_(2i+r) = μ`
(`Daubechies.sum_two_mul_add_mul_coeff`) and `∑_i c_(2i+r) = 1`
(`Daubechies.sum_coeff_two_mul_add`). -/
theorem sum_mul_coeff_two_mul_add (hN : 2 ≤ N) (r : ℤ) :
    ∑ᶠ i : ℤ, (i : ℝ) * coeff m (2 * i + r) = (firstMoment m - r) / 2 := by
  have hinj : Function.Injective fun i : ℤ => 2 * i + r := fun i j h => by
    simp only at h
    omega
  have hfin : (Function.support fun i : ℤ => coeff m (2 * i + r)).Finite :=
    Function.HasFiniteSupport.fun_comp_of_injective hinj (finite_support_coeff m)
  have h1 : (Function.support fun i : ℤ => 2 * (i : ℝ) * coeff m (2 * i + r)).Finite :=
    hfin.subset (Function.support_mul_subset_right _ _)
  have h2 : (Function.support fun i : ℤ => (r : ℝ) * coeff m (2 * i + r)).Finite :=
    hfin.subset (Function.support_mul_subset_right _ _)
  have h := sum_two_mul_add_mul_coeff m hN r
  simp only [add_mul] at h
  rw [finsum_add_distrib h1 h2, ← mul_finsum, sum_coeff_two_mul_add, mul_one] at h
  simp only [mul_assoc] at h
  rw [← mul_finsum] at h
  linarith

/-! ### Derivatives of the symbol -/

/-- **Derivatives of a finite exponential sum** in a real variable: for `a_i, b_i ∈ ℂ`,
`(d/dt)^l ∑_i a_i e^(b_i t) = ∑_i a_i b_i^l e^(b_i t)`. Mathlib's
`iteratedDeriv_cexp_const_mul` is the version for a complex variable. -/
theorem iteratedDeriv_sum_mul_cexp {ι : Type*} (s : Finset ι) (a b : ι → ℂ) (l : ℕ) :
    iteratedDeriv l (fun t : ℝ => ∑ i ∈ s, a i * Complex.exp (b i * t)) =
      fun t : ℝ => ∑ i ∈ s, a i * b i ^ l * Complex.exp (b i * t) := by
  induction l with
  | zero => simp
  | succ l ih =>
    rw [iteratedDeriv_succ, ih]
    funext t
    refine HasDerivAt.deriv (HasDerivAt.fun_sum fun i _ => ?_)
    have h1 : HasDerivAt (fun y : ℝ => b i * (y : ℂ)) (b i) t := by
      simpa only [mul_one] using! ((hasDerivAt_id (t : ℂ)).const_mul (b i)).comp_ofReal
    convert h1.cexp.const_mul (a i * b i ^ l) using 1
    ring

/-- The symbol as a finite exponential sum: `m_0(ξ) = ∑_{k < 2N} (c_k/2) e^(-2πikξ)`. -/
theorem symbol_eq_sum_cexp :
    symbol m = fun ξ : ℝ => ∑ k ∈ Finset.range (2 * N),
      (coeff m k / 2 : ℂ) * Complex.exp (-(2 * π * Complex.I * k) * ξ) := by
  funext ξ
  rw [symbol_eq_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expFreq_pow, expFreq_eq_exp_mul,
    show -(2 * (π : ℂ) * Complex.I * k) * ξ = -(2 * π * Complex.I) * ((k * ξ : ℝ) : ℂ) by
      push_cast; ring]
  ring

/-- **The derivatives of the symbol**: `m_0^(l)(ξ) = ∑_{k < 2N} (c_k/2) (-2πik)^l e^(-2πikξ)`. -/
theorem iteratedDeriv_symbol (l : ℕ) (ξ : ℝ) :
    iteratedDeriv l (symbol m) ξ = ∑ k ∈ Finset.range (2 * N),
      (coeff m k / 2 : ℂ) * (-(2 * π * Complex.I * k)) ^ l * expFreq ξ ^ k := by
  rw [symbol_eq_sum_cexp, iteratedDeriv_sum_mul_cexp]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [expFreq_pow, expFreq_eq_exp_mul]
  congr 2
  push_cast
  ring

/-- **The derivatives of the symbol vanish at the half-integers** up to order `N - 1`:
`m_0^(l)(1/2 + n) = 0` for `l < N` and `n ∈ ℤ`. At `ξ = 1/2 + n` one has
`e^(-2πikξ) = (-1)^k`, so `m_0^(l)(1/2 + n) = (1/2) (-2πi)^l ∑_k (-1)^k k^l c_k`, which vanishes
by the sum rules. -/
theorem iteratedDeriv_symbol_half_add_int {l : ℕ} (hl : l < N) (n : ℤ) :
    iteratedDeriv l (symbol m) (1 / 2 + n) = 0 := by
  have h : ∑ k ∈ Finset.range (2 * N), ((-1) ^ k * (k : ℂ) ^ l * coeff m k) = 0 := by
    exact_mod_cast sum_range_rule m hl
  rw [iteratedDeriv_symbol, expFreq_half_add_int]
  calc ∑ k ∈ Finset.range (2 * N),
        (coeff m k / 2 : ℂ) * (-(2 * π * Complex.I * k)) ^ l * (-1) ^ k
      = (-(2 * π * Complex.I)) ^ l / 2 *
          ∑ k ∈ Finset.range (2 * N), ((-1) ^ k * (k : ℂ) ^ l * coeff m k) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [show -(2 * (π : ℂ) * Complex.I * k) = -(2 * π * Complex.I) * k by ring, mul_pow]
        ring
    _ = 0 := by rw [h, mul_zero]

/-! ### The dual filter -/

/-- **The dual filter** `g_k = (-1)^k c_(1-k)` of a mask, the coefficients of the refinement
equation `ψ(x) = ∑_k g_k φ(2x - k)` of the wavelet. They vanish outside `2 - 2N ≤ k ≤ 1`
(`Daubechies.dualCoeff_eq_zero`). -/
noncomputable def dualCoeff (k : ℤ) : ℝ := (-1) ^ k * coeff m (1 - k)

/-- The dual filter vanishes outside `2 - 2N ≤ k ≤ 1`. -/
theorem dualCoeff_eq_zero {k : ℤ} (hk : k < 2 - 2 * (N : ℤ) ∨ 1 < k) : dualCoeff m k = 0 := by
  rw [dualCoeff, coeff_eq_zero m (by omega), mul_zero]

/-- The dual filter has finite support. -/
theorem finite_support_dualCoeff : (Function.support (dualCoeff m)).Finite :=
  (Set.finite_Icc (2 - 2 * (N : ℤ)) 1).subset fun k hk => by
    by_contra h
    simp only [Set.mem_Icc, not_and_or, not_le] at h
    exact hk (dualCoeff_eq_zero m h)

/-- A sum over `k ∈ ℤ` of a function that vanishes wherever the dual filter vanishes is the
finite sum over `2 - 2N ≤ k ≤ 1`. -/
theorem finsum_eq_sum_Icc_of_dualCoeff {M : Type*} [AddCommMonoid M] (f : ℤ → M)
    (hf : ∀ k : ℤ, dualCoeff m k = 0 → f k = 0) :
    ∑ᶠ k : ℤ, f k = ∑ k ∈ Finset.Icc (2 - 2 * (N : ℤ)) 1, f k :=
  finsum_eq_sum_of_support_subset f fun k hk => by
    rw [Finset.coe_Icc, Set.mem_Icc]
    by_contra h
    rw [not_and_or, not_le, not_le] at h
    exact hk (hf k (dualCoeff_eq_zero m h))

/-- **Orthogonality of the even shifts of the dual filter**: `∑_k g_k g_(k+2j) = 2 δ_(j0)` for
every `j ∈ ℤ`. The substitution `k ↦ 1 - 2j - k` turns the sum into `∑_k c_k c_(k+2j)`
(`Daubechies.sum_coeff_mul_coeff_add`). -/
theorem sum_dualCoeff_mul_dualCoeff_add (j : ℤ) :
    ∑ᶠ k : ℤ, dualCoeff m k * dualCoeff m (k + 2 * j) = if j = 0 then 2 else 0 := by
  calc ∑ᶠ k : ℤ, dualCoeff m k * dualCoeff m (k + 2 * j)
      = ∑ᶠ k : ℤ, dualCoeff m (1 - 2 * j - k) * dualCoeff m (1 - 2 * j - k + 2 * j) :=
        (finsum_comp_equiv (Equiv.subLeft (1 - 2 * j))
          (f := fun k => dualCoeff m k * dualCoeff m (k + 2 * j))).symm
    _ = ∑ᶠ k : ℤ, coeff m k * coeff m (k + 2 * j) := finsum_congr fun k => by
        simp only [dualCoeff]
        rw [show 1 - (1 - 2 * j - k) = k + 2 * j by ring,
          show 1 - 2 * j - k + 2 * j = 1 - k by ring, show 1 - (1 - k) = k by ring,
          neg_one_zpow_eq_of_even_sub (a := 1 - 2 * j - k) (b := 1 - k) ⟨-j, by ring⟩]
        have h1 : (-1 : ℝ) ^ (1 - k) * (-1) ^ (1 - k) = 1 := by
          rw [← zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0)]
          exact Even.neg_one_zpow ⟨1 - k, rfl⟩
        calc (-1) ^ (1 - k) * coeff m (k + 2 * j) * ((-1) ^ (1 - k) * coeff m k)
            = ((-1) ^ (1 - k) * (-1) ^ (1 - k)) * (coeff m k * coeff m (k + 2 * j)) := by ring
          _ = coeff m k * coeff m (k + 2 * j) := by rw [h1, one_mul]
    _ = if j = 0 then 2 else 0 := sum_coeff_mul_coeff_add m j

/-- **The dual filter is orthogonal to the even shifts of the filter**: `∑_k c_k g_(k+2j) = 0`
for every `j ∈ ℤ`. The substitution `k ↦ 1 - 2j - k` maps the sum to its negative. -/
theorem sum_coeff_mul_dualCoeff_add (j : ℤ) :
    ∑ᶠ k : ℤ, coeff m k * dualCoeff m (k + 2 * j) = 0 := by
  have h : ∑ᶠ k : ℤ, coeff m k * dualCoeff m (k + 2 * j) =
      -∑ᶠ k : ℤ, coeff m k * dualCoeff m (k + 2 * j) := by
    rw [← finsum_neg_distrib]
    calc ∑ᶠ k : ℤ, coeff m k * dualCoeff m (k + 2 * j)
        = ∑ᶠ k : ℤ, coeff m (1 - 2 * j - k) * dualCoeff m (1 - 2 * j - k + 2 * j) :=
          (finsum_comp_equiv (Equiv.subLeft (1 - 2 * j))
            (f := fun k => coeff m k * dualCoeff m (k + 2 * j))).symm
      _ = ∑ᶠ k : ℤ, -(coeff m k * dualCoeff m (k + 2 * j)) := finsum_congr fun k => by
          simp only [dualCoeff]
          rw [show 1 - (1 - 2 * j - k + 2 * j) = k by ring,
            show 1 - 2 * j - k + 2 * j = 1 - k by ring,
            show 1 - (k + 2 * j) = 1 - 2 * j - k by ring,
            neg_one_zpow_eq_neg_of_odd_sub (a := 1 - k) (b := k + 2 * j) ⟨-k - j, by ring⟩]
          ring
  linarith

/-- Reindexing a sum of products of filter coefficients over one parity class:
`∑_j c_(a-2j) c_(b-2j) = ∑_i c_(2i+b+(a-b)) c_(2i+b)`. -/
theorem finsum_coeff_sub_two_mul_mul (a b : ℤ) :
    ∑ᶠ j : ℤ, coeff m (a - 2 * j) * coeff m (b - 2 * j) =
      ∑ᶠ i : ℤ, coeff m (2 * i + b + (a - b)) * coeff m (2 * i + b) := by
  calc ∑ᶠ j : ℤ, coeff m (a - 2 * j) * coeff m (b - 2 * j)
      = ∑ᶠ i : ℤ, coeff m (a - 2 * -i) * coeff m (b - 2 * -i) :=
        (finsum_comp_equiv (Equiv.neg ℤ)
          (f := fun j => coeff m (a - 2 * j) * coeff m (b - 2 * j))).symm
    _ = ∑ᶠ i : ℤ, coeff m (2 * i + b + (a - b)) * coeff m (2 * i + b) :=
        finsum_congr fun i => by
          rw [show a - 2 * -i = 2 * i + b + (a - b) by ring, show b - 2 * -i = 2 * i + b by ring]

/-- Reindexing a sum of products of dual filter coefficients over one parity class:
`∑_j g_(a-2j) g_(b-2j) = (-1)^(a+b) ∑_i c_(2i+(1-a)+(a-b)) c_(2i+(1-a))`. -/
theorem finsum_dualCoeff_sub_two_mul_mul (a b : ℤ) :
    ∑ᶠ j : ℤ, dualCoeff m (a - 2 * j) * dualCoeff m (b - 2 * j) =
      (-1) ^ (a + b) *
        ∑ᶠ i : ℤ, coeff m (2 * i + (1 - a) + (a - b)) * coeff m (2 * i + (1 - a)) := by
  rw [mul_finsum]
  refine finsum_congr fun j => ?_
  simp only [dualCoeff]
  rw [neg_one_zpow_eq_of_even_sub (a := a - 2 * j) (b := a) ⟨-j, by ring⟩,
    neg_one_zpow_eq_of_even_sub (a := b - 2 * j) (b := b) ⟨-j, by ring⟩,
    zpow_add₀ (by norm_num : (-1 : ℝ) ≠ 0), show 1 - (a - 2 * j) = 2 * j + (1 - a) by ring,
    show 1 - (b - 2 * j) = 2 * j + (1 - a) + (a - b) by ring]
  ring

/-- **The filter and its dual resolve the identity**: for all `a, b ∈ ℤ`,
`∑_j (c_(a-2j) c_(b-2j) + g_(a-2j) g_(b-2j)) = 2 δ_(ab)`. Both sums run over one parity class
of the products `h(k) = c_(k+(a-b)) c_k`. For `a - b` even the two classes are complementary and
the sum is `∑_k c_k c_(k+(a-b)) = 2 δ_(ab)` (`Daubechies.sum_coeff_mul_coeff_add`); for `a - b`
odd the two classes agree and the sign `(-1)^(a+b) = -1` makes them cancel. -/
theorem sum_coeff_mul_add_dual (a b : ℤ) :
    ∑ᶠ j : ℤ, (coeff m (a - 2 * j) * coeff m (b - 2 * j) +
      dualCoeff m (a - 2 * j) * dualCoeff m (b - 2 * j)) = if a = b then 2 else 0 := by
  have hinj : Function.Injective fun j : ℤ => b - 2 * j := fun i j hij => by
    simp only at hij
    omega
  have hfin1 : (Function.support fun j : ℤ =>
      coeff m (a - 2 * j) * coeff m (b - 2 * j)).Finite :=
    Set.Finite.subset (Function.HasFiniteSupport.fun_comp_of_injective hinj
      (finite_support_coeff m)) (Function.support_mul_subset_right _ _)
  have hfin2 : (Function.support fun j : ℤ =>
      dualCoeff m (a - 2 * j) * dualCoeff m (b - 2 * j)).Finite :=
    Set.Finite.subset (Function.HasFiniteSupport.fun_comp_of_injective hinj
      (finite_support_dualCoeff m)) (Function.support_mul_subset_right _ _)
  have hfinh : (Function.support fun k : ℤ => coeff m (k + (a - b)) * coeff m k).Finite :=
    (finite_support_coeff m).subset (Function.support_mul_subset_right _ _)
  rw [finsum_add_distrib hfin1 hfin2, finsum_coeff_sub_two_mul_mul,
    finsum_dualCoeff_sub_two_mul_mul]
  rcases Int.even_or_odd (a - b) with ⟨t, ht⟩ | ⟨t, ht⟩
  · rw [Even.neg_one_zpow ⟨b + t, by omega⟩, one_mul,
      show 1 - a = b + 1 + 2 * (-b - t) by omega,
      finsum_two_mul_add_add_two_mul (fun k : ℤ => coeff m (k + (a - b)) * coeff m k),
      finsum_two_mul_add_add_finsum hfinh b, show a - b = 2 * t by omega]
    rw [finsum_congr fun k => mul_comm (coeff m (k + 2 * t)) (coeff m k),
      sum_coeff_mul_coeff_add m t]
    simp only [show t = 0 ↔ a = b by omega]
  · rw [Odd.neg_one_zpow ⟨b + t, by omega⟩, show 1 - a = b + 2 * (-b - t) by omega,
      finsum_two_mul_add_add_two_mul (fun k : ℤ => coeff m (k + (a - b)) * coeff m k)]
    simp only [show ¬a = b by omega, ↓reduceIte]
    ring

/-- **Vanishing moments of the dual filter**: `∑_k g_k k^l = 0` for `l < N`. The substitution
`k ↦ 1 - k` turns the sum into `-∑_k (-1)^k (1 - k)^l c_k`, which vanishes by the sum rules for
the polynomial `(1 - X)^l` of degree `l < N` (`Daubechies.sum_rule_poly`). -/
theorem sum_dualCoeff_mul_pow {l : ℕ} (hl : l < N) :
    ∑ᶠ k : ℤ, dualCoeff m k * (k : ℝ) ^ l = 0 := by
  have hdeg : ((1 - X : ℝ[X]) ^ l).natDegree < N := by
    have h1 : (1 - X : ℝ[X]).natDegree ≤ 1 := (natDegree_sub_le _ _).trans (by simp)
    exact (natDegree_pow_le_of_le l h1).trans_lt (by omega)
  calc ∑ᶠ k : ℤ, dualCoeff m k * (k : ℝ) ^ l
      = ∑ᶠ k : ℤ, dualCoeff m (1 - k) * ((1 - k : ℤ) : ℝ) ^ l :=
        (finsum_comp_equiv (Equiv.subLeft 1) (f := fun k => dualCoeff m k * (k : ℝ) ^ l)).symm
    _ = ∑ᶠ k : ℤ, -((-1 : ℝ) ^ k * ((1 - X : ℝ[X]) ^ l).eval (k : ℝ) * coeff m k) :=
        finsum_congr fun k => by
          simp only [dualCoeff]
          rw [show (1 : ℤ) - (1 - k) = k by ring,
            neg_one_zpow_eq_neg_of_odd_sub (a := 1 - k) (b := k) ⟨-k, by ring⟩]
          simp only [eval_pow, eval_sub, eval_one, eval_X]
          push_cast
          ring
    _ = 0 := by rw [finsum_neg_distrib, sum_rule_poly m hdeg, neg_zero]

end Daubechies
