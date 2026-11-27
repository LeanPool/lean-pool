/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import Mathlib.Algebra.Polynomial.Roots
public import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
public import Mathlib.Data.Nat.Choose.Sum
public import Mathlib.Topology.Algebra.Polynomial

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# The Daubechies polynomial

The orthonormal wavelets of Daubechies of order `N` are built from the polynomial
`P_N(y) = ∑_{k < N} C(N - 1 + k, k) y^k` (`Daubechies.daubPoly`), the first `N` terms of the
binomial series `(1 - y)^(-N) = ∑_k C(N - 1 + k, k) y^k`. Its key property is the
**Bézout identity**
`(1 - y)^N P_N(y) + y^N P_N(1 - y) = 1` for `N ≥ 1`
(`Daubechies.daubPoly_bezout`; evaluated: `Daubechies.eval_daubPoly_bezout`). It follows by
induction on `N`, starting from `P_1 = 1`, from the recurrence
`(1 - y) P_{N+1}(y) = P_N(y) + C(2N - 1, N) y^N - C(2N, N) y^(N+1)`
(`Daubechies.one_sub_mul_eval_daubPoly_succ`, as polynomials
`Daubechies.one_sub_X_mul_daubPoly_succ`; Pascal's rule) and `C(2N, N) = 2 C(2N - 1, N)`
(`Daubechies.choose_two_mul_eq_two_mul_choose`): from `N` to `N + 1` the summand
`(1 - y)^N P_N(y)` changes by `y^N (1 - y)^N (C(2N - 1, N) - C(2N, N) y)`, the summand
`y^N P_N(1 - y)` by `y^N (1 - y)^N (C(2N - 1, N) - C(2N, N) (1 - y))`, and these changes cancel.

**Values and bounds.** For `N ≥ 1`: `P_N(0) = 1`, `P_N(1) = C(2N - 1, N)` (the hockey-stick
identity, Mathlib's `Nat.sum_range_add_choose`), and for `0 ≤ y ≤ 1`
`1 ≤ P_N(y) ≤ 1 + C(2N - 1, N) y` (`Daubechies.one_le_eval_daubPoly`,
`Daubechies.eval_daubPoly_le`), since `y^k ≤ y` for `k ≥ 1`. For `N ≥ 2`,
`C(2N - 1, N) < 4^(N - 1)` (`Daubechies.choose_lt_four_pow`, from Mathlib's
`Nat.sum_range_choose_halfway`).

**The trigonometric form** `P(ξ) = P_N(sin²(πξ))` (`Daubechies.daubFun`) is the squared modulus
`|L(e^(-2πiξ))|²` of the polynomial factor `L` of a Daubechies mask of order `N`. It is
continuous, even and `1`-periodic, `P(ξ + 1/2) = P_N(cos²(πξ))`, `P(ξ) ≤ C(2N - 1, N)`,
`1 ≤ P(ξ)` for `N ≥ 1`, and `P(ξ) ≤ 1 + C(2N - 1, N) π² ξ²` (`Daubechies.daubFun_le`, from
`sin²(πξ) ≤ π² ξ²`). At
`y = sin²(πξ)`, where `1 - y = cos²(πξ)`, the Bézout identity becomes
`cos(πξ)^(2N) P(ξ) + sin(πξ)^(2N) P(ξ + 1/2) = 1` (`Daubechies.daubFun_bezout`), the source of
the quadrature mirror filter identity of the Daubechies masks.
-/

@[expose] public section

open Polynomial
open scoped Real

namespace Daubechies

/-! ### The polynomial `P_N` -/

/-- **The Daubechies polynomial** of order `N`: `P_N(y) = ∑_{k < N} C(N - 1 + k, k) y^k`, the
first `N` terms of the binomial series `(1 - y)^(-N) = ∑_k C(N - 1 + k, k) y^k`. For `N = 0`
it is the zero polynomial. -/
noncomputable def daubPoly (N : ℕ) : ℝ[X] :=
  ∑ k ∈ Finset.range N, C ((N - 1 + k).choose k : ℝ) * X ^ k

/-- The value of `P_N` at a real number `y`: `P_N(y) = ∑_{k < N} C(N - 1 + k, k) y^k`. -/
theorem eval_daubPoly (N : ℕ) (y : ℝ) :
    (daubPoly N).eval y = ∑ k ∈ Finset.range N, ((N - 1 + k).choose k : ℝ) * y ^ k := by
  simp only [daubPoly, eval_finsetSum, eval_mul, eval_C, eval_pow, eval_X]

/-- `P_0 = 0`, the empty sum. -/
theorem daubPoly_zero : daubPoly 0 = 0 := by
  simp [daubPoly]

/-- `P_1 = 1`. -/
theorem daubPoly_one : daubPoly 1 = 1 := by
  simp [daubPoly]

/-- `P_2(y) = 1 + 2y`, the polynomial of the wavelet D4. -/
theorem daubPoly_two : daubPoly 2 = 1 + 2 * X := by
  refine Polynomial.funext fun y => ?_
  simp [eval_daubPoly, Finset.sum_range_succ]

/-- `P_3(y) = 1 + 3y + 6y²`. -/
theorem daubPoly_three : daubPoly 3 = 1 + 3 * X + 6 * X ^ 2 := by
  refine Polynomial.funext fun y => ?_
  simp [eval_daubPoly, Finset.sum_range_succ, Nat.choose]

/-- `P_N` has degree at most `N - 1`. -/
theorem natDegree_daubPoly_le (N : ℕ) : (daubPoly N).natDegree ≤ N - 1 :=
  natDegree_sum_le_of_forall_le _ _ fun k hk =>
    (natDegree_C_mul_X_pow_le _ k).trans (by rw [Finset.mem_range] at hk; omega)

/-- The constant term of `P_{M+1}` is `1`:
`P_{M+1}(y) = 1 + ∑_{k < M} C(M + k + 1, k + 1) y^(k+1)`. -/
theorem eval_daubPoly_succ_eq_one_add (M : ℕ) (y : ℝ) :
    (daubPoly (M + 1)).eval y =
      1 + ∑ k ∈ Finset.range M, ((M + (k + 1)).choose (k + 1) : ℝ) * y ^ (k + 1) := by
  rw [eval_daubPoly, Finset.sum_range_succ', add_comm]
  simp

/-- `P_N(0) = 1` for `N ≥ 1`: only the constant term `C(N - 1, 0) = 1` survives. -/
theorem eval_zero_daubPoly {N : ℕ} (hN : 1 ≤ N) : (daubPoly N).eval 0 = 1 := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  simp [eval_daubPoly_succ_eq_one_add]

/-- **The value at `1`**: `P_N(1) = ∑_{k < N} C(N - 1 + k, k) = C(2N - 1, N)` for `N ≥ 1`, by the
symmetry `C(N - 1 + k, k) = C(N - 1 + k, N - 1)` (Mathlib's `Nat.choose_symm_add`) and the
hockey-stick identity `∑_{i ≤ n} C(i + m, m) = C(n + m + 1, m + 1)` (`Nat.sum_range_add_choose`). -/
theorem eval_one_daubPoly {N : ℕ} (hN : 1 ≤ N) :
    (daubPoly N).eval 1 = (2 * N - 1).choose N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  have h : ∑ k ∈ Finset.range (M + 1), (M + 1 - 1 + k).choose k =
      (2 * (M + 1) - 1).choose (M + 1) := by
    rw [show 2 * (M + 1) - 1 = M + M + 1 by omega, ← Nat.sum_range_add_choose M M]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Nat.add_sub_cancel, add_comm M k]
    exact Nat.choose_symm_add
  rw [eval_daubPoly]
  simp only [one_pow, mul_one]
  exact_mod_cast h

/-! ### The recurrence and the Bézout identity -/

/-- **The recurrence of the Daubechies polynomials**, evaluated: for every `N` and every real `y`,
`(1 - y) P_{N+1}(y) = P_N(y) + C(2N - 1, N) y^N - C(2N, N) y^(N+1)`.
On the left the constant term is `1`, the coefficient of `y^(k+1)` for `k < N` is
`C(N + k + 1, k + 1) - C(N + k, k) = C(N + k, k + 1)` (Pascal's rule, Mathlib's
`Nat.choose_succ_succ'`), and the top term is `-C(2N, N) y^(N+1)`; on the right
`P_N(y) + C(2N - 1, N) y^N = ∑_{k ≤ N} C(N - 1 + k, k) y^k` has the same coefficients. -/
theorem one_sub_mul_eval_daubPoly_succ (N : ℕ) (y : ℝ) :
    (1 - y) * (daubPoly (N + 1)).eval y = (daubPoly N).eval y +
      ((2 * N - 1).choose N : ℝ) * y ^ N - ((2 * N).choose N : ℝ) * y ^ (N + 1) := by
  -- `P_{N+1}(y)`, with Pascal's rule applied to the coefficients of `y^(k+1)`
  have hA : (daubPoly (N + 1)).eval y = 1 + ∑ k ∈ Finset.range N,
      ((N + k).choose k : ℝ) * y ^ (k + 1) + ∑ k ∈ Finset.range N,
      ((N + k).choose (k + 1) : ℝ) * y ^ (k + 1) := by
    rw [eval_daubPoly_succ_eq_one_add, add_assoc, ← Finset.sum_add_distrib]
    congr 1
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← add_mul, ← Nat.cast_add, ← Nat.choose_succ_succ', add_assoc]
  -- `y P_{N+1}(y)`, with the top term split off
  have hB : y * (daubPoly (N + 1)).eval y = ∑ k ∈ Finset.range N,
      ((N + k).choose k : ℝ) * y ^ (k + 1) + ((2 * N).choose N : ℝ) * y ^ (N + 1) := by
    rw [eval_daubPoly, Finset.mul_sum, Finset.sum_range_succ]
    congr 1
    · refine Finset.sum_congr rfl fun k _ => ?_
      rw [show N + 1 - 1 + k = N + k by omega]
      ring
    · rw [show N + 1 - 1 + N = 2 * N by omega]
      ring
  -- `P_N(y) + C(2N - 1, N) y^N`, with the constant term split off
  have hC : (daubPoly N).eval y + ((2 * N - 1).choose N : ℝ) * y ^ N = 1 + ∑ k ∈ Finset.range N,
      ((N + k).choose (k + 1) : ℝ) * y ^ (k + 1) := by
    have h : (daubPoly N).eval y + ((2 * N - 1).choose N : ℝ) * y ^ N =
        ∑ k ∈ Finset.range (N + 1), ((N - 1 + k).choose k : ℝ) * y ^ k := by
      rw [Finset.sum_range_succ, eval_daubPoly, show N - 1 + N = 2 * N - 1 by omega]
    rw [h, Finset.sum_range_succ', add_comm]
    congr 1
    · simp
    · refine Finset.sum_congr rfl fun k hk => ?_
      rw [Finset.mem_range] at hk
      rw [show N - 1 + (k + 1) = N + k by omega]
  linear_combination hA - hB - hC

/-- **The recurrence of the Daubechies polynomials** as an identity of polynomials:
`(1 - X) P_{N+1} = P_N + C(2N - 1, N) X^N - C(2N, N) X^(N+1)` for every `N`. -/
theorem one_sub_X_mul_daubPoly_succ (N : ℕ) :
    (1 - X) * daubPoly (N + 1) = daubPoly N + C ((2 * N - 1).choose N : ℝ) * X ^ N -
      C ((2 * N).choose N : ℝ) * X ^ (N + 1) := by
  refine Polynomial.funext fun y => ?_
  simp only [eval_mul, eval_sub, eval_one, eval_X, eval_add, eval_C, eval_pow]
  exact one_sub_mul_eval_daubPoly_succ N y

/-- `C(2N, N) = 2 C(2N - 1, N)` for `N ≥ 1`: Pascal's rule
`C(2N, N) = C(2N - 1, N - 1) + C(2N - 1, N)` and the symmetry `C(2N - 1, N - 1) = C(2N - 1, N)`
(Mathlib's `Nat.choose_symm_half`). -/
theorem choose_two_mul_eq_two_mul_choose {N : ℕ} (hN : 1 ≤ N) :
    (2 * N).choose N = 2 * (2 * N - 1).choose N := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [show 2 * (M + 1) - 1 = 2 * M + 1 by omega, show 2 * (M + 1) = 2 * M + 1 + 1 by ring,
    Nat.choose_succ_succ' (2 * M + 1) M, Nat.choose_symm_half M]
  ring

/-- **The induction step of the Bézout identity**: for `N ≥ 1` the Bézout sum
`(1 - y)^N P_N(y) + y^N P_N(1 - y)` takes the same value at `N + 1` as at `N`. By the recurrence
the first summand changes by `y^N (1 - y)^N (C(2N - 1, N) - C(2N, N) y)` and the second by
`y^N (1 - y)^N (C(2N - 1, N) - C(2N, N) (1 - y))`; the changes add up to
`y^N (1 - y)^N (2 C(2N - 1, N) - C(2N, N)) = 0`. -/
theorem eval_daubPoly_bezout_succ {N : ℕ} (hN : 1 ≤ N) (y : ℝ) :
    (1 - y) ^ (N + 1) * (daubPoly (N + 1)).eval y +
        y ^ (N + 1) * (daubPoly (N + 1)).eval (1 - y) =
      (1 - y) ^ N * (daubPoly N).eval y + y ^ N * (daubPoly N).eval (1 - y) := by
  have h1 := one_sub_mul_eval_daubPoly_succ N y
  have h2 := one_sub_mul_eval_daubPoly_succ N (1 - y)
  have hc : ((2 * N).choose N : ℝ) = 2 * ((2 * N - 1).choose N : ℝ) := by
    exact_mod_cast choose_two_mul_eq_two_mul_choose hN
  linear_combination (1 - y) ^ N * h1 + y ^ N * h2 - y ^ N * (1 - y) ^ N * hc

/-- **The Bézout identity of the Daubechies polynomials**, evaluated:
`(1 - y)^N P_N(y) + y^N P_N(1 - y) = 1` for `N ≥ 1` and every real `y`, by induction from
`P_1 = 1`, where it reads `(1 - y) + y = 1`. -/
theorem eval_daubPoly_bezout {N : ℕ} (hN : 1 ≤ N) (y : ℝ) :
    (1 - y) ^ N * (daubPoly N).eval y + y ^ N * (daubPoly N).eval (1 - y) = 1 := by
  induction N, hN using Nat.le_induction with
  | base => simp [daubPoly_one]
  | succ N hN ih => rw [eval_daubPoly_bezout_succ hN, ih]

/-- **The Bézout identity of the Daubechies polynomials**:
`(1 - X)^N P_N + X^N P_N(1 - X) = 1` for `N ≥ 1`. It follows from the evaluated form
`Daubechies.eval_daubPoly_bezout`, since two real polynomials with the same values at every
real number are equal (Mathlib's `Polynomial.funext`). -/
theorem daubPoly_bezout {N : ℕ} (hN : 1 ≤ N) :
    (1 - X) ^ N * daubPoly N + X ^ N * (daubPoly N).comp (1 - X) = 1 := by
  refine Polynomial.funext fun y => ?_
  simp only [eval_add, eval_mul, eval_pow, eval_sub, eval_one, eval_X, eval_comp]
  exact eval_daubPoly_bezout hN y

/-! ### Bounds -/

/-- `P_N(y) ≥ 0` for `y ≥ 0`: all coefficients of `P_N` are nonnegative. -/
theorem eval_daubPoly_nonneg (N : ℕ) {y : ℝ} (hy : 0 ≤ y) : 0 ≤ (daubPoly N).eval y := by
  rw [eval_daubPoly]
  exact Finset.sum_nonneg fun k _ => by positivity

/-- `P_N(y) ≥ 1` for `y ≥ 0` and `N ≥ 1`: the constant term is `1`, and the other terms are
nonnegative. -/
theorem one_le_eval_daubPoly {N : ℕ} (hN : 1 ≤ N) {y : ℝ} (hy : 0 ≤ y) :
    1 ≤ (daubPoly N).eval y := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [eval_daubPoly_succ_eq_one_add]
  have : 0 ≤ ∑ k ∈ Finset.range M, ((M + (k + 1)).choose (k + 1) : ℝ) * y ^ (k + 1) :=
    Finset.sum_nonneg fun k _ => by positivity
  linarith

/-- On `[0, 1]` the polynomial `P_N` is bounded by its value at `1`, since `y^k ≤ 1` there. -/
theorem eval_daubPoly_le_eval_one (N : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (daubPoly N).eval y ≤ (daubPoly N).eval 1 := by
  rw [eval_daubPoly, eval_daubPoly]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [one_pow, mul_one]
  exact mul_le_of_le_one_right (Nat.cast_nonneg _) (pow_le_one₀ hy0 hy1)

/-- `P_N(y) ≤ 1 + C(2N - 1, N) y` for `0 ≤ y ≤ 1` and every `N`: the constant term is `1`, the
other terms satisfy `y^k ≤ y`, and their coefficients add up to `P_N(1) - 1 = C(2N - 1, N) - 1`
(for `N = 0` the left side is `0`). -/
theorem eval_daubPoly_le (N : ℕ) {y : ℝ} (hy0 : 0 ≤ y) (hy1 : y ≤ 1) :
    (daubPoly N).eval y ≤ 1 + ((2 * N - 1).choose N : ℝ) * y := by
  rcases N with _ | M
  · simp only [daubPoly_zero, eval_zero]
    positivity
  · have h1 := eval_one_daubPoly (N := M + 1) (by omega)
    rw [eval_daubPoly_succ_eq_one_add] at h1 ⊢
    simp only [one_pow, mul_one] at h1
    have hle : ∑ k ∈ Finset.range M, ((M + (k + 1)).choose (k + 1) : ℝ) * y ^ (k + 1) ≤
        (∑ k ∈ Finset.range M, ((M + (k + 1)).choose (k + 1) : ℝ)) * y := by
      rw [Finset.sum_mul]
      refine Finset.sum_le_sum fun k _ => ?_
      exact mul_le_mul_of_nonneg_left (pow_le_of_le_one hy0 hy1 (by omega)) (Nat.cast_nonneg _)
    have hS : (∑ k ∈ Finset.range M, ((M + (k + 1)).choose (k + 1) : ℝ)) ≤
        ((2 * (M + 1) - 1).choose (M + 1) : ℝ) := by
      linarith
    have := mul_le_mul_of_nonneg_right hS hy0
    linarith

/-- `C(2N - 1, N) < 4^(N - 1)` for `N ≥ 2`. With `N = M + 1`, `C(2M + 1, M + 1) = C(2M + 1, M)`
is a term of `∑_{i ≤ M} C(2M + 1, i) = 4^M` (Mathlib's `Nat.sum_range_choose_halfway`), and so is
`C(2M + 1, 0) = 1` since `M ≥ 1`. Equivalently `N - log₄(2 C(2N - 1, N)) > 1/2`. -/
theorem choose_lt_four_pow {N : ℕ} (hN : 2 ≤ N) : (2 * N - 1).choose N < 4 ^ (N - 1) := by
  obtain ⟨M, rfl⟩ : ∃ M, N = M + 1 := ⟨N - 1, by omega⟩
  rw [show 2 * (M + 1) - 1 = 2 * M + 1 by omega, Nat.add_sub_cancel, Nat.choose_symm_half,
    ← Nat.sum_range_choose_halfway M, Finset.sum_range_succ]
  have h0 : 1 ≤ ∑ i ∈ Finset.range M, (2 * M + 1).choose i := by
    have := Finset.single_le_sum (f := fun i => (2 * M + 1).choose i) (fun i _ => Nat.zero_le _)
      (Finset.mem_range.2 (show 0 < M by omega))
    simpa using this
  omega

/-! ### The trigonometric polynomial `P(ξ) = P_N(sin²(πξ))` -/

/-- **The trigonometric Daubechies polynomial** of order `N`: `P(ξ) = P_N(sin²(πξ))`. A
Daubechies mask of order `N` has a polynomial factor `L` with `|L(e^(-2πiξ))|² = P(ξ)`. -/
noncomputable def daubFun (N : ℕ) (ξ : ℝ) : ℝ := (daubPoly N).eval (Real.sin (π * ξ) ^ 2)

/-- `P` has period `1`, since `sin(π(ξ + 1)) = -sin(πξ)`. -/
theorem daubFun_periodic (N : ℕ) : Function.Periodic (daubFun N) 1 := fun ξ => by
  simp only [daubFun, mul_add, mul_one, Real.sin_add_pi, neg_sq]

/-- `P` is even: `P(-ξ) = P(ξ)`. -/
theorem daubFun_neg (N : ℕ) (ξ : ℝ) : daubFun N (-ξ) = daubFun N ξ := by
  simp only [daubFun, mul_neg, Real.sin_neg, neg_sq]

/-- `P(ξ + 1/2) = P_N(cos²(πξ))`, since `sin(π(ξ + 1/2)) = cos(πξ)`. -/
theorem daubFun_add_half (N : ℕ) (ξ : ℝ) :
    daubFun N (ξ + 1 / 2) = (daubPoly N).eval (Real.cos (π * ξ) ^ 2) := by
  rw [daubFun, show π * (ξ + 1 / 2) = π * ξ + π / 2 by ring, Real.sin_add_pi_div_two]

/-- `P(0) = P_N(0) = 1` for `N ≥ 1`. -/
theorem daubFun_zero {N : ℕ} (hN : 1 ≤ N) : daubFun N 0 = 1 := by
  simp [daubFun, eval_zero_daubPoly hN]

/-- For `N = 2`: `P(ξ) = 1 + 2 sin²(πξ)`. -/
theorem daubFun_two (ξ : ℝ) : daubFun 2 ξ = 1 + 2 * Real.sin (π * ξ) ^ 2 := by
  simp [daubFun, daubPoly_two]

/-- For `N = 3`: `P(ξ) = 1 + 3 sin²(πξ) + 6 sin⁴(πξ)`. -/
theorem daubFun_three (ξ : ℝ) :
    daubFun 3 ξ = 1 + 3 * Real.sin (π * ξ) ^ 2 + 6 * Real.sin (π * ξ) ^ 4 := by
  simp only [daubFun, daubPoly_three, eval_add, eval_mul, eval_pow, eval_X, eval_one,
    eval_ofNat]
  ring

/-- `P ≥ 0`. -/
theorem daubFun_nonneg (N : ℕ) (ξ : ℝ) : 0 ≤ daubFun N ξ :=
  eval_daubPoly_nonneg N (sq_nonneg _)

/-- `P ≥ 1` for `N ≥ 1`. -/
theorem one_le_daubFun {N : ℕ} (hN : 1 ≤ N) (ξ : ℝ) : 1 ≤ daubFun N ξ :=
  one_le_eval_daubPoly hN (sq_nonneg _)

/-- `P ≤ C(2N - 1, N)` for every `N`: for `N ≥ 1` this is the value of `P_N` at `1`, the maximum
of `P_N` on `[0, 1]`. -/
theorem daubFun_le_choose (N : ℕ) (ξ : ℝ) : daubFun N ξ ≤ (2 * N - 1).choose N := by
  rcases N with _ | M
  · simp [daubFun, daubPoly_zero]
  · rw [← eval_one_daubPoly (by omega)]
    exact eval_daubPoly_le_eval_one _ (sq_nonneg _) (Real.sin_sq_le_one _)

/-- `P(ξ) ≤ 1 + C(2N - 1, N) π² ξ²`, from `P_N(y) ≤ 1 + C(2N - 1, N) y` on `[0, 1]` and
`sin²(πξ) ≤ π² ξ²` (Mathlib's `Real.sin_sq_le_sq`). -/
theorem daubFun_le (N : ℕ) (ξ : ℝ) :
    daubFun N ξ ≤ 1 + ((2 * N - 1).choose N : ℝ) * π ^ 2 * ξ ^ 2 := by
  have h := eval_daubPoly_le N (sq_nonneg (Real.sin (π * ξ))) (Real.sin_sq_le_one _)
  have hs : Real.sin (π * ξ) ^ 2 ≤ π ^ 2 * ξ ^ 2 := by
    rw [← mul_pow]
    exact Real.sin_sq_le_sq
  calc daubFun N ξ ≤ 1 + ((2 * N - 1).choose N : ℝ) * Real.sin (π * ξ) ^ 2 := h
    _ ≤ 1 + ((2 * N - 1).choose N : ℝ) * (π ^ 2 * ξ ^ 2) := by gcongr
    _ = 1 + ((2 * N - 1).choose N : ℝ) * π ^ 2 * ξ ^ 2 := by ring

/-- `P` is continuous. -/
theorem continuous_daubFun (N : ℕ) : Continuous (daubFun N) := by
  unfold daubFun
  fun_prop

/-- **The trigonometric Bézout identity**: `cos(πξ)^(2N) P(ξ) + sin(πξ)^(2N) P(ξ + 1/2) = 1` for
`N ≥ 1`. This is the Bézout identity at `y = sin²(πξ)`, where `cos²(πξ) = 1 - y` and
`P(ξ + 1/2) = P_N(1 - y)`; it gives the quadrature mirror filter identity
`|m_0(ξ)|² + |m_0(ξ + 1/2)|² = 1` of the Daubechies masks. -/
theorem daubFun_bezout {N : ℕ} (hN : 1 ≤ N) (ξ : ℝ) :
    Real.cos (π * ξ) ^ (2 * N) * daubFun N ξ +
      Real.sin (π * ξ) ^ (2 * N) * daubFun N (ξ + 1 / 2) = 1 := by
  rw [daubFun_add_half, daubFun, pow_mul, pow_mul, Real.cos_sq']
  exact eval_daubPoly_bezout hN _

end Daubechies
