/-
Copyright (c) 2026 Mario Ullrich. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Mario Ullrich
-/
module

public import LeanPool.FunctionSpaces.Domains.Interval.Differences
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.ExpansionScaling
public import LeanPool.FunctionSpaces.Wavelets.Examples.Daubechies.ScalingMoments

/-
Modified for Lean Pool: module names and imports adapted.
-/

/-!
# Polynomial reproduction by the integer translates of the scaling function

For a Daubechies mask of order `N ≥ 2` with scaling function `φ` (`Daubechies.scalingFun`), this
file proves that the integer translates `φ(· - k)`, `k ∈ ℤ`, reproduce the polynomials of degree
`< N`: for every complex polynomial `Q` of degree `< N` and every `x ∈ ℝ`,

`∑_{k ∈ ℤ} ⟨Q, φ(· - k)⟩ φ(x - k) = Q(x)`, where `⟨Q, φ(· - k)⟩ = ∫ Q(y) conj φ(y - k) dy`

(`Daubechies.sum_inner_poly_mul_scalingFun`), and at every dyadic level `j ∈ ℕ`,
`∑_{k ∈ ℤ} 2^j (∫ Q(y) conj φ(2^j y - k) dy) φ(2^j x - k) = Q(x)`
(`Daubechies.sum_inner_poly_mul_scalingFun_two_pow`). Since `φ` vanishes outside `[0, 2N - 1]`,
each of these sums has only finitely many nonzero terms.

* **Integer moments.** Write `k = x - (x - k)` and expand `k^l` by the binomial theorem. The
  periodised moments `∑_k (x - k)^r φ(x - k) = μ_r := ∫ y^r φ(y) dy`, `r < N`
  (`Daubechies.periodization_moment_eq`), give
  `∑_k k^l φ(x - k) = ∑_{i=0}^{l} C(l, i) (-1)^(l-i) μ_(l-i) x^i`
  (`Daubechies.tsum_intCast_pow_mul_scalingFun_sub`), a monic polynomial of degree `l` in `x`
  for `l < N`, since `μ_0 = ∫ φ = 1` (`Daubechies.exists_poly_sum_pow_mul`).
* **Polynomial coefficients.** By induction on the degree, every polynomial `Q` of degree `< N`
  is `Q(x) = ∑_k a(k) φ(x - k)` with a polynomial `a`: subtracting the coefficient of `x^n` in
  `Q` times the monic polynomial `∑_k k^n φ(x - k)` lowers the degree
  (`Daubechies.exists_coeff_poly`).
* **Coefficient recovery.** The integer translates are the generators of level `0` of the
  expansions in `φ`, so coefficient recovery
  `∫ (∑_j a(j) φ(y - j)) conj φ(y - k) dy = a(k)` for every sequence `a : ℤ → ℂ`
  (`Daubechies.integral_tsum_mul_scalingFun_sub_mul_conj`) is the level `0` case of
  `Daubechies.coeffFun_expand_scalingFun`. For `Q = ∑_j a(j) φ(· - j)` this is
  `⟨Q, φ(· - k)⟩ = a(k)`, and the projection identity follows. Its dyadic form is the identity
  for the polynomial `Q(2^(-j) ·)` after the substitution `u = 2^j y`
  (`Daubechies.integral_eq_two_pow_mul_integral_comp`).
-/

@[expose] public section

open MeasureTheory
open scoped ComplexConjugate Polynomial

namespace Daubechies

/-! ### Lowering the degree of a polynomial -/

/-- **Lowering the degree of a polynomial**: let `Q` have degree `< n + 1`, and let `P` have
degree `≤ n` and coefficient `1` at `X^n`. Then `Q - q_n P` has degree `< n`, where `q_n` is the
coefficient of `X^n` in `Q`: the coefficients at `X^n` cancel, and both polynomials have no terms
of higher degree. -/
theorem sub_C_coeff_mul_mem_degreeLT {R : Type*} [Ring R] {n : ℕ} {Q P : R[X]}
    (hQ : Q ∈ Polynomial.degreeLT R (n + 1)) (hP : P.natDegree ≤ n) (hPn : P.coeff n = 1) :
    Q - Polynomial.C (Q.coeff n) * P ∈ Polynomial.degreeLT R n := by
  rw [Polynomial.mem_degreeLT, Polynomial.degree_lt_iff_coeff_zero]
  intro k hk
  rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul]
  rcases hk.eq_or_lt with rfl | hk
  · rw [hPn, mul_one, sub_self]
  · rw [(Polynomial.degree_lt_iff_coeff_zero Q (n + 1)).1 (Polynomial.mem_degreeLT.1 hQ) k hk,
      Polynomial.coeff_eq_zero_of_natDegree_lt (hP.trans_lt hk), mul_zero, sub_zero]

variable {N : ℕ} (m : Mask N)

/-! ### The integer moments of the translates -/

/-- **The integer moments of the translates, as a polynomial in `x`**: for `N ≥ 2`, `l < N` and
every `x ∈ ℝ`,
`∑_{k ∈ ℤ} k^l φ(x - k) = ∑_{i=0}^{l} C(l, i) (-1)^(l-i) μ_(l-i) x^i`,
where `μ_r = ∫ y^r φ(y) dy` are the moments of `φ`. Write `k = x + (-(x - k))` and expand `k^l`
by the binomial theorem (Mathlib's `add_pow`); exchange the finite sum over `i` with the sum over
`k` (each sum over `k` has only finitely many nonzero terms,
`Daubechies.summable_mul_scalingFun_sub`), and use that the periodised moments
`∑_k (x - k)^r φ(x - k)` equal `μ_r` for `r < N` (`Daubechies.periodization_moment_eq`). -/
theorem tsum_intCast_pow_mul_scalingFun_sub (hN : 2 ≤ N) {l : ℕ} (hl : l < N) (x : ℝ) :
    ∑' k : ℤ, (k : ℂ) ^ l * scalingFun m (x - k) =
      ∑ i ∈ Finset.range (l + 1), (l.choose i : ℂ) * (-1) ^ (l - i) *
        (∫ y : ℝ, (y : ℂ) ^ (l - i) * scalingFun m y) * (x : ℂ) ^ i := by
  have h : ∀ k : ℤ, (k : ℂ) ^ l * scalingFun m (x - k) =
      ∑ i ∈ Finset.range (l + 1), (l.choose i : ℂ) * (-1) ^ (l - i) * (x : ℂ) ^ i *
        (((x - k : ℝ) : ℂ) ^ (l - i) * scalingFun m (x - k)) := fun k => by
    have hk : (k : ℂ) = (x : ℂ) + -((x - k : ℝ) : ℂ) := by push_cast; ring
    rw [hk, add_pow, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [neg_pow]
    ring
  have hs : ∀ i ∈ Finset.range (l + 1), Summable fun k : ℤ =>
      (l.choose i : ℂ) * (-1) ^ (l - i) * (x : ℂ) ^ i *
        (((x - k : ℝ) : ℂ) ^ (l - i) * scalingFun m (x - k)) := fun i _ =>
    (summable_mul_scalingFun_sub m hN _ x).mul_left _
  rw [tsum_congr h, Summable.tsum_finsetSum hs]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [tsum_mul_left, periodization_moment_eq m hN ((Nat.sub_le l i).trans_lt hl) x]
  ring

/-- **The integer moments of the translates are polynomials**: for `N ≥ 2` and `l < N` there is
a polynomial `Q` of degree `≤ l` with coefficient `1` at `X^l` (so `Q` is monic of degree `l`)
such that `∑_{k ∈ ℤ} k^l φ(x - k) = Q(x)` for every `x ∈ ℝ`. The polynomial is
`Q = ∑_{i=0}^{l} C(l, i) (-1)^(l-i) μ_(l-i) X^i` with the moments `μ_r = ∫ y^r φ(y) dy`
(`Daubechies.tsum_intCast_pow_mul_scalingFun_sub`); its coefficient at `X^l` is
`μ_0 = ∫ φ = 1` (`Daubechies.integral_scalingFun`). -/
theorem exists_poly_sum_pow_mul (hN : 2 ≤ N) {l : ℕ} (hl : l < N) :
    ∃ Q : ℂ[X], Q.natDegree ≤ l ∧ Q.coeff l = 1 ∧
      ∀ x : ℝ, ∑' k : ℤ, (k : ℂ) ^ l * scalingFun m (x - k) = Q.eval (x : ℂ) := by
  refine ⟨∑ i ∈ Finset.range (l + 1), Polynomial.C ((l.choose i : ℂ) * (-1) ^ (l - i) *
      ∫ y : ℝ, (y : ℂ) ^ (l - i) * scalingFun m y) * Polynomial.X ^ i, ?_, ?_, fun x => ?_⟩
  · exact Polynomial.natDegree_sum_le_of_forall_le _ _ fun i hi =>
      (Polynomial.natDegree_C_mul_X_pow_le _ _).trans (Nat.lt_succ_iff.1 (Finset.mem_range.1 hi))
  · simp only [Polynomial.finsetSum_coeff, Polynomial.coeff_C_mul_X_pow, Finset.sum_ite_eq,
      Finset.mem_range, Nat.lt_succ_self, ↓reduceIte, Nat.choose_self, Nat.sub_self, pow_zero,
      one_mul, integral_scalingFun m hN, Nat.cast_one, mul_one]
  · rw [tsum_intCast_pow_mul_scalingFun_sub m hN hl x, Polynomial.eval_finsetSum]
    simp only [Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]

/-! ### Every polynomial of degree `< N` is a combination of the translates -/

/-- **Polynomials of degree `< n` as combinations of the translates, with polynomial
coefficients**: for `N ≥ 2`, `n ≤ N` and every polynomial `Q` of degree `< n` there is a
polynomial `a` of degree `< n` with `Q(x) = ∑_{k ∈ ℤ} a(k) φ(x - k)` for every `x ∈ ℝ`. Induction
on `n`. For `n = 0` the polynomial `Q` is zero. For the step, let `q_n` be the coefficient of
`X^n` in `Q` and let `P` be the monic polynomial of degree `n` with
`P(x) = ∑_k k^n φ(x - k)` (`Daubechies.exists_poly_sum_pow_mul`, since `n < N`). The polynomial
`Q - q_n P` has degree `< n` (`Daubechies.sub_C_coeff_mul_mem_degreeLT`), so by induction it is
`∑_k a'(k) φ(x - k)` with `a'` of degree `< n`, and `a = q_n X^n + a'` represents `Q`. -/
theorem exists_coeff_poly_of_mem_degreeLT (hN : 2 ≤ N) {n : ℕ} (hn : n ≤ N) {Q : ℂ[X]}
    (hQ : Q ∈ Polynomial.degreeLT ℂ n) :
    ∃ a ∈ Polynomial.degreeLT ℂ n,
      ∀ x : ℝ, Q.eval (x : ℂ) = ∑' k : ℤ, a.eval (k : ℂ) * scalingFun m (x - k) := by
  induction n generalizing Q with
  | zero =>
    have hQ0 : Q = 0 := AddMonoidAlgebra.ext <| Finsupp.ext fun i => by
      simpa using (Polynomial.degree_lt_iff_coeff_zero Q 0).1 (Polynomial.mem_degreeLT.1 hQ) i
        (Nat.zero_le i)
    exact ⟨0, Submodule.zero_mem _, fun x => by simp [hQ0]⟩
  | succ n ih =>
    obtain ⟨P, hPdeg, hPn, hP⟩ := exists_poly_sum_pow_mul m hN (l := n) (by omega)
    obtain ⟨a, ha, hQa⟩ := ih (by omega) (sub_C_coeff_mul_mem_degreeLT hQ hPdeg hPn)
    have hXn : Polynomial.C (Q.coeff n) * Polynomial.X ^ n ∈ Polynomial.degreeLT ℂ (n + 1) :=
      Polynomial.mem_degreeLT.2 ((Polynomial.degree_C_mul_X_pow_le _ _).trans_lt
        (by exact_mod_cast Nat.lt_succ_self n))
    refine ⟨Polynomial.C (Q.coeff n) * Polynomial.X ^ n + a,
      Submodule.add_mem _ hXn (Polynomial.degreeLT_mono (Nat.le_succ n) ha), fun x => ?_⟩
    have hx : Q.eval (x : ℂ) = Q.coeff n * P.eval (x : ℂ) +
        (Q - Polynomial.C (Q.coeff n) * P).eval (x : ℂ) := by
      simp only [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C]
      ring
    rw [hx, ← hP x, hQa x, ← tsum_mul_left, ← Summable.tsum_add
      ((summable_mul_scalingFun_sub m hN (fun k : ℤ => (k : ℂ) ^ n) x).mul_left _)
      (summable_mul_scalingFun_sub m hN (fun k : ℤ => a.eval (k : ℂ)) x)]
    refine tsum_congr fun k => ?_
    simp only [Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
      Polynomial.eval_X]
    ring

/-- **Every polynomial of degree `< N` is a combination of the integer translates of `φ` with
polynomial coefficients**: for `N ≥ 2` and every polynomial `Q` of degree `< N` there is a
polynomial `a` with `Q(x) = ∑_{k ∈ ℤ} a(k) φ(x - k)` for every `x ∈ ℝ`
(`Daubechies.exists_coeff_poly_of_mem_degreeLT` with `n = N`, which also gives `a` of
degree `< N`). For each `x` the sum has only finitely many nonzero terms. -/
theorem exists_coeff_poly (hN : 2 ≤ N) {Q : ℂ[X]} (hQ : Q ∈ Polynomial.degreeLT ℂ N) :
    ∃ a : ℂ[X], ∀ x : ℝ, Q.eval (x : ℂ) = ∑' k : ℤ, a.eval (k : ℂ) * scalingFun m (x - k) :=
  let ⟨a, _, ha⟩ := exists_coeff_poly_of_mem_degreeLT m hN le_rfl hQ
  ⟨a, ha⟩

/-! ### Coefficient recovery -/

/-- **Two translates of `φ` overlap only for nearby indices**: for `N ≥ 2`, `y ∈ ℝ` and integers
`j, k` with `j ∉ [k - (2N - 1), k + (2N - 1)]`, `φ(y - j) conj φ(y - k) = 0`. This is the
level `0` case of `Daubechies.scaledFun_mul_conj_eq_zero` (`Daubechies.scaledFun_zero`), since
`φ` vanishes outside `[0, 2N - 1]` (`Daubechies.scalingFun_eq_zero`), so
`⌈b - a⌉ = ⌈(2N - 1) - 0⌉ = 2N - 1`. -/
theorem scalingFun_sub_mul_conj_eq_zero (hN : 2 ≤ N) {j k : ℤ}
    (hjk : j ∉ Finset.Icc (k - (2 * N - 1)) (k + (2 * N - 1))) (y : ℝ) :
    scalingFun m (y - j) * conj (scalingFun m (y - k)) = 0 := by
  have hc : ((⌈(2 * N - 1 : ℝ) - 0⌉₊ : ℕ) : ℤ) = 2 * N - 1 := by
    have h : (2 * N - 1 : ℝ) - 0 = ((2 * N - 1 : ℕ) : ℝ) := by
      rw [sub_zero, Nat.cast_sub (by omega), Nat.cast_mul, Nat.cast_ofNat, Nat.cast_one]
    rw [h, Nat.ceil_natCast]
    omega
  simpa only [scaledFun_zero] using scaledFun_mul_conj_eq_zero (j := 0) (k := k) (l := j)
    (fun _ hx => scalingFun_eq_zero m hN hx) (by rwa [hc]) y

/-- For `N ≥ 2` and integers `j, k`, the function `y ↦ φ(y - j) conj φ(y - k)` is integrable:
the level `0` case of `Daubechies.integrable_scaledFun_mul_conj` (`Daubechies.scaledFun_zero`),
since `φ` is continuous and vanishes outside `[0, 2N - 1]`. -/
theorem integrable_scalingFun_sub_mul_conj (hN : 2 ≤ N) (j k : ℤ) :
    Integrable fun y : ℝ => scalingFun m (y - j) * conj (scalingFun m (y - k)) := by
  simpa only [scaledFun_zero] using integrable_scaledFun_mul_conj (continuous_scalingFun m hN)
    (fun _ hx => scalingFun_eq_zero m hN hx) 0 k j

/-- **Coefficient recovery**: for `N ≥ 2`, every sequence `a : ℤ → ℂ` and every `k ∈ ℤ`,
`∫ (∑_{j ∈ ℤ} a(j) φ(y - j)) conj φ(y - k) dy = a(k)`. This is coefficient recovery for the
scaling function at level `0` (`Daubechies.coeffFun_expand_scalingFun`,
`Daubechies.scaledFun_zero`). The sequence `a` is arbitrary: at each point the sum over `j` is
finite. -/
theorem integral_tsum_mul_scalingFun_sub_mul_conj (hN : 2 ≤ N) (a : ℤ → ℂ) (k : ℤ) :
    ∫ y, (∑' j : ℤ, a j * scalingFun m (y - j)) * conj (scalingFun m (y - k)) = a k := by
  simpa only [coeffFun, expand, scaledFun_zero] using coeffFun_expand_scalingFun m hN 0 a k

/-! ### The projection identity -/

/-- **The projection identity: the translates of `φ` reproduce polynomials**: for `N ≥ 2`, every
polynomial `Q` of degree `< N` and every `x ∈ ℝ`,
`∑_{k ∈ ℤ} ⟨Q, φ(· - k)⟩ φ(x - k) = Q(x)`, where `⟨Q, φ(· - k)⟩ = ∫ Q(y) conj φ(y - k) dy`.
So the projection `f ↦ ∑_k ⟨f, φ(· - k)⟩ φ(· - k)` leaves every polynomial of degree `< N`
unchanged. Write `Q = ∑_j a(j) φ(· - j)` with a polynomial `a` (`Daubechies.exists_coeff_poly`);
then `⟨Q, φ(· - k)⟩ = a(k)` (`Daubechies.integral_tsum_mul_scalingFun_sub_mul_conj`), and the left
side is `∑_k a(k) φ(x - k) = Q(x)`. -/
theorem sum_inner_poly_mul_scalingFun (hN : 2 ≤ N) {Q : ℂ[X]}
    (hQ : Q ∈ Polynomial.degreeLT ℂ N) (x : ℝ) :
    ∑' k : ℤ, (∫ y : ℝ, Q.eval (y : ℂ) * conj (scalingFun m (y - k))) * scalingFun m (x - k) =
      Q.eval (x : ℂ) := by
  obtain ⟨a, ha⟩ := exists_coeff_poly m hN hQ
  have h : ∀ k : ℤ, ∫ y : ℝ, Q.eval (y : ℂ) * conj (scalingFun m (y - k)) = a.eval (k : ℂ) :=
    fun k => by
      simp_rw [ha]
      exact integral_tsum_mul_scalingFun_sub_mul_conj m hN (fun j => a.eval (j : ℂ)) k
  simp_rw [h]
  exact (ha x).symm

/-- **The projection identity, real form**: for `N ≥ 2`, every polynomial `Q` of degree `< N` and
every `x ∈ ℝ`, `∑_{k ∈ ℤ} (∫ Q(y) φ(y - k) dy) φ(x - k) = Q(x)`. Since `φ` is real
(`Daubechies.conj_scalingFun`), this is `Daubechies.sum_inner_poly_mul_scalingFun`. -/
theorem sum_integral_poly_mul_scalingFun (hN : 2 ≤ N) {Q : ℂ[X]}
    (hQ : Q ∈ Polynomial.degreeLT ℂ N) (x : ℝ) :
    ∑' k : ℤ, (∫ y : ℝ, Q.eval (y : ℂ) * scalingFun m (y - k)) * scalingFun m (x - k) =
      Q.eval (x : ℂ) := by
  simpa only [conj_scalingFun] using sum_inner_poly_mul_scalingFun m hN hQ x

/-! ### The projection identity at the dyadic levels -/

/-- **Dilating a polynomial**: for every polynomial `Q` of degree `< N` and every `j ∈ ℕ` there is
a polynomial `R` of degree `< N` with `R(2^j y) = Q(y)` for every `y ∈ ℝ`, namely
`R(u) = Q(2^(-j) u)` (`Interval.comp_affine_mem_degreeLT`). -/
theorem exists_poly_comp_two_pow_mul {Q : ℂ[X]} (hQ : Q ∈ Polynomial.degreeLT ℂ N) (j : ℕ) :
    ∃ R ∈ Polynomial.degreeLT ℂ N, ∀ y : ℝ, R.eval ((2 ^ j * y : ℝ) : ℂ) = Q.eval (y : ℂ) := by
  refine ⟨Q.comp (Polynomial.C 0 + Polynomial.C ((2 : ℂ) ^ j)⁻¹ * Polynomial.X),
    Interval.comp_affine_mem_degreeLT hQ 0 ((2 : ℂ) ^ j)⁻¹, fun y => ?_⟩
  simp only [Polynomial.eval_comp, Polynomial.eval_add, Polynomial.eval_mul, Polynomial.eval_C,
    Polynomial.eval_X, zero_add]
  push_cast
  rw [inv_mul_cancel_left₀ (pow_ne_zero _ two_ne_zero)]

/-- **The projection identity at the dyadic level `j`**: for `N ≥ 2`, every polynomial `Q` of
degree `< N`, every `j ∈ ℕ` and every `x ∈ ℝ`,
`∑_{k ∈ ℤ} 2^j (∫ Q(y) conj φ(2^j y - k) dy) φ(2^j x - k) = Q(x)`.
For the normalised functions `φ_(j,k)(x) = 2^(j/2) φ(2^j x - k)` this reads
`∑_k ⟨Q, φ_(j,k)⟩ φ_(j,k)(x) = Q(x)`. Apply `Daubechies.sum_inner_poly_mul_scalingFun` to the
polynomial `R` of degree `< N` with `R(2^j y) = Q(y)` (`Daubechies.exists_poly_comp_two_pow_mul`)
at the point `2^j x`, and substitute `u = 2^j y` in the integrals
(`Daubechies.integral_eq_two_pow_mul_integral_comp`). -/
theorem sum_inner_poly_mul_scalingFun_two_pow (hN : 2 ≤ N) {Q : ℂ[X]}
    (hQ : Q ∈ Polynomial.degreeLT ℂ N) (j : ℕ) (x : ℝ) :
    ∑' k : ℤ, ((2 : ℂ) ^ j * ∫ y : ℝ, Q.eval (y : ℂ) * conj (scalingFun m (2 ^ j * y - k))) *
      scalingFun m (2 ^ j * x - k) = Q.eval (x : ℂ) := by
  obtain ⟨R, hR, hRQ⟩ := exists_poly_comp_two_pow_mul hQ j
  have h := sum_inner_poly_mul_scalingFun m hN hR (2 ^ j * x)
  rw [hRQ] at h
  rw [← h]
  refine tsum_congr fun k => ?_
  rw [integral_eq_two_pow_mul_integral_comp
    (fun u : ℝ => R.eval (u : ℂ) * conj (scalingFun m (u - k))) j]
  simp only [hRQ]

end Daubechies
