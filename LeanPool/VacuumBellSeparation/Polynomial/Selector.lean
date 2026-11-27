/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Polynomial.SelectorDefs
public import Mathlib.Algebra.Order.Star.Int
public import Mathlib.Algebra.Ring.IsFormallyReal
public import Mathlib.RingTheory.PowerSeries.Trunc
public import Mathlib.RingTheory.PowerSeries.WellKnown
public import Mathlib.Tactic.Basify
public import Mathlib.Tactic.ENatToNat
public import Mathlib.Tactic.ReduceModChar
public import Mathlib.Tactic.TypeStar
import Mathlib.Tactic.Positivity

/-!
# The polynomial selector of equation (7.4)

`poly_N(z) = (1 - z)^N Σ_{k=0}^{N-1} C(N+k-1, k) z^k` (manuscript, `eq:selectors`). Proved here:

* `selector_natDegree_le`: its degree is at most `2N - 1`; `selector_natDegree`: for `N ≥ 1`
  the degree is exactly `2N - 1`, with leading coefficient `(-1)^N C(2N-2, N-1)`
  (`selector_leadingCoeff`, from `coeff_selector_two_mul_sub_one`); for `N = 0`, `poly_0 = 0`;
* `coeff_selector_of_lt`: `poly_N - 1` has a zero of order `N` at zero (the constant coefficient
  is `1` and the coefficients of `z, …, z^{N-1}` vanish), from the expansion
  `(1 - z)^{-N} = Σ_k C(N+k-1, k) z^k`;
* `one_sub_X_pow_dvd_selector`: `poly_N` has a zero of order `N` at one (`(1 - z)^N` divides it);
* `coeffAbsSum_selector_le`: the sum of the absolute values of its coefficients,
  `coeffAbsSum`, is at most `8^N = 2^N · 4^N`: submultiplicativity (`coeffAbsSum_mul_le`),
  `coeffAbsSum ((1 - z)^N) ≤ 2^N` and the binomial bound `Σ_{k<N} C(N+k-1, k) ≤ 4^N`
  (`sum_choose_le_four_pow`);
* `coeffAbsSum_selector_comp_le`: after any affine substitution `z ↦ αz + β` (`α, β ∈ ℝ`) the
  sum is at most `(8 max(1, |α| + |β|)^2)^N`, i.e. `C^N` with `C` depending only on the shift,
  from the composition bound `coeffAbsSum_comp_le`. This covers the one-variable shifts in the
  proof of `lem:polynomial`: the factors `poly_{2n}(u₁)`, `poly_{2n}(1 - v₁)` in the midpoint
  coordinates `a = u₁ - 1/2`, `b = v₁ - 1/2` are `poly_{2n}(a + 1/2)` and `poly_{2n}(1/2 - b)`.
-/

@[expose] public section

open Polynomial

namespace VacuumBellSeparation

/-- `(1 - z)^N` divides `poly_N`: it has a zero of order `N` at one. -/
theorem one_sub_X_pow_dvd_selector (N : ℕ) : (1 - X) ^ N ∣ selector N :=
  dvd_mul_right _ _

/-- The degree of `poly_N` is at most `2N - 1`. -/
theorem selector_natDegree_le (N : ℕ) : (selector N).natDegree ≤ 2 * N - 1 := by
  rcases Nat.eq_zero_or_pos N with rfl | hN
  · simp [selector]
  have h1 : ((1 - X : ℝ[X]) ^ N).natDegree ≤ N := by
    refine (natDegree_pow_le).trans ?_
    have : (1 - X : ℝ[X]).natDegree ≤ 1 := by
      refine (natDegree_sub_le _ _).trans ?_
      simp
    nlinarith
  have h2 : (∑ k ∈ Finset.range N, C (((N + k - 1).choose k : ℕ) : ℝ) * X ^ k).natDegree
      ≤ N - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ (fun k hk => ?_)
    have hk' : k < N := Finset.mem_range.mp hk
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    omega
  refine (natDegree_mul_le).trans ?_
  omega

/-- The truncated binomial series `Σ_{k<N} C(N+k-1, k) z^k` is the truncation of
`(1 - z)^{-N}`. -/
theorem selector_sum_eq_trunc (d : ℕ) :
    (∑ k ∈ Finset.range (d + 1), C (((d + 1 + k - 1).choose k : ℕ) : ℝ) * X ^ k)
      = PowerSeries.trunc (d + 1) (PowerSeries.mk fun n => ((d + n).choose d : ℝ)) := by
  ext j
  rw [PowerSeries.coeff_trunc, finsetSum_coeff]
  simp only [coeff_C_mul_X_pow, PowerSeries.coeff_mk]
  rw [Finset.sum_ite_eq (Finset.range (d + 1)) j]
  simp only [Finset.mem_range]
  split_ifs with h
  · have e : d + 1 + j - 1 = d + j := by omega
    rw [e, Nat.choose_symm_add]
  · rfl

/-- `poly_N` equals `1` to order `N - 1` at zero. -/
theorem coeff_selector_of_lt {N n : ℕ} (hn : n < N) :
    (selector N).coeff n = if n = 0 then 1 else 0 := by
  obtain ⟨d, rfl⟩ : ∃ d, N = d + 1 := ⟨N - 1, by omega⟩
  have hf : (PowerSeries.mk fun n => ((d + n).choose d : ℝ)) *
      ((1 : PowerSeries ℝ) - PowerSeries.X) ^ (d + 1) = 1 :=
    PowerSeries.mk_add_choose_mul_one_sub_pow_eq_one ℝ d
  have hcoe : (((1 - X : ℝ[X]) ^ (d + 1) : ℝ[X]) : PowerSeries ℝ)
      = ((1 : PowerSeries ℝ) - PowerSeries.X) ^ (d + 1) := by
    rw [Polynomial.coe_pow]
    congr 1
    ext k
    rw [Polynomial.coeff_coe]
    simp only [coeff_sub, coeff_one, coeff_X, map_sub, PowerSeries.coeff_one,
      PowerSeries.coeff_X]
    split_ifs <;> first | rfl | (exfalso; omega)
  have hsel : ((selector (d + 1) : ℝ[X]) : PowerSeries ℝ)
      = ((1 : PowerSeries ℝ) - PowerSeries.X) ^ (d + 1) *
        ((PowerSeries.trunc (d + 1) (PowerSeries.mk fun n => ((d + n).choose d : ℝ)) : ℝ[X]) :
          PowerSeries ℝ) := by
    rw [selector, Polynomial.coe_mul, hcoe, selector_sum_eq_trunc]
  have htr : PowerSeries.trunc (d + 1) ((selector (d + 1) : ℝ[X]) : PowerSeries ℝ) = 1 := by
    rw [hsel, mul_comm, PowerSeries.trunc_trunc_mul, hf, PowerSeries.trunc_one]
  have hc := congrArg (fun p : ℝ[X] => p.coeff n) htr
  simpa [PowerSeries.coeff_trunc, hn, Polynomial.coeff_coe, Polynomial.coeff_one] using hc

/-! ### The degree is exactly `2N - 1` -/

/-- The coefficient of `z^{2N-1}` in `poly_N` is `(-1)^N C(2N-2, N-1)`: the product of the
coefficient `(-1)^N` of `z^N` in `(1 - z)^N` and the top coefficient `C(2N-2, N-1)` of the
truncated series. -/
theorem coeff_selector_two_mul_sub_one {N : ℕ} (hN : 1 ≤ N) :
    (selector N).coeff (2 * N - 1) = (-1) ^ N * ((2 * N - 2).choose (N - 1) : ℝ) := by
  have h1 : (1 - X : ℝ[X]).natDegree ≤ 1 := by
    refine (natDegree_sub_le _ _).trans ?_
    simp
  have hpow : ((1 - X : ℝ[X]) ^ N).natDegree ≤ N * 1 :=
    natDegree_pow_le.trans (Nat.mul_le_mul le_rfl h1)
  have hsum : (∑ k ∈ Finset.range N, C (((N + k - 1).choose k : ℕ) : ℝ) * X ^ k).natDegree
      ≤ N - 1 := by
    refine natDegree_sum_le_of_forall_le _ _ (fun k hk => ?_)
    have hk' : k < N := Finset.mem_range.mp hk
    refine (natDegree_C_mul_X_pow_le _ _).trans ?_
    omega
  have hX : (1 - X : ℝ[X]).coeff 1 = -1 := by
    simp [coeff_one]
  have hS : (∑ k ∈ Finset.range N, C (((N + k - 1).choose k : ℕ) : ℝ) * X ^ k).coeff (N - 1)
      = ((2 * N - 2).choose (N - 1) : ℝ) := by
    rw [finsetSum_coeff]
    simp only [coeff_C_mul_X_pow]
    rw [Finset.sum_ite_eq (Finset.range N) (N - 1),
      ite_eq_left (Finset.mem_range.mpr (by omega : N - 1 < N))]
    have e : N + (N - 1) - 1 = 2 * N - 2 := by omega
    rw [e]
  have e : 2 * N - 1 = N * 1 + (N - 1) := by omega
  rw [e, selector, coeff_mul_add_eq_of_natDegree_le hpow hsum, coeff_pow_of_natDegree_le h1, hX,
    hS]

/-- The degree of `poly_N` is exactly `2N - 1` for `N ≥ 1`. -/
theorem selector_natDegree {N : ℕ} (hN : 1 ≤ N) : (selector N).natDegree = 2 * N - 1 := by
  refine natDegree_eq_of_le_of_coeff_ne_zero (selector_natDegree_le N) ?_
  rw [coeff_selector_two_mul_sub_one hN]
  refine mul_ne_zero (pow_ne_zero _ (by norm_num)) ?_
  exact_mod_cast (Nat.choose_pos (by omega : N - 1 ≤ 2 * N - 2)).ne'

/-- The leading coefficient of `poly_N` is `(-1)^N C(2N-2, N-1)` for `N ≥ 1`. -/
theorem selector_leadingCoeff {N : ℕ} (hN : 1 ≤ N) :
    (selector N).leadingCoeff = (-1) ^ N * ((2 * N - 2).choose (N - 1) : ℝ) := by
  rw [leadingCoeff, selector_natDegree hN, coeff_selector_two_mul_sub_one hN]

/-! ### The sum of absolute coefficients -/

theorem coeffAbsSum_nonneg (p : ℝ[X]) : 0 ≤ coeffAbsSum p :=
  Finset.sum_nonneg fun _ _ => abs_nonneg _

/-- `coeffAbsSum p` may be computed over any range `{0, …, n - 1}` past the degree. -/
theorem coeffAbsSum_eq_sum_range {p : ℝ[X]} {n : ℕ} (hn : p.natDegree < n) :
    coeffAbsSum p = ∑ i ∈ Finset.range n, |p.coeff i| := by
  rw [coeffAbsSum]
  refine Finset.sum_subset ?_ ?_
  · intro i hi
    rw [Finset.mem_range] at hi ⊢
    omega
  · intro i hi hi'
    rw [Finset.mem_range] at hi hi'
    have hlt : p.natDegree < i := by omega
    rw [coeff_eq_zero_of_natDegree_lt hlt, abs_zero]

theorem coeffAbsSum_zero : coeffAbsSum 0 = 0 := by
  simp [coeffAbsSum]

theorem coeffAbsSum_C (a : ℝ) : coeffAbsSum (C a) = |a| := by
  simp [coeffAbsSum]

theorem coeffAbsSum_one : coeffAbsSum 1 = 1 := by
  simp [coeffAbsSum]

/-- The triangle inequality for `coeffAbsSum`. -/
theorem coeffAbsSum_add_le (p q : ℝ[X]) :
    coeffAbsSum (p + q) ≤ coeffAbsSum p + coeffAbsSum q := by
  obtain ⟨n, hp, hq, hpq⟩ : ∃ n, p.natDegree < n ∧ q.natDegree < n ∧ (p + q).natDegree < n :=
    ⟨p.natDegree + q.natDegree + (p + q).natDegree + 1, by omega, by omega, by omega⟩
  rw [coeffAbsSum_eq_sum_range hpq, coeffAbsSum_eq_sum_range hp, coeffAbsSum_eq_sum_range hq,
    ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun i _ => ?_
  rw [coeff_add]
  exact abs_add_le _ _

theorem coeffAbsSum_sum_le {ι : Type*} (s : Finset ι) (f : ι → ℝ[X]) :
    coeffAbsSum (∑ i ∈ s, f i) ≤ ∑ i ∈ s, coeffAbsSum (f i) :=
  Finset.le_sum_of_subadditive coeffAbsSum coeffAbsSum_zero.le coeffAbsSum_add_le s f

/-- Multiplication by a monomial `a z^n` multiplies `coeffAbsSum` by `|a|`. -/
theorem coeffAbsSum_C_mul_X_pow_mul (a : ℝ) (n : ℕ) (q : ℝ[X]) :
    coeffAbsSum (C a * X ^ n * q) = |a| * coeffAbsSum q := by
  have hdeg : (C a * X ^ n * q).natDegree < n + (q.natDegree + 1) := by
    have h1 : (C a * X ^ n * q).natDegree ≤ (C a * X ^ n).natDegree + q.natDegree :=
      natDegree_mul_le
    have h2 : (C a * X ^ n).natDegree ≤ n := natDegree_C_mul_X_pow_le a n
    omega
  have hcoeff : ∀ k, (C a * X ^ n * q).coeff k = if n ≤ k then a * q.coeff (k - n) else 0 := by
    intro k
    rw [mul_assoc, coeff_C_mul, coeff_X_pow_mul', mul_ite, mul_zero]
  have hq : coeffAbsSum q = ∑ i ∈ Finset.range (q.natDegree + 1), |q.coeff i| := rfl
  rw [coeffAbsSum_eq_sum_range hdeg, Finset.sum_range_add, hq, Finset.mul_sum]
  have h0 : ∑ i ∈ Finset.range n, |(C a * X ^ n * q).coeff i| = 0 := by
    refine Finset.sum_eq_zero fun i hi => ?_
    have hi' : ¬ n ≤ i := by
      have := Finset.mem_range.mp hi
      omega
    rw [hcoeff, ite_eq_right hi', abs_zero]
  rw [h0, zero_add]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [hcoeff, ite_eq_left (Nat.le_add_right n j), Nat.add_sub_cancel_left, abs_mul]

/-- Submultiplicativity: `coeffAbsSum (p q) ≤ coeffAbsSum p · coeffAbsSum q`. -/
theorem coeffAbsSum_mul_le (p q : ℝ[X]) :
    coeffAbsSum (p * q) ≤ coeffAbsSum p * coeffAbsSum q := by
  have hp : coeffAbsSum p = ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| := rfl
  calc coeffAbsSum (p * q)
      = coeffAbsSum (∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * X ^ i * q) := by
        rw [← Finset.sum_mul, ← p.as_sum_range_C_mul_X_pow]
    _ ≤ ∑ i ∈ Finset.range (p.natDegree + 1), coeffAbsSum (C (p.coeff i) * X ^ i * q) :=
        coeffAbsSum_sum_le _ _
    _ = coeffAbsSum p * coeffAbsSum q := by
        rw [hp, Finset.sum_mul]
        exact Finset.sum_congr rfl fun i _ => coeffAbsSum_C_mul_X_pow_mul _ _ _

theorem coeffAbsSum_pow_le (p : ℝ[X]) (n : ℕ) : coeffAbsSum (p ^ n) ≤ coeffAbsSum p ^ n := by
  induction n with
  | zero => simp [coeffAbsSum_one]
  | succ n ih =>
    rw [pow_succ, pow_succ]
    exact (coeffAbsSum_mul_le _ _).trans
      (mul_le_mul_of_nonneg_right ih (coeffAbsSum_nonneg p))

theorem coeffAbsSum_one_sub_X : coeffAbsSum (1 - X) = 2 := by
  have hdeg : (1 - X : ℝ[X]).natDegree < 2 := by
    have h : (1 - X : ℝ[X]).natDegree ≤ 1 := by
      refine (natDegree_sub_le _ _).trans ?_
      simp
    omega
  rw [coeffAbsSum_eq_sum_range hdeg]
  norm_num [Finset.sum_range_succ, coeff_sub, coeff_one]

/-- `coeffAbsSum ((1 - z)^N) ≤ 2^N` (in fact equality: the binomial coefficients sum to `2^N`). -/
theorem coeffAbsSum_one_sub_X_pow_le (N : ℕ) : coeffAbsSum ((1 - X) ^ N) ≤ 2 ^ N := by
  have h := coeffAbsSum_pow_le (1 - X) N
  rwa [coeffAbsSum_one_sub_X] at h

/-- The binomial bound `Σ_{k<N} C(N+k-1, k) ≤ Σ_{k ≤ 2N} C(2N, k) = 4^N`. -/
theorem sum_choose_le_four_pow (N : ℕ) :
    ∑ k ∈ Finset.range N, (N + k - 1).choose k ≤ 4 ^ N := by
  calc ∑ k ∈ Finset.range N, (N + k - 1).choose k
      ≤ ∑ k ∈ Finset.range N, (2 * N).choose k := by
        refine Finset.sum_le_sum fun k hk => Nat.choose_le_choose k ?_
        have := Finset.mem_range.mp hk
        omega
    _ ≤ ∑ k ∈ Finset.range (2 * N + 1), (2 * N).choose k :=
        Finset.sum_le_sum_of_subset (Finset.range_subset_range.mpr (by omega))
    _ = 4 ^ N := by
        rw [Nat.sum_range_choose, pow_mul]
        norm_num

/-- The truncated series `Σ_{k<N} C(N+k-1, k) z^k` has `coeffAbsSum ≤ 4^N`. -/
theorem coeffAbsSum_selector_sum_le (N : ℕ) :
    coeffAbsSum (∑ k ∈ Finset.range N, C (((N + k - 1).choose k : ℕ) : ℝ) * X ^ k) ≤ 4 ^ N := by
  refine (coeffAbsSum_sum_le _ _).trans ?_
  have h : ∀ k ∈ Finset.range N, coeffAbsSum (C (((N + k - 1).choose k : ℕ) : ℝ) * X ^ k)
      = (((N + k - 1).choose k : ℕ) : ℝ) := by
    intro k _
    have := coeffAbsSum_C_mul_X_pow_mul (((N + k - 1).choose k : ℕ) : ℝ) k 1
    rwa [mul_one, coeffAbsSum_one, mul_one, Nat.abs_cast] at this
  rw [Finset.sum_congr rfl h]
  exact_mod_cast sum_choose_le_four_pow N

/-- **Coefficient bound for (7.4)**: the sum of the absolute coefficients of `poly_N` is at most
`8^N = 2^N · 4^N`. -/
theorem coeffAbsSum_selector_le (N : ℕ) : coeffAbsSum (selector N) ≤ 8 ^ N := by
  have hsel : selector N = (1 - X) ^ N *
      ∑ k ∈ Finset.range N, C (((N + k - 1).choose k : ℕ) : ℝ) * X ^ k := rfl
  rw [hsel]
  calc coeffAbsSum ((1 - X) ^ N *
        ∑ k ∈ Finset.range N, C (((N + k - 1).choose k : ℕ) : ℝ) * X ^ k)
      ≤ coeffAbsSum ((1 - X) ^ N) *
          coeffAbsSum (∑ k ∈ Finset.range N, C (((N + k - 1).choose k : ℕ) : ℝ) * X ^ k) :=
        coeffAbsSum_mul_le _ _
    _ ≤ 2 ^ N * 4 ^ N :=
        mul_le_mul (coeffAbsSum_one_sub_X_pow_le N) (coeffAbsSum_selector_sum_le N)
          (coeffAbsSum_nonneg _) (by positivity)
    _ = 8 ^ N := by
        rw [← mul_pow]
        norm_num

/-! ### Affine shifts -/

/-- `coeffAbsSum (αz + β) ≤ |α| + |β|`. -/
theorem coeffAbsSum_affine_le (α β : ℝ) : coeffAbsSum (C α * X + C β) ≤ |α| + |β| := by
  have hX : coeffAbsSum (C α * X) = |α| := by
    have := coeffAbsSum_C_mul_X_pow_mul α 1 1
    rwa [pow_one, mul_one, coeffAbsSum_one, mul_one] at this
  calc coeffAbsSum (C α * X + C β) ≤ coeffAbsSum (C α * X) + coeffAbsSum (C β) :=
        coeffAbsSum_add_le _ _
    _ = |α| + |β| := by rw [hX, coeffAbsSum_C]

/-- Composition bound:
`coeffAbsSum (p ∘ q) ≤ coeffAbsSum p · max(1, coeffAbsSum q)^{deg p}`. -/
theorem coeffAbsSum_comp_le (p q : ℝ[X]) :
    coeffAbsSum (p.comp q) ≤ coeffAbsSum p * max 1 (coeffAbsSum q) ^ p.natDegree := by
  have hcomp : p.comp q = ∑ i ∈ Finset.range (p.natDegree + 1), C (p.coeff i) * q ^ i := by
    rw [Polynomial.comp, eval₂_eq_sum_range]
  have hp : coeffAbsSum p = ∑ i ∈ Finset.range (p.natDegree + 1), |p.coeff i| := rfl
  have hM : 1 ≤ max 1 (coeffAbsSum q) := le_max_left _ _
  rw [hp, hcomp, Finset.sum_mul]
  refine (coeffAbsSum_sum_le _ _).trans (Finset.sum_le_sum fun i hi => ?_)
  have hi' : i ≤ p.natDegree := by
    have := Finset.mem_range.mp hi
    omega
  calc coeffAbsSum (C (p.coeff i) * q ^ i)
      ≤ coeffAbsSum (C (p.coeff i)) * coeffAbsSum (q ^ i) := coeffAbsSum_mul_le _ _
    _ ≤ |p.coeff i| * coeffAbsSum q ^ i := by
        rw [coeffAbsSum_C]
        exact mul_le_mul_of_nonneg_left (coeffAbsSum_pow_le _ _) (abs_nonneg _)
    _ ≤ |p.coeff i| * max 1 (coeffAbsSum q) ^ p.natDegree := by
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        exact (pow_le_pow_left₀ (coeffAbsSum_nonneg q) (le_max_right _ _) i).trans
          (pow_le_pow_right₀ hM hi')

/-- **Affine shifts of (7.4)**: for fixed `α, β ∈ ℝ`, the sum of the absolute coefficients of
`poly_N(αz + β)` is at most `C^N` with `C = 8 max(1, |α| + |β|)^2`, uniformly in `N`. -/
theorem coeffAbsSum_selector_comp_le (α β : ℝ) (N : ℕ) :
    coeffAbsSum ((selector N).comp (C α * X + C β)) ≤ (8 * max 1 (|α| + |β|) ^ 2) ^ N := by
  have hK : 1 ≤ max 1 (|α| + |β|) := le_max_left _ _
  have hM : max 1 (coeffAbsSum (C α * X + C β)) ≤ max 1 (|α| + |β|) :=
    max_le_max le_rfl (coeffAbsSum_affine_le α β)
  have hM0 : 0 ≤ max 1 (coeffAbsSum (C α * X + C β)) := le_trans zero_le_one (le_max_left _ _)
  calc coeffAbsSum ((selector N).comp (C α * X + C β))
      ≤ coeffAbsSum (selector N) *
          max 1 (coeffAbsSum (C α * X + C β)) ^ (selector N).natDegree :=
        coeffAbsSum_comp_le _ _
    _ ≤ 8 ^ N * max 1 (|α| + |β|) ^ (2 * N) := by
        refine mul_le_mul (coeffAbsSum_selector_le N) ?_ (pow_nonneg hM0 _) (by positivity)
        exact (pow_le_pow_left₀ hM0 hM _).trans
          (pow_le_pow_right₀ hK ((selector_natDegree_le N).trans (Nat.sub_le _ _)))
    _ = (8 * max 1 (|α| + |β|) ^ 2) ^ N := by
        rw [mul_pow, ← pow_mul]

end VacuumBellSeparation
