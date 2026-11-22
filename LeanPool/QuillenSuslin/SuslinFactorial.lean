/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import LeanPool.QuillenSuslin.SuslinMatrix
public import Mathlib.LinearAlgebra.Matrix.SpecialLinearGroup

/-!
# Suslin's `r!` theorem for factorial-shaped exponents

For a unimodular row `(a₀, …, a_r)` over a commutative ring, `r ≥ 1`, and exponents `m` such that,
after a permutation `σ`, `max (r - i) 1` divides `m (σ i)` for every `i`, the row
`(a₀ ^ m₀, …, a_r ^ m_r)` is the first row of a matrix of determinant one. In particular the row
`(a₀, a₁, a₂ ², …, a_r ʳ)` is completable (Suslin 1977, the core case of Theorem 2), and for
`r ≤ 2` the full divisibility statement `r! ∣ ∏ mᵢ` follows (for `r = 2` this is the theorem of
Swan and Towber).

The proof is by induction on `r`, with the bordering step `exists_border`. Polynomially, for rows
`y` and `z` of length `k + 2`, the row `(y₀ ^ (k + 1), …, y_k, y_{k+1})` with exponents
`max (k + 1 - i) 1` is the first row of a matrix of determinant `(∑ yᵢ zᵢ) ^ (k + 1)!`
(`exists_row_pow_det`): with `p = ∑_{i ≥ 1} yᵢ zᵢ`, `u = y₀ z₀` and `e = (k + 1)!`, write
`(p + u) ^ e = u T + p ^ e`; the bordering step with `X = y₀ ^ (k + 2)`, `τ = z₀ T` and
`δ = p ^ e` gives determinant `(u T + p ^ e) ^ (k + 2) = (p + u) ^ (k + 2)!`.

## Main results

* `exists_row_pow_det`: the polynomial identity above.
* `exists_specialLinearGroup_row_pow_of_perm`: the theorem for permuted factorial-shaped
  exponents.
* `exists_specialLinearGroup_row_pow_max`: the row `(a₀, a₁, a₂ ², …, a_r ʳ)` is completable.
* `exists_specialLinearGroup_row_pow_of_le_two`: Suslin's `r!` theorem for `r ≤ 2`.

## References

* A. A. Suslin, *On stably free modules*, Math. USSR Sb. 31 (1977), 479–491, Theorem 2.
* R. G. Swan, J. Towber, *A class of projective modules which are nearly free*, J. Algebra 36
  (1975), 427–434.
* T. Y. Lam, *Serre's problem on projective modules*, Springer, 2006, Chapter III.
-/

@[expose] public section

open Matrix

namespace LeanPool.QuillenSuslin

variable {R : Type*} [CommRing R]

/-- For rows `y`, `z` of length `k + 2`, the row `i ↦ yᵢ ^ max (k + 1 - i) 1` is the first row of
a matrix of determinant `(∑ yᵢ zᵢ) ^ (k + 1)!`. -/
theorem exists_row_pow_det (k : ℕ) (y z : Fin (k + 2) → R) :
    ∃ M : Matrix (Fin (k + 2)) (Fin (k + 2)) R, M 0 = (fun i => y i ^ max (k + 1 - i) 1) ∧
      M.det = (∑ i, y i * z i) ^ (k + 1).factorial := by
  induction k with
  | zero =>
    refine ⟨!![y 0, y 1; -z 1, z 0], ?_, ?_⟩
    · ext i
      fin_cases i <;> simp
    · simp [det_fin_two, Fin.sum_univ_two]
  | succ k ih =>
    obtain ⟨β, hβ0, hβdet⟩ := ih (fun i => y i.succ) (fun i => z i.succ)
    set p := ∑ i : Fin (k + 2), y i.succ * z i.succ
    set u := y 0 * z 0
    set e := (k + 1).factorial
    obtain ⟨T, hT⟩ : u ∣ (p + u) ^ e - p ^ e := by
      have := (Commute.all (p + u) p).sub_dvd_pow_sub_pow e
      rwa [add_sub_cancel_left] at this
    set τ := z 0 * T
    obtain ⟨M, hM0, hMdet⟩ := exists_border (k + 1) β (y 0 ^ (k + 2)) τ
      (fun j => -(y 0 ^ (k + 1 - j) * ((k + 2).choose (j + 1) : R)))
    refine ⟨M, ?_, ?_⟩
    · rw [hM0, hβ0]
      ext i
      refine Fin.cases ?_ (fun i => ?_) i
      · simp
      · simp only [Fin.cons_succ, Fin.val_succ]
        congr 2
        omega
    · rw [hMdet, hβdet, Fin.sum_univ_succ (f := fun i => y i * z i)]
      have hB : (p + u) ^ e = y 0 * τ + p ^ e := by
        rw [sub_eq_iff_eq_add] at hT
        rw [hT]; simp only [τ, u]; ring
      have hfac : (k + 1 + 1).factorial = (k + 2) * e := Nat.factorial_succ _
      rw [show y 0 * z 0 + p = p + u by simp only [u]; ring, hfac, pow_mul', hB,
        add_comm (y 0 * τ), add_pow, Finset.sum_range_succ', ← Fin.sum_univ_eq_sum_range]
      simp only [pow_zero, one_mul, Nat.sub_zero, Nat.choose_zero_right, Nat.cast_one, mul_one]
      rw [add_comm _ ((y 0 * τ) ^ (k + 2)), sub_eq_add_neg,
        ← mul_neg, ← Finset.sum_neg_distrib, Finset.mul_sum]
      congr 1
      · simp only [τ]; ring
      · refine Finset.sum_congr rfl fun j _ => ?_
        have hj : k + 2 - (j + 1) = k + 1 - j := by omega
        rw [hj, pow_succ]
        ring

/-- If the entries of `a` generate the unit ideal, so do the powers `aᵢ ^ lᵢ`. -/
theorem span_range_pow_eq_top {ι : Type*} [Finite ι] {a : ι → R}
    (ha : Ideal.span (Set.range a) = ⊤) (l : ι → ℕ) :
    Ideal.span (Set.range fun i => a i ^ l i) = ⊤ := by
  have := Fintype.ofFinite ι
  have hN := Ideal.span_pow_eq_top (Set.range a) ha (∑ i, l i)
  rw [eq_top_iff, ← hN, Ideal.span_le]
  rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
  have hle : l i ≤ ∑ j, l j := Finset.single_le_sum (fun j _ => Nat.zero_le (l j))
    (Finset.mem_univ i)
  change a i ^ (∑ j, l j) ∈ _
  rw [← Nat.add_sub_cancel' hle, pow_add]
  exact Ideal.mul_mem_right _ _ (Ideal.subset_span ⟨i, rfl⟩)

/-- **Suslin's `r!` theorem, factorial-shaped exponents.** If `(a₀, …, a_r)` is unimodular,
`r ≥ 1`, and for some permutation `σ` the exponent `m (σ i)` is divisible by `max (r - i) 1`,
then `(a₀ ^ m₀, …, a_r ^ m_r)` is the first row of a matrix of determinant one. -/
theorem exists_specialLinearGroup_row_pow_of_perm {r : ℕ} (hr : r ≠ 0) (a : Fin (r + 1) → R)
    (ha : Ideal.span (Set.range a) = ⊤) (m : Fin (r + 1) → ℕ) (σ : Equiv.Perm (Fin (r + 1)))
    (hσ : ∀ i : Fin (r + 1), max (r - i) 1 ∣ m (σ i)) :
    ∃ α : Matrix.SpecialLinearGroup (Fin (r + 1)) R,
      ∀ i : Fin (r + 1), (α : Matrix (Fin (r + 1)) (Fin (r + 1)) R) 0 i = a i ^ m i := by
  obtain ⟨k, rfl⟩ := Nat.exists_eq_succ_of_ne_zero hr
  set y : Fin (k + 2) → R := fun i => a (σ i) ^ (m (σ i) / max (k + 1 - i) 1)
  have hy : ∀ i, y i ^ max (k + 1 - i) 1 = a (σ i) ^ m (σ i) := fun i => by
    simp only [y, ← pow_mul, Nat.div_mul_cancel (hσ i)]
  have hspan : Ideal.span (Set.range y) = ⊤ := by
    have h1 := span_range_pow_eq_top ha (fun j => m j / max (k + 1 - σ.symm j) 1)
    convert h1 using 2
    ext x
    constructor
    · rintro ⟨i, rfl⟩
      exact ⟨σ i, by simp [y]⟩
    · rintro ⟨j, rfl⟩
      exact ⟨σ.symm j, by simp [y]⟩
  obtain ⟨z, hz⟩ : ∃ z : Fin (k + 2) → R, ∑ i, y i * z i = 1 := by
    have h1 : (1 : R) ∈ Ideal.span (Set.range y) := by rw [hspan]; trivial
    obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun R).mp h1
    exact ⟨c, by rw [← hc]; simp [mul_comm]⟩
  obtain ⟨M, hM0, hMdet⟩ := exists_row_pow_det k y z
  rw [hz, one_pow] at hMdet
  set N := M.submatrix id σ.symm
  have hN0 : ∀ j, N 0 j = a j ^ m j := fun j => by
    simp only [N, submatrix_apply, id, hM0]
    rw [hy, Equiv.apply_symm_apply]
  have hNdet : N.det = (Equiv.Perm.sign σ.symm : R) := by
    rw [det_permute', hMdet, mul_one]
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ.symm) with h | h
  · refine ⟨⟨N, by rw [hNdet, h]; simp⟩, hN0⟩
  · refine ⟨⟨N.updateRow 1 ((-1 : R) • N 1), ?_⟩, fun j => ?_⟩
    · rw [det_updateRow_smul, updateRow_eq_self, hNdet, h]
      simp
    · simp [hN0]

/-- Suslin: for a unimodular row `(a₀, …, a_r)` with `r ≥ 1`, the row `(a₀, a₁, a₂ ², …, a_r ʳ)`
is the first row of a matrix of determinant one. -/
theorem exists_specialLinearGroup_row_pow_max {r : ℕ} (hr : r ≠ 0) (a : Fin (r + 1) → R)
    (ha : Ideal.span (Set.range a) = ⊤) :
    ∃ α : Matrix.SpecialLinearGroup (Fin (r + 1)) R,
      ∀ i : Fin (r + 1), (α : Matrix (Fin (r + 1)) (Fin (r + 1)) R) 0 i = a i ^ max (i : ℕ) 1 :=
  exists_specialLinearGroup_row_pow_of_perm hr a ha _ Fin.revPerm fun i => by
    simp [Fin.val_rev]

/-- **Suslin's `r!` theorem for `r ≤ 2`.** If `(a₀, …, a_r)` is unimodular, `1 ≤ r ≤ 2` and
`r!` divides `∏ mᵢ`, then `(a₀ ^ m₀, …, a_r ^ m_r)` is the first row of a matrix of determinant
one. For `r = 2` this is the theorem of Swan and Towber. -/
theorem exists_specialLinearGroup_row_pow_of_le_two {r : ℕ} (hr : r ≠ 0) (hr2 : r ≤ 2)
    (a : Fin (r + 1) → R) (ha : Ideal.span (Set.range a) = ⊤) (m : Fin (r + 1) → ℕ)
    (hdvd : r.factorial ∣ ∏ i : Fin (r + 1), m i) :
    ∃ α : Matrix.SpecialLinearGroup (Fin (r + 1)) R,
      ∀ i : Fin (r + 1), (α : Matrix (Fin (r + 1)) (Fin (r + 1)) R) 0 i = a i ^ m i := by
  obtain rfl | rfl : r = 1 ∨ r = 2 := by omega
  · exact exists_specialLinearGroup_row_pow_of_perm hr a ha m 1 fun i => by
      fin_cases i <;> simp
  · obtain ⟨j, -, hj⟩ := (Nat.prime_iff.mp Nat.prime_two).exists_mem_finset_dvd hdvd
    refine exists_specialLinearGroup_row_pow_of_perm hr a ha m (Equiv.swap 0 j) fun i => ?_
    fin_cases i
    · simpa using hj
    · simp
    · simp

end LeanPool.QuillenSuslin
