/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.Data.Nat.Choose.Vandermonde
public import Mathlib.Algebra.BigOperators.NatAntidiagonal

/-!
# The determinant of the symmetric Pascal matrix

The symmetric Pascal matrix `((i + j).choose i)` of size `n` factors as `L * Lᵀ`, with
`L = (i.choose j)` lower unitriangular (Vandermonde's identity in matrix form). Hence its
determinant is `1` over every commutative ring.

## Main statements

* `Matrix.choose_mul_transpose_choose`
* `Matrix.det_pascal`
-/

public section

open Finset Matrix

namespace Matrix

variable {R : Type*} [CommRing R]

private theorem isLowerTriangular_choose (n : ℕ) :
    (of fun i j : Fin n ↦ (i : ℕ).choose j).IsLowerTriangular :=
  fun _ _ h ↦ Nat.choose_eq_zero_of_lt h

/-- Vandermonde's identity in matrix form: the symmetric Pascal matrix `((i + j).choose i)` is
the product of the lower unitriangular matrix `(i.choose j)` and its transpose. -/
theorem choose_mul_transpose_choose (n : ℕ) :
    (of fun i j : Fin n ↦ (i : ℕ).choose j) * (of fun i j : Fin n ↦ (i : ℕ).choose j)ᵀ =
      of fun i j : Fin n ↦ (i + j : ℕ).choose i := by
  ext i j
  simp only [mul_apply, of_apply, transpose_apply]
  rw [Fin.sum_univ_eq_sum_range (fun k ↦ (i : ℕ).choose k * (j : ℕ).choose k),
    ← sum_subset (range_mono i.isLt) fun k _ hk ↦ by
      simp [Nat.choose_eq_zero_of_lt (not_lt.mp (mem_range.not.mp hk))],
    Nat.add_choose_eq, ← Nat.sum_antidiagonal_swap, Nat.sum_antidiagonal_eq_sum_range_succ_mk]
  exact sum_congr rfl fun k hk ↦ by simp [Nat.choose_symm (mem_range_succ_iff.mp hk)]

variable (R) in
/-- The symmetric Pascal matrix `((i + j).choose i)` has determinant `1`. -/
theorem det_pascal (n : ℕ) :
    (of fun i j : Fin n ↦ ((i + j : ℕ).choose i : R)).det = 1 := by
  change ((of fun i j : Fin n ↦ (i + j : ℕ).choose i).map (Nat.castRingHom R)).det = 1
  rw [← choose_mul_transpose_choose, Matrix.map_mul, transpose_map, det_mul, det_transpose,
    det_of_isLowerTriangular _ ((isLowerTriangular_choose n).map _)]
  simp

end Matrix
