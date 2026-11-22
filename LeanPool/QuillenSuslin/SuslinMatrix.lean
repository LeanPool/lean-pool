/-
Copyright (c) 2026 Michel Hua. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Michel Hua
-/
module

public import Mathlib.GroupTheory.Perm.Fin
public import Mathlib.LinearAlgebra.Matrix.Adjugate
public import Mathlib.LinearAlgebra.Matrix.Block
public import Mathlib.LinearAlgebra.Matrix.Charpoly.Basic
public import Mathlib.Algebra.Ring.GeomSum
public import Mathlib.Tactic.LinearCombination

/-!
# Suslin's bordering step

This file contains the matrix identity behind Suslin's `r!` theorem. Given an `n × n` matrix `β`
with first row `b` and determinant `δ`, the row `(X, b)` is the first row of an explicit
`(n + 1) × (n + 1)` matrix whose determinant is `X τ ⁿ` modulo `δ (τ, δ)ⁿ⁻¹`, for any `X` and `τ`.

## Main results

* `det_border`: the determinant of a bordered matrix, `p det Γ - (b adj Γ) · u`.
* `adjugate_scalar_sub_smul_shift_zero`: the first row of the adjugate of `τ - δ S`, for the shift
  matrix `S`.
* `exists_border`: the bordering step.

## References

* A. A. Suslin, *On stably free modules*, Math. USSR Sb. 31 (1977), 479–491, Theorem 2.
* T. Y. Lam, *Serre's problem on projective modules*, Springer, 2006, Chapter III.
-/

@[expose] public section

open Matrix Polynomial

namespace LeanPool.QuillenSuslin

variable {R : Type*} [CommRing R]

/-- The `n × n` shift matrix `S`, with `S i (i + 1) = 1` and all other entries zero. -/
def shiftMatrix (n : ℕ) (α : Type*) [Zero α] [One α] : Matrix (Fin n) (Fin n) α :=
  Matrix.of fun i j => if (j : ℕ) = i + 1 then 1 else 0

/-- The entries of the shift matrix. -/
theorem shiftMatrix_apply {n : ℕ} (i j : Fin n) :
    shiftMatrix n R i j = if (j : ℕ) = i + 1 then 1 else 0 := rfl

/-- The `k`-th power of the shift matrix has its ones on the `k`-th superdiagonal. -/
theorem shiftMatrix_pow_apply {n : ℕ} (k : ℕ) (i j : Fin n) :
    (shiftMatrix n R ^ k) i j = if (j : ℕ) = i + k then 1 else 0 := by
  induction k generalizing j with
  | zero =>
    simp only [pow_zero, add_zero]
    by_cases h : i = j
    · subst h; simp
    · rw [Matrix.one_apply_ne h]
      have : ¬ ((j : ℕ) = i) := fun h' => h (Fin.ext h'.symm)
      simp [this]
  | succ k ih =>
    rw [pow_succ, Matrix.mul_apply]
    simp only [ih, shiftMatrix_apply, ite_mul, one_mul, zero_mul]
    by_cases h : (j : ℕ) = i + (k + 1)
    · rw [Finset.sum_eq_single ⟨i + k, by omega⟩]
      · have h' : (↑i + (k + 1) : ℕ) = ↑i + k + 1 := by omega
        simp [h, h']
      · intro l _ hl
        have : ¬ ((l : ℕ) = i + k) := fun hl' => hl (Fin.ext hl')
        simp [this]
      · simp
    · rw [ite_eq_right h]
      refine Finset.sum_eq_zero fun l _ => ?_
      split_ifs with h1 h2 <;> first | rfl | omega

/-- The `n × n` shift matrix is nilpotent of index at most `n`. -/
theorem shiftMatrix_pow_self (n : ℕ) : shiftMatrix n R ^ n = 0 := by
  ext i j
  rw [shiftMatrix_pow_apply, ite_eq_right (by omega)]
  rfl

/-- The matrix `τ - δ S` is upper triangular. -/
theorem isUpperTriangular_scalar_sub_smul_shift (n : ℕ) (τ δ : R) :
    (scalar (Fin n) τ - δ • shiftMatrix n R).IsUpperTriangular := by
  intro i j hij
  have h1 : i ≠ j := ne_of_gt hij
  have h2 : ¬ ((j : ℕ) = i + 1) := by have : (j : ℕ) < i := hij; omega
  simp [shiftMatrix, h1, h2]

/-- The determinant of `τ - δ S` is `τ ^ n`. -/
theorem det_scalar_sub_smul_shift (n : ℕ) (τ δ : R) :
    (scalar (Fin n) τ - δ • shiftMatrix n R).det = τ ^ n := by
  rw [det_of_isUpperTriangular (isUpperTriangular_scalar_sub_smul_shift n τ δ)]
  simp [shiftMatrix]

/-- If `A B = det A • 1` and `det A` is left regular, then `B` is the adjugate of `A`. -/
theorem adjugate_eq_of_mul_eq {n : Type*} [Fintype n] [DecidableEq n] {A B : Matrix n n R}
    (h : A * B = A.det • 1) (hreg : IsLeftRegular A.det) : adjugate A = B := by
  have h1 : adjugate A * (A * B) = A.det • B := by
    rw [← Matrix.mul_assoc, adjugate_mul, smul_mul, Matrix.one_mul]
  rw [h, Matrix.mul_smul, Matrix.mul_one] at h1
  ext i j
  have := congrArg (fun M : Matrix n n R => M i j) h1
  simp only [Matrix.smul_apply, smul_eq_mul] at this
  exact hreg this

/-- The adjugate of `τ - δ S` is `∑_{i < n} τ ^ i (δ S) ^ (n - 1 - i)`. The identity is first
proved over `R[X]` with `τ = X`, where the determinant `X ^ n` is a non-zero-divisor, and then
specialised. -/
theorem adjugate_scalar_sub_smul_shift (n : ℕ) (τ δ : R) :
    adjugate (scalar (Fin n) τ - δ • shiftMatrix n R) =
      ∑ i ∈ Finset.range n, scalar (Fin n) τ ^ i * (δ • shiftMatrix n R) ^ (n - 1 - i) := by
  set x : Matrix (Fin n) (Fin n) R[X] := scalar (Fin n) X
  set y : Matrix (Fin n) (Fin n) R[X] := C δ • shiftMatrix n R[X]
  have hc : Commute x y := scalar_commute _ (fun _ => Commute.all _ _) _
  have hdet : (x - y).det = X ^ n := det_scalar_sub_smul_shift n X (C δ)
  have hy : y ^ n = 0 := by rw [smul_pow, shiftMatrix_pow_self, smul_zero]
  have key : adjugate (x - y) = ∑ i ∈ Finset.range n, x ^ i * y ^ (n - 1 - i) := by
    refine adjugate_eq_of_mul_eq ?_ ?_
    · rw [hc.mul_geom_sum₂, hy, sub_zero, hdet]
      simp [x, smul_one_eq_diagonal, diagonal_pow]
    · rw [hdet]
      exact ((monic_X_pow n).isRegular).left
  have hmap := congrArg (evalRingHom τ).mapMatrix key
  rw [RingHom.map_adjugate, map_sum] at hmap
  have hx : (evalRingHom τ).mapMatrix x = scalar (Fin n) τ := by
    ext i j
    by_cases h : i = j <;> simp [x, h]
  have hS : (evalRingHom τ).mapMatrix (shiftMatrix n R[X]) = shiftMatrix n R := by
    ext i j
    by_cases h : (j : ℕ) = i + 1 <;> simp [shiftMatrix_apply, h]
  have hy' : (evalRingHom τ).mapMatrix y = δ • shiftMatrix n R := by
    simp only [y, ← hS]
    ext i j
    simp
  simp only [map_sub, map_mul, map_pow, hx, hy'] at hmap
  exact hmap

/-- The first row of the adjugate of `τ - δ S` is `(τ ^ n, τ ^ (n - 1) δ, …, δ ^ n)`. -/
theorem adjugate_scalar_sub_smul_shift_zero (n : ℕ) (τ δ : R) (j : Fin (n + 1)) :
    adjugate (scalar (Fin (n + 1)) τ - δ • shiftMatrix (n + 1) R) 0 j =
      τ ^ (n - j) * δ ^ (j : ℕ) := by
  have hterm : ∀ i m : ℕ, (scalar (Fin (n + 1)) τ ^ i * (δ • shiftMatrix (n + 1) R) ^ m) =
      (τ ^ i * δ ^ m) • shiftMatrix (n + 1) R ^ m := by
    intro i m
    rw [← map_pow, scalar_apply, ← smul_eq_diagonal_mul, smul_pow, smul_smul]
  rw [adjugate_scalar_sub_smul_shift, Matrix.sum_apply]
  simp only [hterm, Matrix.smul_apply, shiftMatrix_pow_apply, Fin.val_zero, zero_add,
    smul_eq_mul, mul_ite, mul_one, mul_zero]
  rw [Finset.sum_eq_single (n - j)]
  · have h1 : (j : ℕ) = n + 1 - 1 - (n - j) := by omega
    rw [ite_eq_left h1, ← h1]
  · intro i hi hne
    rw [ite_eq_right]
    simp only [Finset.mem_range] at hi
    omega
  · intro h
    simp only [Finset.mem_range] at h
    omega
/-- Expansion of a bordered determinant: the matrix with first row `(p, b)` and lower block
`(u | Γ)` has determinant `p det Γ - (b adj Γ) · u`. -/
theorem det_border {n : ℕ} (p : R) (b u : Fin (n + 1) → R)
    (Γ : Matrix (Fin (n + 1)) (Fin (n + 1)) R) :
    (Matrix.of (Fin.cons (Fin.cons p b) (fun i => Fin.cons (u i) (Γ i)) :
      Fin (n + 2) → Fin (n + 2) → R)).det = p * Γ.det - (b ᵥ* adjugate Γ) ⬝ᵥ u := by
  rw [det_succ_column_zero, Fin.sum_univ_succ]
  have hrow : ∀ k : Fin (n + 1), (Γ.updateRow k b).det = (b ᵥ* adjugate Γ) k := by
    intro k
    rw [← cramer_transpose_apply, cramer_eq_adjugate_mulVec, ← adjugate_transpose,
      mulVec_transpose]
  have hsub : ∀ k : Fin (n + 1),
      ((Matrix.of (Fin.cons (Fin.cons p b) (fun i => Fin.cons (u i) (Γ i)) :
        Fin (n + 2) → Fin (n + 2) → R)).submatrix k.succ.succAbove Fin.succ) =
      (Γ.updateRow k b).submatrix (Fin.cycleRange k).symm id := by
    intro k
    ext i j
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [Fin.cycleRange_symm_zero]
    · simp only [submatrix_apply, Fin.succ_succAbove_succ, of_apply, Fin.cons_succ,
        Fin.cycleRange_symm_succ, id]
      rw [updateRow_ne (Fin.succAbove_ne k i)]
  simp only [of_apply, Fin.cons_zero, Fin.val_zero, pow_zero, one_mul, Fin.cons_succ,
    Fin.val_succ]
  simp_rw [hsub, det_permute, hrow]
  have h0 : (Matrix.of (Fin.cons (Fin.cons p b) (fun i => Fin.cons (u i) (Γ i)) :
      Fin (n + 2) → Fin (n + 2) → R)).submatrix (Fin.succAbove 0) Fin.succ = Γ := by
    ext i j
    simp
  rw [h0, sub_eq_add_neg, dotProduct, ← Finset.sum_neg_distrib]
  congr 1
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [Equiv.Perm.sign_symm, Fin.sign_cycleRange]
  push_cast
  have hk : ((-1 : R) ^ (k : ℕ)) * (-1) ^ (k : ℕ) = 1 := by
    rw [← mul_pow, neg_one_mul, neg_neg, one_pow]
  linear_combination (-(u k * (b ᵥ* adjugate Γ) k)) * hk

/-- For an `n × n` matrix `β` with adjugate `C`, the matrix `τ - C S β` has determinant
`τ ^ n`, because `C S β` and `S β C = (det β) S` have the same characteristic polynomial. -/
theorem det_scalar_sub_adjugate_mul (n : ℕ) (β : Matrix (Fin n) (Fin n) R) (τ : R) :
    (scalar (Fin n) τ - adjugate β * (shiftMatrix n R * β)).det = τ ^ n := by
  rw [← eval_charpoly, charpoly_mul_comm, eval_charpoly, Matrix.mul_assoc, mul_adjugate,
    Matrix.mul_smul, Matrix.mul_one, det_scalar_sub_smul_shift]

/-- **Suslin's bordering step.** Let `β` be an `(n + 1) × (n + 1)` matrix with first row `b` and
determinant `δ`. For all `X`, `τ` and `v`, the row `(X, b)` is the first row of a matrix of
determinant `X τ ^ (n + 1) - δ ∑ⱼ τ ^ (n - j) δ ^ j vⱼ`.

The matrix is the bordered matrix with lower block `(C v | τ - C S β)`, where `C` is the adjugate of
`β` and `S` the shift matrix; its determinant is computed from `β (τ - C S β) = (τ - δ S) β`. -/
theorem exists_border (n : ℕ) (β : Matrix (Fin (n + 1)) (Fin (n + 1)) R) (X τ : R)
    (v : Fin (n + 1) → R) :
    ∃ M : Matrix (Fin (n + 2)) (Fin (n + 2)) R, M 0 = Fin.cons X (β 0) ∧
      M.det = X * τ ^ (n + 1) - β.det * ∑ j : Fin (n + 1), τ ^ (n - j) * β.det ^ (j : ℕ) * v j := by
  set C := adjugate β
  set δ := β.det
  set Sh := shiftMatrix (n + 1) R
  set Γ := scalar (Fin (n + 1)) τ - C * (Sh * β)
  set Λ := scalar (Fin (n + 1)) τ - δ • Sh
  refine ⟨Matrix.of (Fin.cons (Fin.cons X (β 0)) (fun i => Fin.cons ((C *ᵥ v) i) (Γ i))),
    rfl, ?_⟩
  rw [det_border, det_scalar_sub_adjugate_mul]
  have hβΓ : β * Γ = Λ * β := by
    simp only [Γ, Λ, Matrix.mul_sub, Matrix.sub_mul, ← Matrix.mul_assoc, mul_adjugate,
      scalar_apply, ← smul_eq_diagonal_mul, ← smul_eq_mul_diagonal, smul_mul, Matrix.one_mul, C, δ]
  have hadj : adjugate Γ * C = C * adjugate Λ := by
    rw [← adjugate_mul_distrib, hβΓ, adjugate_mul_distrib]
  have hrow : β 0 ᵥ* C = δ • Pi.single 0 1 := by
    ext j
    have := congrArg (fun M : Matrix _ _ R => M 0 j) (mul_adjugate β)
    simp only [Matrix.mul_apply, Matrix.smul_apply] at this
    simp only [vecMul, dotProduct, Pi.smul_apply, this, smul_eq_mul, C, δ]
    rcases eq_or_ne j 0 with rfl | h
    · simp
    · simp [h, Matrix.one_apply_ne (Ne.symm h)]
  rw [dotProduct_mulVec, vecMul_vecMul, hadj, ← vecMul_vecMul, hrow, smul_vecMul,
    single_one_vecMul, smul_dotProduct, smul_eq_mul]
  congr 2
  simp only [dotProduct, Λ, Sh, Matrix.row_apply, adjugate_scalar_sub_smul_shift_zero]

end LeanPool.QuillenSuslin
