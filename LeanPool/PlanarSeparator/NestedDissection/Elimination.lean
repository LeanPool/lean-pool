/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.NestedDissection.Spec
public import Mathlib.LinearAlgebra.Matrix.Determinant.Basic
public import Mathlib.Data.Matrix.Mul
public import Mathlib.Algebra.BigOperators.Fin

/-!
# Gaussian elimination without pivoting

`leading` is defined in `NestedDissection/Spec.lean`.

Gaussian elimination of a square matrix over a field `K` in the fixed order `0, 1, …, n - 1`,
without any row or column exchanges.  One elimination step replaces an `(n + 1) × (n + 1)`
matrix
```
  A = | a  r |
      | c  B |
```
by the *Schur complement* `S = B - c a⁻¹ r` of its `(0, 0)` entry (the *pivot* `a`), and the
algorithm recurses on `S`.  Everything is defined by structural recursion on the size and is
computable over any field with computable operations (for instance `ℚ` or `ZMod p`).

## Main definitions

* `NestedDissection.bordered a r c B`: the `(n + 1) × (n + 1)` matrix with corner `a`, first
  row `r`, first column `c` and trailing block `B`.
* `NestedDissection.schur A`: the Schur complement of the `(0, 0)` entry.
* `NestedDissection.pivots A`: the sequence of pivots met by elimination.
* `NestedDissection.lowerFactor A`, `NestedDissection.upperFactor A`: the factors `L` (unit lower
  triangular, holding the multipliers) and `U` (upper triangular, with the pivots on its
  diagonal).
* `NestedDissection.leading A k hk`: the leading principal `k × k` submatrix.

## Main results

* `NestedDissection.det_eq_mul_det_schur`: `det A = a * det (schur A)` when `a ≠ 0`.
* `NestedDissection.det_leading_eq_prod_pivots`: the `k`-th leading principal minor is the
  product of the first `k` pivots, provided the first `k - 1` pivots are nonzero.
* `NestedDissection.pivots_ne_zero`: if every leading principal minor is nonzero, every pivot is
  nonzero.
* `NestedDissection.det_eq_prod_pivots`: `det A = ∏ k, pivots A k` (all pivots but the last
  nonzero; in particular whenever all proper leading principal minors are nonzero).
* `NestedDissection.lowerFactor_mul_upperFactor`: `L * U = A` under the same hypothesis.
* Triangularity of the factors: `lowerFactor_apply_of_lt`, `lowerFactor_apply_self`,
  `upperFactor_apply_of_lt`, `upperFactor_apply_self`.
* `NestedDissection.det_eq_prod_pivotsIn`: the same for elimination in the order given by a
  permutation `σ` (elimination of `A.submatrix σ σ`).
-/

namespace NestedDissection

open Matrix

@[expose] public section

universe u

variable {K : Type u}

/-! ### Bordered matrices -/

section Bordered

/-- The `(n + 1) × (n + 1)` matrix with `(0, 0)` entry `a`, rest of the first row `r`, rest of
the first column `c` and trailing `n × n` block `B`. -/
def bordered {n : ℕ} (a : K) (r c : Fin n → K) (B : Matrix (Fin n) (Fin n) K) :
    Matrix (Fin (n + 1)) (Fin (n + 1)) K :=
  Matrix.of (Fin.cons (Fin.cons a r) fun i => Fin.cons (c i) (B i))

variable {n : ℕ} (a : K) (r c : Fin n → K) (B : Matrix (Fin n) (Fin n) K)

@[simp] theorem bordered_zero_zero : bordered a r c B 0 0 = a := rfl
@[simp] theorem bordered_zero_succ (j : Fin n) : bordered a r c B 0 j.succ = r j := rfl
@[simp] theorem bordered_succ_zero (i : Fin n) : bordered a r c B i.succ 0 = c i := rfl
@[simp] theorem bordered_succ_succ (i j : Fin n) : bordered a r c B i.succ j.succ = B i j := rfl

/-- Every matrix of size `n + 1` is bordered. -/
theorem eq_bordered (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    A = bordered (A 0 0) (fun j => A 0 j.succ) (fun i => A i.succ 0)
      (A.submatrix Fin.succ Fin.succ) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;> rfl

theorem bordered_mul [Semiring K] (a' : K) (r' c' : Fin n → K) (B' : Matrix (Fin n) (Fin n) K) :
    bordered a r c B * bordered a' r' c' B' =
      bordered (a * a' + ∑ k, r k * c' k) (fun j => a * r' j + ∑ k, r k * B' k j)
        (fun i => c i * a' + ∑ k, B i k * c' k)
        (Matrix.of fun i j => c i * r' j + ∑ k, B i k * B' k j) := by
  ext i j
  refine Fin.cases ?_ (fun i => ?_) i <;> refine Fin.cases ?_ (fun j => ?_) j <;>
    simp [Matrix.mul_apply, Fin.sum_univ_succ]

end Bordered

/-! ### One elimination step -/

section Field

variable [Field K]

/-- The Schur complement of the `(0, 0)` entry: `S i j = A (i+1) (j+1) - A (i+1) 0 * A 0 0⁻¹ *
A 0 (j+1)`.  (If `A 0 0 = 0` this is just the trailing block, since `0⁻¹ = 0`.) -/
def schur {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) : Matrix (Fin n) (Fin n) K :=
  Matrix.of fun i j => A i.succ j.succ - A i.succ 0 * (A 0 0)⁻¹ * A 0 j.succ

@[simp] theorem schur_apply {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (i j : Fin n) :
    schur A i j = A i.succ j.succ - A i.succ 0 * (A 0 0)⁻¹ * A 0 j.succ := rfl

/-- One step of elimination does not change the determinant beyond the pivot factor:
`det A = A 0 0 * det (schur A)` when `A 0 0 ≠ 0`. -/
theorem det_eq_mul_det_schur {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K)
    (h : A 0 0 ≠ 0) : A.det = A 0 0 * (schur A).det := by
  set c : Fin (n + 1) → K := Fin.cons 0 fun i => A i.succ 0 * (A 0 0)⁻¹ with hc
  set B : Matrix (Fin (n + 1)) (Fin (n + 1)) K := Matrix.of fun i j => A i j - c i * A 0 j
    with hB
  have hB0 : ∀ j, B 0 j = A 0 j := by intro j; simp [hB, hc]
  have hdet : A.det = B.det := by
    refine det_eq_of_forall_row_eq_smul_add_const c 0 (by simp [hc]) fun i j => ?_
    rw [hB0]; simp [hB]
  rw [hdet, det_succ_column_zero, Fin.sum_univ_succ]
  have hcol : ∀ i : Fin n, B i.succ 0 = 0 := by
    intro i; simp [hB, hc, h]
  simp only [hcol, mul_zero, zero_mul, Finset.sum_const_zero, add_zero, Fin.val_zero, pow_zero,
    one_mul, Fin.succAbove_zero, hB0]
  congr 2

/-! ### The elimination -/

/-- The pivots of Gaussian elimination without pivoting, in order. -/
def pivots : {n : ℕ} → Matrix (Fin n) (Fin n) K → Fin n → K
  | 0, _ => fun i => i.elim0
  | _ + 1, A => Fin.cons (A 0 0) (pivots (schur A))

@[simp] theorem pivots_zero {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    pivots A 0 = A 0 0 := rfl

@[simp] theorem pivots_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (k : Fin n) :
    pivots A k.succ = pivots (schur A) k := rfl

/-- The unit lower triangular factor: the multipliers of the elimination. -/
def lowerFactor : {n : ℕ} → Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K
  | 0, A => A
  | _ + 1, A => bordered 1 0 (fun i => A i.succ 0 * (A 0 0)⁻¹) (lowerFactor (schur A))

/-- The upper triangular factor: the pivot rows of the successive Schur complements. -/
def upperFactor : {n : ℕ} → Matrix (Fin n) (Fin n) K → Matrix (Fin n) (Fin n) K
  | 0, A => A
  | _ + 1, A => bordered (A 0 0) (fun j => A 0 j.succ) 0 (upperFactor (schur A))

theorem lowerFactor_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    lowerFactor A = bordered 1 0 (fun i => A i.succ 0 * (A 0 0)⁻¹) (lowerFactor (schur A)) :=
  rfl

theorem upperFactor_succ {n : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) :
    upperFactor A = bordered (A 0 0) (fun j => A 0 j.succ) 0 (upperFactor (schur A)) :=
  rfl

theorem lowerFactor_apply_self {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    lowerFactor A i i = 1 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · rw [lowerFactor_succ, bordered_succ_succ, ih]

theorem lowerFactor_apply_of_lt {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {i j : Fin n}
    (h : i < j) : lowerFactor A i j = 0 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [lowerFactor_succ]
    induction i using Fin.cases with
    | zero =>
      induction j using Fin.cases with
      | zero => exact absurd h (lt_irrefl _)
      | succ j => rfl
    | succ i =>
      induction j using Fin.cases with
      | zero => exact absurd h (Fin.not_lt_zero _)
      | succ j => rw [bordered_succ_succ]; exact ih _ (Fin.succ_lt_succ_iff.mp h)

theorem upperFactor_apply_self {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (i : Fin n) :
    upperFactor A i i = pivots A i := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    refine Fin.cases ?_ (fun i => ?_) i
    · rfl
    · rw [upperFactor_succ, bordered_succ_succ, ih, pivots_succ]

theorem upperFactor_apply_of_lt {n : ℕ} (A : Matrix (Fin n) (Fin n) K) {i j : Fin n}
    (h : j < i) : upperFactor A i j = 0 := by
  induction n with
  | zero => exact i.elim0
  | succ n ih =>
    rw [upperFactor_succ]
    induction i using Fin.cases with
    | zero => exact absurd h (Fin.not_lt_zero _)
    | succ i =>
      induction j using Fin.cases with
      | zero => rfl
      | succ j => rw [bordered_succ_succ]; exact ih _ (Fin.succ_lt_succ_iff.mp h)

/-- **LU factorization.**  If all pivots except possibly the last are nonzero, then
`lowerFactor A * upperFactor A = A`. -/
theorem lowerFactor_mul_upperFactor {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ k : Fin n, (k : ℕ) + 1 < n → pivots A k ≠ 0) :
    lowerFactor A * upperFactor A = A := by
  induction n with
  | zero => ext i; exact i.elim0
  | succ n ih =>
    have hS := ih (schur A) fun k hk => by simpa using h k.succ (by simpa using hk)
    rw [lowerFactor_succ, upperFactor_succ, bordered_mul]
    conv_rhs => rw [eq_bordered A]
    congr 1
    · simp
    · funext j; simp
    · funext i
      have h0 : A 0 0 ≠ 0 := by simpa using h 0 (by have := i.pos; simp; omega)
      simp [h0]
    · ext i j
      have := congrFun (congrFun hS i) j
      rw [Matrix.mul_apply] at this
      simp [this]

/-! ### Leading principal minors -/

omit [Field K] in
@[simp] theorem leading_self {n : ℕ} (A : Matrix (Fin n) (Fin n) K) :
    leading A n le_rfl = A := rfl

theorem schur_leading {n k : ℕ} (A : Matrix (Fin (n + 1)) (Fin (n + 1)) K) (hk : k ≤ n) :
    schur (leading A (k + 1) (Nat.succ_le_succ hk)) = leading (schur A) k hk := by
  ext i j; simp [leading]

/-- The `k`-th leading principal minor is the product of the first `k` pivots, provided the
first `k - 1` pivots are nonzero. -/
theorem det_leading_eq_prod_pivots {n : ℕ} (A : Matrix (Fin n) (Fin n) K) (k : ℕ) (hk : k ≤ n)
    (h : ∀ j : Fin n, (j : ℕ) + 1 < k → pivots A j ≠ 0) :
    (leading A k hk).det = ∏ j : Fin k, pivots A (Fin.castLE hk j) := by
  induction n generalizing k with
  | zero =>
    obtain rfl : k = 0 := by omega
    simp
  | succ n ih =>
    rcases k with _ | k
    · simp
    rw [Fin.prod_univ_succ]
    rcases Nat.eq_zero_or_pos k with rfl | hk0
    · simp [leading]
    have h0 : A 0 0 ≠ 0 := by simpa using h 0 (by simp; omega)
    rw [det_eq_mul_det_schur _ (by simpa [leading] using h0),
      schur_leading A (Nat.le_of_succ_le_succ hk),
      ih (schur A) k _ fun j hj => by simpa using h j.succ (by simpa using hj)]
    simp [leading]

/-- **Determinant as the product of the pivots**, assuming all pivots except possibly the last
are nonzero. -/
theorem det_eq_prod_pivots {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ k : Fin n, (k : ℕ) + 1 < n → pivots A k ≠ 0) :
    A.det = ∏ k, pivots A k := by
  simpa using det_leading_eq_prod_pivots A n le_rfl h

/-- If every leading principal minor of positive order is nonzero, every pivot is nonzero. -/
theorem pivots_ne_zero {n : ℕ} (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ (k : ℕ) (hk : k ≤ n), 0 < k → (leading A k hk).det ≠ 0) (j : Fin n) :
    pivots A j ≠ 0 := by
  suffices ∀ m (hm : m < n), pivots A ⟨m, hm⟩ ≠ 0 from this j j.2
  intro m
  induction m using Nat.strong_induction_on with
  | _ m ih =>
    intro hm
    have hle : m + 1 ≤ n := hm
    have hne := h (m + 1) hle (Nat.succ_pos m)
    rw [det_leading_eq_prod_pivots A (m + 1) hle fun i hi => ih i.1 (by omega) i.2,
      Fin.prod_univ_castSucc] at hne
    have hlast : Fin.castLE hle (Fin.last m) = ⟨m, hm⟩ := Fin.ext (by simp)
    intro h0
    exact hne (by rw [hlast, h0, mul_zero])

/-! ### Elimination in a prescribed order -/

/-- The pivots of elimination in the order `σ 0, σ 1, …`: the pivots of `A.submatrix σ σ`. -/
def pivotsIn {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) K) : Fin n → K :=
  pivots (A.submatrix σ σ)

/-- **Determinant from elimination in the order `σ`.** -/
theorem det_eq_prod_pivotsIn {n : ℕ} (σ : Equiv.Perm (Fin n)) (A : Matrix (Fin n) (Fin n) K)
    (h : ∀ k : Fin n, (k : ℕ) + 1 < n → pivotsIn σ A k ≠ 0) :
    A.det = ∏ k, pivotsIn σ A k := by
  rw [← det_submatrix_equiv_self σ A]; exact det_eq_prod_pivots _ h

/-- **LU factorization in the order `σ`**: `L * U = A.submatrix σ σ`. -/
theorem lowerFactor_mul_upperFactor_submatrix {n : ℕ} (σ : Equiv.Perm (Fin n))
    (A : Matrix (Fin n) (Fin n) K) (h : ∀ k : Fin n, (k : ℕ) + 1 < n → pivotsIn σ A k ≠ 0) :
    lowerFactor (A.submatrix σ σ) * upperFactor (A.submatrix σ σ) = A.submatrix σ σ :=
  lowerFactor_mul_upperFactor _ h

end Field

end

end NestedDissection
