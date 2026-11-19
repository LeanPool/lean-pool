/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurJacobian.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
The original source is MIT licensed; its notice follows.

MIT License

Copyright (c) 2026 Djalil Chafai

Permission is hereby granted, free of charge, to any person obtaining a copy
of this software and associated documentation files (the "Software"), to deal
in the Software without restriction, including without limitation the rights
to use, copy, modify, merge, publish, distribute, sublicense, and/or sell
copies of the Software, and to permit persons to whom the Software is
furnished to do so, subject to the following conditions:

The above copyright notice and this permission notice shall be included in all
copies or substantial portions of the Software.

THE SOFTWARE IS PROVIDED "AS IS", WITHOUT WARRANTY OF ANY KIND, EXPRESS OR
IMPLIED, INCLUDING BUT NOT LIMITED TO THE WARRANTIES OF MERCHANTABILITY,
FITNESS FOR A PARTICULAR PURPOSE AND NONINFRINGEMENT. IN NO EVENT SHALL THE
AUTHORS OR COPYRIGHT HOLDERS BE LIABLE FOR ANY CLAIM, DAMAGES OR OTHER
LIABILITY, WHETHER IN AN ACTION OF CONTRACT, TORT OR OTHERWISE, ARISING FROM,
OUT OF OR IN CONNECTION WITH THE SOFTWARE OR THE USE OR OTHER DEALINGS IN THE
SOFTWARE.
-/

module

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurDecomposition
public import Mathlib.Order.Prod.Lex.Basic

/-! # The Vandermonde block of the Schur differential

Strict lower entries are ordered by column and decreasing row. With that order,
the lower-entry commutator map for an upper triangular matrix is triangular;
its diagonal entries are differences of the triangular diagonal eigenvalues.
Its complex determinant is their product, and its squared norm is the
Vandermonde weight. The later lemmas identify this matrix with the actual
lower-entry part of the skew-Hermitian tangent commutator. Upper triangular
conjugate-transpose terms contribute zero to those lower entries.
-/

@[expose] public section

open Matrix Order OrderDual
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- Strict lower entries ordered by column, then by decreasing row. This ordering
makes the lower block of the Schur conjugation differential triangular. -/
abbrev SchurLowerIndex (n : ℕ) :=
  {p : (Fin n) ×ₗ (Fin n)ᵒᵈ // (ofLex p).1 < ofDual (ofLex p).2}

/-- The row of a strictly lower position. -/
def schurLowerRow {n : ℕ} (p : SchurLowerIndex n) : Fin n := ofDual (ofLex p.val).2
/-- The column of a strictly lower position. -/
def schurLowerCol {n : ℕ} (p : SchurLowerIndex n) : Fin n := (ofLex p.val).1

/-- The complex linear lower-entry block of the commutator differential `[K,T]`. -/
def schurLowerJacobian {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (SchurLowerIndex n) (SchurLowerIndex n) ℂ := fun p q =>
  (if schurLowerRow p = schurLowerRow q then T (schurLowerCol q) (schurLowerCol p) else 0) -
  (if schurLowerCol p = schurLowerCol q then T (schurLowerRow p) (schurLowerRow q) else 0)

theorem schurLowerJacobian_lowerTriangular {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) : (schurLowerJacobian T).IsLowerTriangular := by
  intro p q hpq
  have h : (ofLex p.val).1 < (ofLex q.val).1 ∨
      (ofLex p.val).1 = (ofLex q.val).1 ∧ (ofLex p.val).2 < (ofLex q.val).2 := by
    have hh : p.val < q.val := hpq
    exact (Prod.Lex.toLex_lt_toLex).mp hh
  rcases h with h | ⟨hc, hr⟩
  · have hne : schurLowerCol p ≠ schurLowerCol q := ne_of_lt h
    have hz := hT (schurLowerCol q) (schurLowerCol p) h
    simp [schurLowerJacobian, hne, hz]
  · have hne : schurLowerRow p ≠ schurLowerRow q := ne_of_gt hr
    have hz := hT (schurLowerRow p) (schurLowerRow q) hr
    simp [schurLowerJacobian, hne, hz]

theorem schurLowerJacobian_det {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) :
    (schurLowerJacobian T).det =
      ∏ p : SchurLowerIndex n, (T (schurLowerCol p) (schurLowerCol p) -
        T (schurLowerRow p) (schurLowerRow p)) := by
  rw [Matrix.det_of_isLowerTriangular _ (schurLowerJacobian_lowerTriangular T hT)]
  simp [schurLowerJacobian]

/-- Strictly lower positions as pairs of a column `j` and a row `i` with `j < i`. -/
def schurLowerSigmaEquiv (n : ℕ) :
    SchurLowerIndex n ≃ (Σ j : Fin n, {i : Fin n // j < i}) where
  toFun p := ⟨schurLowerCol p, ⟨schurLowerRow p, p.property⟩⟩
  invFun q := ⟨toLex (q.1, toDual q.2.val), q.2.property⟩
  left_inv p := by rfl
  right_inv q := by rfl

/-- The squared complex determinant of the lower Schur differential is precisely
the Vandermonde square of the triangular diagonal. -/
theorem schurLowerJacobian_normSq_det {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) :
    Complex.normSq (schurLowerJacobian T).det = vandermondeWeight (fun i => T i i) := by
  classical
  rw [schurLowerJacobian_det T hT]
  simp only [map_prod]
  have he := (schurLowerSigmaEquiv n).prod_comp
    (fun q : Σ j : Fin n, {i : Fin n // j < i} =>
      Complex.normSq (T q.1 q.1 - T q.2.val q.2.val))
  change (∏ p : SchurLowerIndex n, Complex.normSq
    (T (schurLowerCol p) (schurLowerCol p) - T (schurLowerRow p) (schurLowerRow p))) =
      ∏ q : Σ j : Fin n, {i : Fin n // j < i},
        Complex.normSq (T q.1 q.1 - T q.2.val q.2.val) at he
  change (∏ p : SchurLowerIndex n,
    Complex.normSq (T (schurLowerCol p) (schurLowerCol p) - T (schurLowerRow p) (schurLowerRow p)))
        = _
  rw [he, Fintype.prod_sigma]
  unfold vandermondeWeight
  rw [vandermonde_eq_product]
  simp only [map_prod]
  apply Finset.prod_congr rfl
  intro j hj
  rw [← Finset.prod_subtype (Finset.Ioi j) (by simp)
    (fun i => Complex.normSq (T j j - T i i))]
  apply Finset.prod_congr rfl
  intro i hi
  rw [← neg_sub (T i i) (T j j), Complex.normSq_neg]

/-- The strictly lower-triangular matrix whose entry at each strictly lower position `p` is
`x p`. -/
def schurLowerCombination {n : ℕ} (x : SchurLowerIndex n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  ∑ p, x p • Matrix.single (schurLowerRow p) (schurLowerCol p) 1

theorem schurLowerJacobian_entry_commutator {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (p q : SchurLowerIndex n) :
    schurLowerJacobian T p q =
      ((Matrix.single (schurLowerRow q) (schurLowerCol q) 1 * T -
        T * Matrix.single (schurLowerRow q) (schurLowerCol q) 1) : Matrix (Fin n) (Fin n) ℂ)
        (schurLowerRow p) (schurLowerCol p) := by
  classical
  by_cases hr : schurLowerRow p = schurLowerRow q <;>
    by_cases hc : schurLowerCol p = schurLowerCol q <;>
  simp [schurLowerJacobian, Matrix.mul_apply, Matrix.single_apply,
    ite_mul, mul_ite, eq_comm, hr, hc]

/-- The triangular matrix whose determinant was computed above is the actual
lower-entry commutator map on strictly lower perturbations. -/
theorem schurLowerJacobian_mulVec_commutator {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (x : SchurLowerIndex n → ℂ) (p : SchurLowerIndex n) :
    (schurLowerJacobian T *ᵥ x) p =
      (schurLowerCombination x * T - T * schurLowerCombination x)
        (schurLowerRow p) (schurLowerCol p) := by
  classical
  simp only [Matrix.mulVec, dotProduct, schurLowerJacobian_entry_commutator,
    schurLowerCombination, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, ← Finset.sum_sub_distrib]
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem schurLowerCombination_upperEntries_zero {n : ℕ} (x : SchurLowerIndex n → ℂ)
    (i j : Fin n) (hij : i ≤ j) : schurLowerCombination x i j = 0 := by
  classical
  simp only [schurLowerCombination, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_eq_zero
  intro p hp
  have hnot : ¬(i = schurLowerRow p ∧ j = schurLowerCol p) := by
    rintro ⟨rfl, rfl⟩
    exact not_le_of_gt p.property hij
  simp [eq_comm, hnot]

/-- The skew-Hermitian matrix `L - Lᴴ` with `L = schurLowerCombination x`. -/
def schurSkewCombination {n : ℕ} (x : SchurLowerIndex n → ℂ) : Matrix (Fin n) (Fin n) ℂ :=
  schurLowerCombination x - (schurLowerCombination x)ᴴ

theorem schurSkewCombination_conjTranspose {n : ℕ} (x : SchurLowerIndex n → ℂ) :
    (schurSkewCombination x)ᴴ = -schurSkewCombination x := by
  simp [schurSkewCombination]

/-- The Vandermonde block is the actual lower-entry map of the skew-Hermitian
unitary tangent commutator, not a separately postulated Jacobian matrix. -/
theorem schurLowerJacobian_skew_commutator {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0) (x : SchurLowerIndex n → ℂ) (p : SchurLowerIndex n) :
    (schurLowerJacobian T *ᵥ x) p =
      (schurSkewCombination x * T - T * schurSkewCombination x)
        (schurLowerRow p) (schurLowerCol p) := by
  have hu : ((schurLowerCombination x)ᴴ).IsUpperTriangular := by
    intro i j hij
    simp only [Matrix.conjTranspose_apply]
    rw [schurLowerCombination_upperEntries_zero x j i (le_of_lt hij), star_zero]
  have htu : T.IsUpperTriangular := fun {i j} hij => hT i j hij
  have h1 := hu.mul htu
  have h2 := htu.mul hu
  have hz1 : ((schurLowerCombination x)ᴴ * T) (schurLowerRow p) (schurLowerCol p) = 0 := h1
      p.property
  have hz2 : (T * (schurLowerCombination x)ᴴ) (schurLowerRow p) (schurLowerCol p) = 0 := h2
      p.property
  rw [schurLowerJacobian_mulVec_commutator]
  simp only [schurSkewCombination, Matrix.sub_mul, Matrix.mul_sub, Matrix.sub_apply]
  rw [hz1, hz2]
  ring

theorem schurLowerJacobian_det_ne_zero {n : ℕ} (T : Matrix (Fin n) (Fin n) ℂ)
    (hT : ∀ i j, j < i → T i j = 0)
    (hd : Function.Injective (fun i => T i i)) : (schurLowerJacobian T).det ≠ 0 := by
  rw [schurLowerJacobian_det T hT]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  exact sub_ne_zero.mpr (hd.ne (ne_of_lt p.property))

theorem schurLowerIndex_ext {n : ℕ} {p q : SchurLowerIndex n}
    (hr : schurLowerRow p = schurLowerRow q) (hc : schurLowerCol p = schurLowerCol q) : p = q := by
  apply Subtype.ext
  apply ofLex.injective
  apply Prod.ext hc
  exact (ofDual.injective hr)

theorem schurLowerCombination_lowerEntry {n : ℕ} (x : SchurLowerIndex n → ℂ)
    (p : SchurLowerIndex n) :
    schurLowerCombination x (schurLowerRow p) (schurLowerCol p) = x p := by
  classical
  have he (q : SchurLowerIndex n) :
      (schurLowerRow q = schurLowerRow p ∧ schurLowerCol q = schurLowerCol p) ↔ q = p :=
    ⟨fun h => schurLowerIndex_ext h.1 h.2, fun h => by simp [h]⟩
  simp [schurLowerCombination, Matrix.sum_apply, Matrix.single_apply, he]

end
end GinibrePoincare
