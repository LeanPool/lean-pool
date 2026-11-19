/-
Copyright (c) 2026 Djalil Chafaï. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Djalil Chafaï
-/

/-
Adapted for Lean Pool from djalilchafai/ginibre-
poincare/GinibrePoincare/Analysis/MatrixSchurUniqueness.lean.
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

public import LeanPool.GinibrePoincare.Analysis.MatrixSchurFullJacobian

/-! # Uniqueness of ordered Schur representations modulo phases

For two upper triangular matrices with the same distinct diagonal, the lower
entries of an intertwiner solve a homogeneous Sylvester system. Ordering those
entries by column and decreasing row makes its matrix triangular, with nonzero
eigenvalue differences on the diagonal. Invertibility forces every lower entry
to vanish. A unitary upper triangular matrix must be diagonal: its inverse is
both upper triangular and its conjugate transpose. Applying this to the change
of Schur basis proves that ordered representations differ only by diagonal phases.
-/

@[expose] public section

open Matrix Order OrderDual
open scoped BigOperators
namespace GinibrePoincare
noncomputable section

/-- The matrix, indexed by strictly lower positions, of the coefficients of the Sylvester map
`X ↦ X * A - B * X` restricted to strictly lower entries. -/
def schurLowerSylvester {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ) :
    Matrix (SchurLowerIndex n) (SchurLowerIndex n) ℂ := fun p q =>
  (if schurLowerRow p = schurLowerRow q then A (schurLowerCol q) (schurLowerCol p) else 0) -
  (if schurLowerCol p = schurLowerCol q then B (schurLowerRow p) (schurLowerRow q) else 0)

theorem schurLowerSylvester_lowerTriangular {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) : (schurLowerSylvester A B).IsLowerTriangular := by
  intro p q hpq
  have h : (ofLex p.val).1 < (ofLex q.val).1 ∨
      (ofLex p.val).1 = (ofLex q.val).1 ∧ (ofLex p.val).2 < (ofLex q.val).2 := by
    have hh : p.val < q.val := hpq
    exact (Prod.Lex.toLex_lt_toLex).mp hh
  rcases h with h | ⟨hc, hr⟩
  · have hne : schurLowerCol p ≠ schurLowerCol q := ne_of_lt h
    have hz := hA (schurLowerCol q) (schurLowerCol p) h
    simp [schurLowerSylvester, hne, hz]
  · have hne : schurLowerRow p ≠ schurLowerRow q := ne_of_gt hr
    have hz := hB (schurLowerRow p) (schurLowerRow q) hr
    simp [schurLowerSylvester, hne, hz]

theorem schurLowerSylvester_det {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, j < i → A i j = 0)
    (hB : ∀ i j, j < i → B i j = 0) :
    (schurLowerSylvester A B).det =
      ∏ p : SchurLowerIndex n, (A (schurLowerCol p) (schurLowerCol p) -
        B (schurLowerRow p) (schurLowerRow p)) := by
  rw [Matrix.det_of_isLowerTriangular _ (schurLowerSylvester_lowerTriangular A B hA hB)]
  simp [schurLowerSylvester]

theorem schurLowerSylvester_entry {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (p q : SchurLowerIndex n) : schurLowerSylvester A B p q =
      ((Matrix.single (schurLowerRow q) (schurLowerCol q) 1 * A -
        B * Matrix.single (schurLowerRow q) (schurLowerCol q) 1) : Matrix (Fin n) (Fin n) ℂ)
        (schurLowerRow p) (schurLowerCol p) := by
  classical
  by_cases hr : schurLowerRow p = schurLowerRow q <;>
    by_cases hc : schurLowerCol p = schurLowerCol q <;>
  simp [schurLowerSylvester, Matrix.mul_apply, Matrix.single_apply,
    ite_mul, mul_ite, eq_comm, hr, hc]

theorem schurLowerSylvester_mulVec {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (x : SchurLowerIndex n → ℂ) (p : SchurLowerIndex n) :
    (schurLowerSylvester A B *ᵥ x) p =
      (schurLowerCombination x * A - B * schurLowerCombination x)
        (schurLowerRow p) (schurLowerCol p) := by
  classical
  simp only [Matrix.mulVec, dotProduct, schurLowerSylvester_entry,
    schurLowerCombination, Matrix.sum_mul, Matrix.mul_sum, Matrix.smul_mul,
    Matrix.mul_smul, ← Finset.sum_sub_distrib]
  simp only [Matrix.sub_apply, Matrix.sum_apply, Matrix.smul_apply, smul_eq_mul]
  apply Finset.sum_congr rfl
  intro q hq
  ring

theorem schurLowerSylvester_det_ne_zero {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0)
    (hd : ∀ i, A i i = B i i) (hinj : Function.Injective (fun i => A i i)) :
    (schurLowerSylvester A B).det ≠ 0 := by
  rw [schurLowerSylvester_det A B hA hB]
  apply Finset.prod_ne_zero_iff.mpr
  intro p hp
  rw [← hd]
  apply sub_ne_zero.mpr
  intro he
  exact (ne_of_lt p.property) (hinj he)

theorem matrix_upper_product {n : ℕ} (A B : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0) :
    ∀ i j, j < i → (A * B) i j = 0 := by
  classical
  intro i j hij
  rw [Matrix.mul_apply]
  apply Finset.sum_eq_zero
  intro k hk
  by_cases hki : k < i
  · rw [hA i k hki, zero_mul]
  · rw [hB k j (lt_of_lt_of_le hij (le_of_not_gt hki)), mul_zero]

/-- An intertwiner between upper triangular matrices with the same distinct ordered diagonal
is upper triangular. This is the uniqueness of the ordered invariant flag. -/
theorem schur_intertwiner_upper {n : ℕ} (A B Q : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0)
    (hd : ∀ i, A i i = B i i) (hinj : Function.Injective (fun i => A i i))
    (hQ : Q * A = B * Q) : ∀ i j, j < i → Q i j = 0 := by
  classical
  let x := (schurEntryCoordinates Q).1
  let y := (schurEntryCoordinates Q).2
  have hsplit : schurLowerCombination x + schurUpperCombination y = Q := by
    simpa [schurEntryCoordinatesInverse_apply, x, y] using schurEntryCoordinates_left_inv n Q
  have hu := schurUpperCombination_lower_zero y
  have hUA := matrix_upper_product (schurUpperCombination y) A hu hA
  have hBU := matrix_upper_product B (schurUpperCombination y) hB hu
  have hz : schurLowerSylvester A B *ᵥ x = 0 := by
    funext p
    rw [schurLowerSylvester_mulVec]
    have he : (schurLowerCombination x * A - B * schurLowerCombination x) +
        (schurUpperCombination y * A - B * schurUpperCombination y) = 0 := by
      calc
        _ = (schurLowerCombination x + schurUpperCombination y) * A -
            B * (schurLowerCombination x + schurUpperCombination y) := by noncomm_ring
        _ = 0 := by rw [hsplit, hQ, sub_self]
    have hp := congrArg (fun M : Matrix (Fin n) (Fin n) ℂ => M (schurLowerRow p) (schurLowerCol p))
        he
    have h1 : (schurUpperCombination y * A) (schurLowerRow p) (schurLowerCol p) = 0 :=
      hUA _ _ p.property
    have h2 : (B * schurUpperCombination y) (schurLowerRow p) (schurLowerCol p) = 0 :=
      hBU _ _ p.property
    simpa only [Matrix.add_apply, Matrix.sub_apply, Matrix.zero_apply, h1, h2,
      sub_self, add_zero, Pi.zero_apply] using hp
  have hinvert := (Matrix.isUnit_iff_isUnit_det (schurLowerSylvester A B)).mpr
    (isUnit_iff_ne_zero.mpr (schurLowerSylvester_det_ne_zero A B hA hB hd hinj))
  have hxin : Function.Injective (Matrix.mulVec (schurLowerSylvester A B)) :=
    Matrix.mulVec_injective_iff_isUnit.mpr hinvert
  have hx : x = 0 := hxin (by simpa using hz)
  intro i j hij
  let p : SchurLowerIndex n := ⟨toLex (j, toDual i), hij⟩
  have hp := congrFun hx p
  simpa [x, p, schurEntryCoordinates, schurLowerRow, schurLowerCol] using hp

theorem matrix_unitary_upper_diagonal {n : ℕ} (Q : Matrix (Fin n) (Fin n) ℂ)
    (hQ : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) (hu : ∀ i j, j < i → Q i j = 0) :
    Q = Matrix.diagonal (fun i => Q i i) := by
  let : Invertible Q := Matrix.invertibleOfIsUnitDet Q
    (Matrix.UnitaryGroup.det_isUnit ⟨Q, hQ⟩)
  have hupper : Q.IsUpperTriangular := fun _ _ h => hu _ _ h
  have hinv := Matrix.blockTriangular_inv_of_blockTriangular hupper
  have he : Q⁻¹ = Qᴴ := Matrix.inv_eq_left_inv (Matrix.mem_unitaryGroup_iff'.mp hQ)
  rw [he] at hinv
  ext i j
  by_cases hij : i = j
  · subst j
    simp
  · rw [Matrix.diagonal_apply_ne _ hij]
    rcases lt_or_gt_of_ne hij with h | h
    · have hz : Qᴴ j i = 0 := hinv h
      simpa using congrArg star hz
    · exact hu i j h

/-- Ordered Schur bases differ by diagonal unitary phases. -/
theorem schur_unitary_intertwiner_diagonal {n : ℕ} (A B Q : Matrix (Fin n) (Fin n) ℂ)
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0)
    (hd : ∀ i, A i i = B i i) (hinj : Function.Injective (fun i => A i i))
    (hQ : Q * A = B * Q) (hunit : Q ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    Q = Matrix.diagonal (fun i => Q i i) :=
  matrix_unitary_upper_diagonal Q hunit (schur_intertwiner_upper A B Q hA hB hd hinj hQ)

/-- Two Schur representations with the same distinct diagonal have the same unitary
basis modulo diagonal phases. -/
theorem schur_ordered_representation_unique_phases {n : ℕ}
    (G A B U V : Matrix (Fin n) (Fin n) ℂ)
    (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) (hV : V ∈ Matrix.unitaryGroup (Fin n) ℂ)
    (hA : ∀ i j, j < i → A i j = 0) (hB : ∀ i j, j < i → B i j = 0)
    (hd : ∀ i, A i i = B i i) (hinj : Function.Injective (fun i => A i i))
    (hga : G = U * A * Uᴴ) (hgb : G = V * B * Vᴴ) :
    Vᴴ * U = Matrix.diagonal (fun i => (Vᴴ * U) i i) := by
  have hu : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.mp hU
  have hv : Vᴴ * V = 1 := Matrix.mem_unitaryGroup_iff'.mp hV
  have hua : U * A = G * U := by
    calc
      _ = U * A * (Uᴴ * U) := by rw [hu, Matrix.mul_one]
      _ = (U * A * Uᴴ) * U := by noncomm_ring
      _ = G * U := by rw [← hga]
  have hvb : Vᴴ * G = B * Vᴴ := by
    rw [hgb]
    calc
      _ = (Vᴴ * V) * B * Vᴴ := by noncomm_ring
      _ = B * Vᴴ := by rw [hv, Matrix.one_mul]
  have hi : (Vᴴ * U) * A = B * (Vᴴ * U) := by
    rw [Matrix.mul_assoc, hua, ← Matrix.mul_assoc, hvb, Matrix.mul_assoc]
  let u : Matrix.unitaryGroup (Fin n) ℂ := ⟨U, hU⟩
  let v : Matrix.unitaryGroup (Fin n) ℂ := ⟨V, hV⟩
  have hunit : Vᴴ * U ∈ Matrix.unitaryGroup (Fin n) ℂ := (star v * u).property
  exact schur_unitary_intertwiner_diagonal A B (Vᴴ * U) hA hB hd hinj hi hunit

end
end GinibrePoincare
