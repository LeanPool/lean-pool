/-
Copyright (c) 2026 Robert D. Barish. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Robert D. Barish
-/

/- Modified for Lean Pool: imports, Lean compatibility, and repository lint. -/

module

public import LeanPool.PlanarSeparator.NestedDissection.Elimination
public import Mathlib.LinearAlgebra.Matrix.PosDef

/-!
# Elimination of positive definite matrices

Every leading principal submatrix of a positive definite matrix is positive definite and so has
positive determinant.  Hence Gaussian elimination without pivoting of a positive definite matrix
(for instance a real symmetric positive definite matrix), in any order, meets only positive
pivots.

## Main results

* `NestedDissection.pivots_pos_of_posDef`, `NestedDissection.pivots_ne_zero_of_posDef`.
* `NestedDissection.pivotsIn_ne_zero_of_posDef`: the same for elimination in the order `σ`.
-/

namespace NestedDissection

open Matrix

@[expose] public section

universe u

variable {K : Type u} [Field K] [PartialOrder K] [StarRing K] [IsOrderedRing K]
  [PosMulReflectLT K]

theorem det_leading_pos_of_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : A.PosDef)
    (k : ℕ) (hk : k ≤ n) : 0 < (leading A k hk).det :=
  (hA.submatrix (Fin.castLE_injective hk)).det_pos

/-- Elimination of a positive definite matrix meets only nonzero pivots. -/
theorem pivots_ne_zero_of_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : A.PosDef)
    (j : Fin n) : pivots A j ≠ 0 :=
  pivots_ne_zero A (fun k hk _ => (det_leading_pos_of_posDef hA k hk).ne') j

/-- Elimination of a positive definite matrix meets only positive pivots. -/
theorem pivots_pos_of_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : A.PosDef)
    (j : Fin n) : 0 < pivots A j := by
  have hle : (j : ℕ) + 1 ≤ n := j.2
  have h1 := det_leading_pos_of_posDef hA _ hle
  have h0 := det_leading_pos_of_posDef hA _ (Nat.le_of_succ_le hle)
  have hp : ∀ i : Fin n, (i : ℕ) + 1 < (j : ℕ) + 1 → pivots A i ≠ 0 :=
    fun i _ => pivots_ne_zero_of_posDef hA i
  rw [det_leading_eq_prod_pivots A _ hle hp, Fin.prod_univ_castSucc] at h1
  rw [det_leading_eq_prod_pivots A _ (Nat.le_of_succ_le hle)
    fun i hi => hp i (by omega)] at h0
  have hlast : Fin.castLE hle (Fin.last j) = j := Fin.ext (by simp)
  have e : ∏ i : Fin j, pivots A (Fin.castLE hle i.castSucc) =
      ∏ i : Fin j, pivots A (Fin.castLE (Nat.le_of_succ_le hle) i) :=
    Finset.prod_congr rfl fun i _ => rfl
  rw [hlast, e] at h1
  exact pos_of_mul_pos_right h1 h0.le

/-- Elimination of a positive definite matrix in any order meets only nonzero pivots. -/
theorem pivotsIn_ne_zero_of_posDef {n : ℕ} {A : Matrix (Fin n) (Fin n) K} (hA : A.PosDef)
    (σ : Equiv.Perm (Fin n)) (j : Fin n) : pivotsIn σ A j ≠ 0 :=
  pivots_ne_zero_of_posDef (hA.submatrix σ.injective) j

end

end NestedDissection
