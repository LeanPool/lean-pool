/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Weights

/-! # Output-cell restrictions of a weighted product -/

@[expose] public section

namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k : ℕ}

/-- Returns `w x y z` when `(x, y) ∈ u` holds, and `0` otherwise. -/
def mask (w : Fin i → Fin j → Fin k → F) (u : Finset (Pos i j))
    (x : Fin i) (y : Fin j) (z : Fin k) : F := if (x, y) ∈ u then w x y z else 0

/-- Logarithm of the short side of the most nearly square rectangle
of area `q` fitting in the original format. -/
noncomputable def short (i j q : ℕ) : ℝ :=
  min (min (Real.log i) (Real.log j)) (Real.log q / 2)

/-- The cell bound of type `Prop` for the given inputs. -/
def CellBound (F : Type*) [Field F] : Prop :=
  ∀ i j k r : ℕ, 0 < i → 0 < j → 0 < k →
    ∀ (w : Fin i → Fin j → Fin k → F) (u : Finset (Pos i j)),
    u.Nonempty → (∀ x y z, w x y z ≠ 0 ↔ (x, y) ∈ u) → WeightedRankLE w r →
      Real.exp (exponent F (short i j u.card)
        (Real.log u.card - short i j u.card) (Real.log k)) ≤ r

theorem short_bounds {i j q : ℕ} (hi : 0 < i) (hj : 0 < j) (hq : 0 < q) :
    0 ≤ short i j q ∧ short i j q ≤ Real.log q := by
  have hlog {n : ℕ} (hn : 0 < n) : 0 ≤ Real.log (n : ℝ) := Real.log_nonneg (by exact_mod_cast hn)
  exact ⟨le_min (le_min (hlog hi) (hlog hj)) (by linarith [hlog hq]),
    (min_le_right _ _).trans (by linarith [hlog hq])⟩

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle
