/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Border.WeightedModel

/-!
# A sum of independently weighted products

The site order throughout is output, left input, right input.
The spectral tensor semiring uses direct sum and tensor product.
-/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Sums
open Spectral Filter

/-- The data for the shape construction, including `i`, `j`, `k`, `hi`, `hj`. -/
structure Shape where
  /-- The `Shape` field of type `ℕ`. -/
  i : ℕ
  /-- The `Shape` field of type `ℕ`. -/
  j : ℕ
  /-- The `Shape` field of type `ℕ`. -/
  k : ℕ
  hi : 0 < i
  hj : 0 < j
  hk : 0 < k

/-- The indexing data represented by `Fin v.i → Fin v.j → Fin v.k → F`. -/
abbrev Weights (F : Type) (v : Shape) := Fin v.i → Fin v.j → Fin v.k → F
/-- Computes the three by the application `Tensor F (Fin 3)`. -/
abbrev Three (F : Type) [Field F] := Tensor F (Fin 3)

variable {F : Type} [Field F] {n : ℕ}

/-- The infimum of `{r : ℕ | A ≤ (r : Three F)}`. -/
def rank (A : Three F) : ℕ := sInf {r : ℕ | A ≤ (r : Three F)}

/-- The quantity computed by `limUnder atTop fun t : ℕ => (rank (A ^ t) : ℝ) ^ (t : ℝ)⁻¹`. -/
def asymptotic (A : Three F) : ℝ :=
  limUnder atTop fun t : ℕ => (rank (A ^ t) : ℝ) ^ (t : ℝ)⁻¹

/-- The sum of `weightedTensor (w t)` indexed by `t`. -/
def blocks (v : Fin n → Shape) (w : ∀ t, Weights F (v t)) : Three F :=
  ∑ t, weightedTensor (w t)

/-- Evaluates `1` at the input `_ _ _ _`. -/
def unweighted (F : Type) [Field F] (v : Fin n → Shape) : ∀ t, Weights F (v t) :=
  fun _ _ _ _ => 1

/-- The quantity computed by `-(∑ i, p i * Real.log (p i))`. -/
def entropy (p : Fin n → ℝ) := -(∑ i, p i * Real.log (p i))

/-- The sum of `p i * Real.log (q (v i))` indexed by `i`. -/
def mean (v : Fin n → Shape) (p : Fin n → ℝ) (q : Shape → ℕ) :=
  ∑ i, p i * Real.log (q (v i))

/-- The quantity computed by `entropy p + L (mean v p Shape.i) (mean v p Shape.j) (mean v p
Shape.k)`. -/
def objective (L : ℝ → ℝ → ℝ → ℝ) (v : Fin n → Shape) (p : Fin n → ℝ) :=
  entropy p + L (mean v p Shape.i) (mean v p Shape.j) (mean v p Shape.k)

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle.Sums
