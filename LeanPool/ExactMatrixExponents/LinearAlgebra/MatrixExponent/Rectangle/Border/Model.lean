/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Weights
public import Mathlib.Algebra.MvPolynomial.Eval
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-! # Geometric closure of the rank locus in the full coefficient space -/

@[expose] public section

noncomputable section
namespace MatrixMultiplicationAllFields.MatrixExponent.Rectangle

variable {F : Type*} [Field F] {i j k : ℕ}

/-- The condition `∀ p : MvPolynomial ι F, (∀ y ∈ s, MvPolynomial.eval y p = 0) →
MvPolynomial.eval x p = 0` on the specified data. -/
def ZClosure {ι : Type} (s : Set (ι → F)) (x : ι → F) : Prop :=
  ∀ p : MvPolynomial ι F,
    (∀ y ∈ s, MvPolynomial.eval y p = 0) → MvPolynomial.eval x p = 0

/-- Indexes the coordinates by the coordinates of `Pos i k × Pos k j × Pos i j`. -/
abbrev Coordinates (i j k : ℕ) := Pos i k × Pos k j × Pos i j

/-- Evaluates `if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then w x.1 y.2 x.2 else 0` at the input `(x,
y, z)`. -/
def coefficients (w : Fin i → Fin j → Fin k → F) : Coordinates i j k → F :=
  fun (x, y, z) => if x.1 = z.1 ∧ x.2 = y.1 ∧ y.2 = z.2 then w x.1 y.2 x.2 else 0

/-- The rank set of type `Set (Coordinates i j k → F)` for the given inputs. -/
def rankSet (F : Type*) [Field F] (i j k r : ℕ) : Set (Coordinates i j k → F) :=
  {v | ∃ (a : Fin r → Pos i k → F) (b : Fin r → Pos k j → F) (c : Fin r → Pos i j → F),
    ∀ x y z, ∑ l : Fin r, a l x * b l y * c l z = v (x, y, z)}

/-- The defining condition `ZClosure (rankSet (AlgebraicClosure F) i j k r) (coefficients (fun x
y z => algebraMap F (AlgebraicClosure F) (w x y z)))`. -/
def BorderRankLE (w : Fin i → Fin j → Fin k → F) (r : ℕ) : Prop :=
  ZClosure (rankSet (AlgebraicClosure F) i j k r)
    (coefficients (fun x y z => algebraMap F (AlgebraicClosure F) (w x y z)))

end MatrixMultiplicationAllFields.MatrixExponent.Rectangle
