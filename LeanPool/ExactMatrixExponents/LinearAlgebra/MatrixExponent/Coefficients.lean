/-
Copyright (c) 2026 the original authors. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/
/- Modified by Lean Pool contributors for this port. -/
module

public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Sparse.Law
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Mask
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.Rectangle.Profile.Pairing
public import LeanPool.ExactMatrixExponents.LinearAlgebra.TensorSpectrum.Additive.RankAnalysis
public import LeanPool.ExactMatrixExponents.LinearAlgebra.MatrixExponent.LocalTensor
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexMatrixTensor
public import Mathlib.FieldTheory.IsAlgClosed.AlgebraicClosure

/-!
# Choosing coefficients for the upper bound

The tensor semiring is monomorphic. To reuse it without assuming
characteristic zero, choose an algebraically closed counterexample if one
exists. The tensor argument only uses the field axioms and algebraic closure.
-/

@[expose] public section

noncomputable section

namespace MatrixMultiplicationAllFields.MatrixExponent

/-- The data for the closed field construction, including `carrier`, `[field`, `[closed`. -/
structure ClosedField where
  /-- The `ClosedField` component of type `Type`. -/
  carrier : Type
  [field : Field carrier]
  [closed : IsAlgClosed carrier]

attribute [instance] ClosedField.field ClosedField.closed

instance : Nonempty ClosedField := ⟨⟨AlgebraicClosure ℚ⟩⟩

/-- The defining condition `∀ A B C : ℕ, 0 < A → 0 < B → 0 < C → Rectangle.exponent F ((A : ℝ) *
B) ((A : ℝ) * C) ((B : ℝ) * C) ≤ ((A : ℝ) + B + C) ^ 2 / 4`. -/
def Rectangle.DiscreteBound (F : Type*) [Field F] : Prop :=
  ∀ A B C : ℕ, 0 < A → 0 < B → 0 < C →
    Rectangle.exponent F ((A : ℝ) * B) ((A : ℝ) * C) ((B : ℝ) * C) ≤ ((A : ℝ) + B + C) ^ 2 / 4

/-- Field-independent consequences of the shared-tag inequality. No
law assumes square equality or any conjecture about spectral contacts. -/
structure Fulfills (F : Type) [Field F] : Prop where
  discrete : Rectangle.DiscreteBound F
  density : Rectangle.DensityBound F
  cells : Rectangle.CellBound F
  binary : Rectangle.Profile.BinaryLaw F
  degrees : Rectangle.Sparse.DegreeBound F

/-- The indexed operation `Classical.epsilon (fun k : ClosedField => ¬ Fulfills k.carrier)`. -/
def candidate : ClosedField :=
  Classical.epsilon (fun k : ClosedField => ¬ Fulfills k.carrier)

/-- Uses `candidate.carrier` as the representation. -/
abbrev Coeff := candidate.carrier

theorem closed_laws (h : Fulfills Coeff) (K : Type) [Field K] [IsAlgClosed K] :
    Fulfills K := by
  by_contra bad
  have ex : ∃ k : ClosedField, ¬ Fulfills k.carrier := ⟨⟨K⟩, bad⟩
  exact Classical.epsilon_spec ex h

theorem exists_nonzero_nodes {F : Type*} [Field F] [Infinite F] (n : ℕ) :
    ∃ nodes : Fin n → F, Function.Injective nodes ∧ ∀ i, nodes i ≠ 0 := by
  let e : Fin n ↪ ({0}ᶜ : Set F) :=
    Fin.valEmbedding.trans ((Set.finite_singleton (0 : F)).infinite_compl.natEmbedding _)
  exact ⟨fun i => e i, Subtype.val_injective.comp e.injective, fun i => (e i).property⟩

end MatrixMultiplicationAllFields.MatrixExponent

namespace MatrixMultiplicationAllFields.MatrixExponent.Upper
open MatrixMultiplicationAllFields.MatrixMultiplication.Foundation

/-- Computes the matrix tensor by the application `Tensor.matrixCoefficients (Fin a) (Fin b)
(Fin c)`. -/
def matrixTensor (a b c : ℕ) :
    Tensor Coeff (Fin a × Fin b) (Fin b × Fin c) (Fin c × Fin a) :=
  Tensor.matrixCoefficients (Fin a) (Fin b) (Fin c)

end MatrixMultiplicationAllFields.MatrixExponent.Upper
