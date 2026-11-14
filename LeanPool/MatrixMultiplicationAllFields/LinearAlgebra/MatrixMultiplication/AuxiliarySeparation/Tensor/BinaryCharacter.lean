/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/BinaryCharacter.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K`
algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.CharacterBounds
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.DirectSum
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Character additivity for binary tensor sums

The summands may have different finite coordinate types.  A binary sum is a
coordinate reindexing of the dependent direct sum over `Bool`.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.Character

/-- A character is additive on binary direct sums with arbitrary finite
coordinate types. -/
theorem value_sumTensor (χ : Character K)
    {X Y Z U V W : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W) :
    χ.value (sumTensor T S) = χ.value T + χ.value S := by
  classical
  let family : (b : Bool) →
      Tensor K (bif b then U else X) (bif b then V else Y) (bif b then W else Z)
    | false => T
    | true => S
  let : ∀ b : Bool, Fintype (bif b then U else X) :=
    fun | false => inferInstanceAs (Fintype X) | true => inferInstanceAs (Fintype U)
  let : ∀ b : Bool, Fintype (bif b then V else Y) :=
    fun | false => inferInstanceAs (Fintype Y) | true => inferInstanceAs (Fintype V)
  let : ∀ b : Bool, Fintype (bif b then W else Z) :=
    fun | false => inferInstanceAs (Fintype Z) | true => inferInstanceAs (Fintype W)
  have heq : Tensor.pullback (Equiv.sumEquivSigmaBool X U)
      (Equiv.sumEquivSigmaBool Y V) (Equiv.sumEquivSigmaBool Z W)
      (Tensor.dependentDirectSum family) = sumTensor T S := by
    funext x y z
    cases x <;> cases y <;> cases z <;>
      simp [Tensor.pullback, Tensor.dependentDirectSum, Equiv.sumEquivSigmaBool,
        family, sumTensor]
  rw [← heq, χ.value_reindex, χ.value_dependentDirectSum]
  simp [family, add_comm]

end MatrixMultiplication.AuxiliarySeparation.Character

end

end MatrixMultiplicationAllFields
