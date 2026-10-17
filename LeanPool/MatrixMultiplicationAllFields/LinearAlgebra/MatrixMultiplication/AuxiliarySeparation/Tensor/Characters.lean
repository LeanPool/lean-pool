/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/Characters.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K` algebraically
closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.Semiring
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.BinaryCharacter
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.DirectSumClass
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Concrete tensor characters and the tensor semiring

The coefficient-level character interface and monotone real-valued semiring
homomorphisms on mutual-restriction classes describe the same valuations.
The map `classOf` uses finite natural-number coordinate presentations, so
the construction applies to all finite coordinate types in the character
interface.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

open TensorSemiring

namespace Character

/-- A character has a well-defined value on mutual-restriction classes. -/
def valueOnTensorClass (χ : Character K) : (TensorClass K) → ℝ :=
  Quotient.lift (fun T : (FiniteTensor K) => χ.value T.coeff) (by
    intro T S h
    apply le_antisymm
    · rcases h.1 with ⟨A, B, C, heq⟩
      rw [heq]
      exact χ.monotone S.coeff A B C
    · rcases h.2 with ⟨A, B, C, heq⟩
      rw [heq]
      exact χ.monotone T.coeff A B C)

@[simp] theorem valueOnTensorClass_tensorClass (χ : Character K) (T : (FiniteTensor K)) :
    χ.valueOnTensorClass (tensorClass T) = χ.value T.coeff := rfl

/-- Passing to a finite natural-coordinate presentation preserves the value. -/
@[simp] theorem valueOnTensorClass_classOf (χ : Character K)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : χ.valueOnTensorClass (classOf T) = χ.value T :=
  χ.value_reindex T _ _ _

/-- Restriction monotonicity descends to the quotient order. -/
theorem valueOnTensorClass_monotone (χ : Character K) : Monotone χ.valueOnTensorClass := by
  intro T S h
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change IsRestriction T.coeff S.coeff at h
  rcases h with ⟨A, B, C, heq⟩
  change χ.value T.coeff ≤ χ.value S.coeff
  rw [heq]
  exact χ.monotone S.coeff A B C

@[simp] theorem valueOnTensorClass_zero (χ : Character K) :
    χ.valueOnTensorClass 0 = 0 := by
  change χ.valueOnTensorClass (classOf (0 : Tensor K Empty Empty Empty)) = 0
  rw [χ.valueOnTensorClass_classOf, χ.map_zero]

@[simp] theorem valueOnTensorClass_one (χ : Character K) :
    χ.valueOnTensorClass 1 = 1 := by
  change χ.valueOnTensorClass (classOf (unitTensor K)) = 1
  rw [χ.valueOnTensorClass_classOf, χ.map_one]

/-- Multiplicativity is unchanged on passing to tensor classes. -/
theorem valueOnTensorClass_mul (χ : Character K) (T S : (TensorClass K)) :
    χ.valueOnTensorClass (T * S) = χ.valueOnTensorClass T * χ.valueOnTensorClass S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change χ.valueOnTensorClass (tensorClass T * tensorClass S) =
    χ.valueOnTensorClass (tensorClass T) * χ.valueOnTensorClass (tensorClass S)
  rw [← classOf_coeff T, ← classOf_coeff S, ← classOf_product]
  simp only [χ.valueOnTensorClass_classOf]
  exact χ.map_product T.coeff S.coeff

/-- Additivity is unchanged on passing to tensor classes. -/
theorem valueOnTensorClass_add (χ : Character K) (T S : (TensorClass K)) :
    χ.valueOnTensorClass (T + S) = χ.valueOnTensorClass T + χ.valueOnTensorClass S := by
  induction T using Quotient.inductionOn with | h T =>
  induction S using Quotient.inductionOn with | h S =>
  change χ.valueOnTensorClass (tensorClass T + tensorClass S) =
    χ.valueOnTensorClass (tensorClass T) + χ.valueOnTensorClass (tensorClass S)
  rw [← classOf_coeff T, ← classOf_coeff S, ← classOf_sum]
  simp only [χ.valueOnTensorClass_classOf]
  exact χ.value_sumTensor T.coeff S.coeff

/-- A coefficient-level character descends to a normalized semiring homomorphism. -/
def toTensorClassHom (χ : Character K) : (TensorClass K) →+* ℝ where
  toFun := χ.valueOnTensorClass
  map_zero' := χ.valueOnTensorClass_zero
  map_one' := χ.valueOnTensorClass_one
  map_add' := χ.valueOnTensorClass_add
  map_mul' := χ.valueOnTensorClass_mul

theorem toTensorClassHom_monotone (χ : Character K) : Monotone χ.toTensorClassHom :=
  χ.valueOnTensorClass_monotone

@[simp] theorem toTensorClassHom_classOf (χ : Character K)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : χ.toTensorClassHom (classOf T) = χ.value T :=
  χ.valueOnTensorClass_classOf T

/-- A monotone semiring homomorphism on tensor classes gives a character on all
finite coefficient tensors. Normalization follows from preservation of `0` and `1`. -/
def ofTensorClassHom (φ : (TensorClass K) →+* ℝ) (hφ : Monotone φ) : Character K where
  value := fun T => φ (classOf T)
  nonneg := by
    intro X Y Z hX hY hZ T
    simpa only [φ.map_zero] using hφ (TensorSemiring.zero_le (classOf T))
  map_zero := by
    intro X Y Z hX hY hZ
    rw [classOf_zero]
    exact φ.map_zero
  map_one := by
    change φ 1 = 1
    exact φ.map_one
  map_directSum := by
    intro ι X Y Z hι dι hX hY hZ T
    rw [classOf_directSum, map_sum]
  map_product := by
    intro X Y Z U V W hX hY hZ hU hV hW T S
    rw [classOf_product, map_mul]
  monotone := by
    intro X Y Z X' Y' Z' hX hY hZ hX' hY' hZ' T A B C
    apply hφ
    exact (classOf_le_iff _ _).mpr ⟨A, B, C, rfl⟩

@[simp] theorem ofTensorClassHom_value (φ : (TensorClass K) →+* ℝ) (hφ : Monotone φ)
    {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z) : (ofTensorClassHom φ hφ).value T = φ (classOf T) := rfl

/-- Equality of all coefficient-level values determines a character. -/
@[ext] theorem ext {χ ψ : Character K}
    (h : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
      (T : Tensor K X Y Z), χ.value T = ψ.value T) : χ = ψ := by
  cases χ
  cases ψ
  congr
  funext X Y Z hX hY hZ T
  exact h T

/-- Descending and then lifting recovers the original coefficient-level character. -/
@[simp] theorem ofTensorClassHom_toTensorClassHom (χ : Character K) :
    ofTensorClassHom χ.toTensorClassHom χ.toTensorClassHom_monotone = χ := by
  apply ext
  intro X Y Z hX hY hZ T
  exact χ.toTensorClassHom_classOf T

/-- Lifting and then descending recovers the original semiring homomorphism. -/
@[simp] theorem toTensorClassHom_ofTensorClassHom
    (φ : (TensorClass K) →+* ℝ) (hφ : Monotone φ) :
    (ofTensorClassHom φ hφ).toTensorClassHom = φ := by
  apply RingHom.ext
  intro T
  induction T using Quotient.inductionOn with | h T =>
  change φ (classOf T.coeff) = φ (tensorClass T)
  rw [classOf_coeff]

/-- Concrete characters are exactly monotone real-valued tensor semiring homomorphisms. -/
def tensorClassHomEquiv : Character K ≃ {φ : (TensorClass K) →+* ℝ // Monotone φ} where
  toFun χ := ⟨χ.toTensorClassHom, χ.toTensorClassHom_monotone⟩
  invFun φ := ofTensorClassHom φ.1 φ.2
  left_inv := ofTensorClassHom_toTensorClassHom
  right_inv φ := Subtype.ext (toTensorClassHom_ofTensorClassHom φ.1 φ.2)

end Character

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
