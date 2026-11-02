/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Character/Permutation.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K` algebraically
closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Dot
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Symmetrization
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The six permuted tensor characters

Precomposing a character with a leg permutation gives another character. The
six resulting values multiply to the symmetrized product, and each singleton
leg exponent occurs twice among their first-leg exponents.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation.Character

variable (χ : Character K)

/-- The reflected character exchanges the second and third tensor legs. -/
def swap23Character : Character K where
  value T := χ.value (fun x z y => T x y z)
  nonneg T := χ.nonneg (fun x z y => T x y z)
  map_zero := χ.map_zero
  map_one := χ.map_one
  map_directSum T := by
    have heq : (fun x z y => Tensor.directSum T x y z) =
        Tensor.directSum (fun i x z y => T i x y z) := by
      funext x z y
      simp only [Tensor.directSum, and_comm]
    change χ.value (fun x z y => Tensor.directSum T x y z) = _
    rw [heq, χ.map_directSum]
  map_product T S := χ.map_product (fun x z y => T x y z) (fun x z y => S x y z)
  monotone T A B C := by
    have heq : (fun x z y => Tensor.restrict A B C T x y z) =
        Tensor.restrict A C B (fun x z y => T x y z) := by
      funext x z y
      simp only [Tensor.restrict]
      apply Finset.sum_congr rfl
      intro i hi
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro k hk
      apply Finset.sum_congr rfl
      intro j hj
      ring
    change χ.value (fun x z y => Tensor.restrict A B C T x y z) ≤ _
    rw [heq]
    exact χ.monotone (fun x z y => T x y z) A C B

@[simp] theorem swap23Character_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z) :
    χ.swap23Character.value T = χ.value (fun x z y => T x y z) := rfl

/-- The three cyclic orders followed by their reflected orders. -/
def permutedCharacter (i : Fin 6) : Character K :=
  ![χ, χ.cyclicCharacter, χ.cyclicCharacter.cyclicCharacter,
    χ.swap23Character, χ.swap23Character.cyclicCharacter,
    χ.swap23Character.cyclicCharacter.cyclicCharacter] i

/-- The six permuted characters give exactly the sixfold product on any legs. -/
theorem prod_permutedCharacter_value {X Y Z : Type}
    [Fintype X] [Fintype Y] [Fintype Z] (T : Tensor K X Y Z) :
    (∏ i : Fin 6, (χ.permutedCharacter i).value T) = χ.sixfoldProduct T := by
  simp only [Fin.prod_univ_succ, Fin.prod_univ_zero, mul_one]
  change χ.value T * (χ.value (fun y z x => T x y z) *
      (χ.value (fun z x y => T x y z) * (χ.value (fun x z y => T x y z) *
      (χ.value (fun y x z => T x y z) * χ.value (fun z y x => T x y z))))) = _
  unfold sixfoldProduct
  ring

@[simp] theorem cyclicCharacter_pX : χ.cyclicCharacter.pX = χ.pZ := by
  rfl

@[simp] theorem cyclicCharacter_pY : χ.cyclicCharacter.pY = χ.pX := rfl

@[simp] theorem cyclicCharacter_pZ : χ.cyclicCharacter.pZ = χ.pY := rfl

@[simp] theorem swap23Character_pX : χ.swap23Character.pX = χ.pX := by
  unfold pX pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

@[simp] theorem swap23Character_pY : χ.swap23Character.pY = χ.pZ := by
  unfold pY pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

@[simp] theorem swap23Character_pZ : χ.swap23Character.pZ = χ.pY := by
  unfold pY pZ
  simp only [cyclicCharacter_value, swap23Character_value]
  congr 2
  apply congrArg χ.value
  funext x y z
  simp [Tensor.cyclic, Tensor.dotPairing, eq_comm]

/-- Each singleton-leg exponent occurs twice among the first-leg exponents. -/
theorem sum_permutedCharacter_pX :
    (∑ i : Fin 6, (χ.permutedCharacter i).pX) = 2 * (χ.pX + χ.pY + χ.pZ) := by
  simp [permutedCharacter, Fin.sum_univ_succ]
  ring

end MatrixMultiplication.AuxiliarySeparation.Character

end

end MatrixMultiplicationAllFields
