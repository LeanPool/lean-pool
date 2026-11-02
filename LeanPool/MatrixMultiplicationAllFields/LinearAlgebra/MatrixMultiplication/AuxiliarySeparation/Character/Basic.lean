/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Character/Basic.lean`, by
Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K` algebraically
closed; docstrings updated from ℂ to `K`.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.Tensor.ComplexTensor
public import Mathlib.Logic.Equiv.Prod
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Characters of finite tensors over `K`

The tensor operations in this file are the coefficient operations from
`MatrixMultiplication.Foundation.Tensor`. A character is an assumption on those
operations, not an assertion that a character exists. Restriction monotonicity
forces invariance under independent invertible changes of coordinates, so this
interface descends to the mutual-restriction classes of Section 3 of the paper.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable (K) in
/-- The scalar multiplication tensor, the multiplicative unit. -/
def unitTensor : Tensor K PUnit PUnit PUnit := fun _ _ _ => 1

variable (K) in
/-- The direct sum of `r` scalar multiplication tensors, in diagonal coordinates. -/
def scalarTensor (r : ℕ) : Tensor K (Fin r) (Fin r) (Fin r) :=
  fun i j k => if i = j ∧ i = k then 1 else 0

variable (K) in
/-- A normalized, additive, multiplicative, restriction-monotone tensor valuation.

Index types vary over all finite types in `Type`. No character-existence result is
included among the fields or claimed by this definition.
-/
structure Character where
  /-- The nonnegative real value assigned to a finite tensor by the character. -/
  value : {X Y Z : Type} → [Fintype X] → [Fintype Y] → [Fintype Z] →
    Tensor K X Y Z → ℝ
  nonneg : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z]
    (T : Tensor K X Y Z), 0 ≤ value T
  map_zero : ∀ {X Y Z : Type} [Fintype X] [Fintype Y] [Fintype Z],
    value (0 : Tensor K X Y Z) = 0
  map_one : value (unitTensor K) = 1
  map_directSum : ∀ {ι X Y Z : Type} [Fintype ι] [DecidableEq ι]
    [Fintype X] [Fintype Y] [Fintype Z] (T : ι → Tensor K X Y Z),
    value (Tensor.directSum T) = ∑ i, value (T i)
  map_product : ∀ {X Y Z U V W : Type} [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype U] [Fintype V] [Fintype W]
    (T : Tensor K X Y Z) (S : Tensor K U V W),
    value (Tensor.product T S) = value T * value S
  monotone : ∀ {X Y Z X' Y' Z' : Type}
    [Fintype X] [Fintype Y] [Fintype Z]
    [Fintype X'] [Fintype Y'] [Fintype Z']
    (T : Tensor K X Y Z) (A : X' → X → K)
    (B : Y' → Y → K) (C : Z' → Z → K),
    value (Tensor.restrict A B C T) ≤ value T

namespace Character

variable (χ : Character K)
variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

/-- Coordinate pullbacks are restrictions. -/
theorem value_pullback_le (T : Tensor K X Y Z)
    (fx : X' → X) (fy : Y' → Y) (fz : Z' → Z) :
    χ.value (Tensor.pullback fx fy fz T) ≤ χ.value T := by
  classical
  rw [Tensor.pullback_eq_restrict]
  exact χ.monotone T _ _ _

/-- Independent coordinate bijections preserve a character. -/
theorem value_reindex (T : Tensor K X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.value (Tensor.pullback ex ey ez T) = χ.value T := by
  apply le_antisymm (χ.value_pullback_le T ex ey ez)
  have h := χ.value_pullback_le (Tensor.pullback ex ey ez T) ex.symm ey.symm ez.symm
  have heq : Tensor.pullback ex.symm ey.symm ez.symm
      (Tensor.pullback ex ey ez T) = T := by
    funext x y z
    simp [Tensor.pullback]
  simpa only [heq] using h

/-- The character has the same value on mutually restricting tensors. -/
theorem value_eq_of_mutual_restriction (T : Tensor K X Y Z) (S : Tensor K X' Y' Z')
    (A : X' → X → K) (B : Y' → Y → K) (C : Z' → Z → K)
    (A' : X → X' → K) (B' : Y → Y' → K) (C' : Z → Z' → K)
    (hS : S = Tensor.restrict A B C T) (hT : T = Tensor.restrict A' B' C' S) :
    χ.value T = χ.value S := by
  apply le_antisymm
  · calc
      χ.value T = χ.value (Tensor.restrict A' B' C' S) := congrArg χ.value hT
      _ ≤ χ.value S := χ.monotone S A' B' C'
  · calc
      χ.value S = χ.value (Tensor.restrict A B C T) := congrArg χ.value hS
      _ ≤ χ.value T := χ.monotone T A B C

/-- An integer scalar tensor has its expected character value. -/
@[simp] theorem value_scalarTensor (r : ℕ) : χ.value (scalarTensor K r) = r := by
  let T : Fin r → Tensor K PUnit PUnit PUnit := fun _ => (unitTensor K)
  have heq : Tensor.pullback (Equiv.prodPUnit (Fin r)).symm
      (Equiv.prodPUnit (Fin r)).symm (Equiv.prodPUnit (Fin r)).symm
      (Tensor.directSum T) = scalarTensor K r := by
    rfl
  rw [← heq, χ.value_reindex, χ.map_directSum]
  simp [T, χ.map_one]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Restricting a diagonal scalar tensor realizes a rank decomposition. -/
theorem restrict_scalarTensor (r : ℕ) (a : Fin r → X → K)
    (b : Fin r → Y → K) (c : Fin r → Z → K) :
    Tensor.restrict (fun x i => a i x) (fun y i => b i y) (fun z i => c i z)
      (scalarTensor K r) =
      fun x y z => ∑ i, Tensor.rankOne (a i) (b i) (c i) x y z := by
  classical
  funext x y z
  simp [Tensor.restrict, scalarTensor, Tensor.rankOne, mul_ite, ite_and]

/-- Character values are bounded by every exact rank decomposition size. -/
theorem value_le_rank {T : Tensor K X Y Z} {r : ℕ} (h : Tensor.RankAtMost T r) :
    χ.value T ≤ r := by
  rcases h with ⟨a, b, c, rfl⟩
  rw [← restrict_scalarTensor r a b c]
  exact (χ.monotone (scalarTensor K r) _ _ _).trans_eq (χ.value_scalarTensor r)

/-- Every nonzero tensor restricts to the scalar multiplication tensor. -/
theorem one_le_value {T : Tensor K X Y Z} (hT : T ≠ 0) : 1 ≤ χ.value T := by
  classical
  obtain ⟨x, hx⟩ := Function.ne_iff.mp hT
  obtain ⟨y, hy⟩ := Function.ne_iff.mp hx
  obtain ⟨z, hz⟩ := Function.ne_iff.mp hy
  change T x y z ≠ 0 at hz
  let A : PUnit → X → K := fun _ x' => if x' = x then (T x y z)⁻¹ else 0
  let B : PUnit → Y → K := fun _ y' => if y' = y then 1 else 0
  let C : PUnit → Z → K := fun _ z' => if z' = z then 1 else 0
  have heq : Tensor.restrict A B C T = (unitTensor K) := by
    funext i j k
    simp [Tensor.restrict, A, B, C, unitTensor, ite_mul, mul_ite, hz]
  simpa only [heq, χ.map_one] using χ.monotone T A B C

/-- Normalization and restriction monotonicity make the character faithful. -/
@[simp] theorem value_eq_zero_iff (T : Tensor K X Y Z) : χ.value T = 0 ↔ T = 0 := by
  constructor
  · intro h
    by_contra hT
    have hle := χ.one_le_value hT
    rw [h] at hle
    exact (not_le_of_gt zero_lt_one) hle
  · rintro rfl
    exact χ.map_zero

end Character

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
