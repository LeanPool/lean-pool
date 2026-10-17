/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Tensor/SupportExtension.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K`
algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.CharacterBounds
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Recovering tensors from their supported coordinate subspaces

If a tensor has support inside three injectively embedded coordinate sets, it
is exactly the extension by zero of its pullback to those sets. Characters
therefore have the same value on the ambient tensor and this smaller tensor.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



namespace MatrixMultiplication.AuxiliarySeparation

open MatrixMultiplication.Foundation


variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

open Classical in
omit [Fintype X'] [Fintype Y'] [Fintype Z'] in
/-- Support in embedded coordinate sets reconstructs the tensor by zero extension. -/
theorem tensor_eq_extendByZero_pullback (T : Tensor K X' Y' Z')
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 →
      x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz) :
    T = Tensor.restrict
      (fun x' x => if fx x = x' then 1 else 0)
      (fun y' y => if fy y = y' then 1 else 0)
      (fun z' z => if fz z = z' then 1 else 0)
      (Tensor.pullback fx fy fz T) := by
  classical
  funext x' y' z'
  by_cases hx' : x' ∈ Set.range fx
  · obtain ⟨x, rfl⟩ := hx'
    by_cases hy' : y' ∈ Set.range fy
    · obtain ⟨y, rfl⟩ := hy'
      by_cases hz' : z' ∈ Set.range fz
      · obtain ⟨z, rfl⟩ := hz'
        simp [Tensor.restrict, Tensor.pullback, hx.eq_iff, hy.eq_iff, hz.eq_iff,
          ite_mul, mul_ite]
      · have hzero : T (fx x) (fy y) z' = 0 := by
          by_contra h
          exact hz' (hs _ _ _ h).2.2
        have hnone : ∀ z, fz z ≠ z' := fun z h => hz' ⟨z, h⟩
        simp [Tensor.restrict, hzero, hnone]
    · have hzero : T (fx x) y' z' = 0 := by
        by_contra h
        exact hy' (hs _ _ _ h).2.1
      have hnone : ∀ y, fy y ≠ y' := fun y h => hy' ⟨y, h⟩
      simp [Tensor.restrict, hzero, hnone]
  · have hzero : T x' y' z' = 0 := by
      by_contra h
      exact hx' (hs _ _ _ h).1
    have hnone : ∀ x, fx x ≠ x' := fun x h => hx' ⟨x, h⟩
    simp [Tensor.restrict, hzero, hnone]

namespace Character

/-- A character ignores ambient coordinates outside a tensor's support. -/
theorem value_eq_pullback_of_support (χ : Character K) (T : Tensor K X' Y' Z')
    (fx : X → X') (fy : Y → Y') (fz : Z → Z')
    (hx : Function.Injective fx) (hy : Function.Injective fy)
    (hz : Function.Injective fz)
    (hs : ∀ x' y' z', T x' y' z' ≠ 0 →
      x' ∈ Set.range fx ∧ y' ∈ Set.range fy ∧ z' ∈ Set.range fz) :
    χ.value T = χ.value (Tensor.pullback fx fy fz T) := by
  classical
  calc
    χ.value T = χ.value (Tensor.restrict
        (fun x' x => if fx x = x' then 1 else 0)
        (fun y' y => if fy y = y' then 1 else 0)
        (fun z' z => if fz z = z' then 1 else 0)
        (Tensor.pullback fx fy fz T)) :=
      congrArg χ.value (tensor_eq_extendByZero_pullback T fx fy fz hx hy hz hs)
    _ = _ := χ.value_extendByZero _ fx fy fz hx hy hz

end Character
end MatrixMultiplication.AuxiliarySeparation

end MatrixMultiplicationAllFields
