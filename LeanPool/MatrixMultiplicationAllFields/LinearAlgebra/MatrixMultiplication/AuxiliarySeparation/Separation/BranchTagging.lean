/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Separation/BranchTagging.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K`
algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Separation.Basic
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Tensor.SupportExtension
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# Recovering branch tags from coordinate support

When both non-shared coordinates determine a branch label, adding explicit
matching branch tags does not change a character's value. The tags can be
recovered by independent coordinate maps, and forgetting them recovers the
original coefficientwise sum of branches.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

open MatrixMultiplication.Foundation
open scoped BigOperators

namespace MatrixMultiplication.AuxiliarySeparation

variable {M : ℕ} {X Y Z : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]

omit [Fintype X] [Fintype Y] [Fintype Z] in
/-- Recovering the two coordinate labels identifies the tagged tensor with
the coefficientwise sum of the branches. -/
theorem sharedFirstTensor_pullback_labels
    (B : Fin M → Tensor K X Y Z) (ly : Y → Fin M) (lz : Z → Fin M)
    (hsupport : ∀ i x y z, B i x y z ≠ 0 → ly y = i ∧ lz z = i) :
    Tensor.pullback id (fun y => (ly y, y)) (fun z => (lz z, z))
      (sharedFirstTensor B) = ∑ i, B i := by
  classical
  funext x y z
  simp only [Finset.sum_apply]
  change (if ly y = lz z then B (ly y) x y z else 0) = ∑ i, B i x y z
  have hsum : (∑ i, B i x y z) = B (ly y) x y z := by
    apply Finset.sum_eq_single (ly y)
    · intro i _ hi
      by_contra h
      exact hi (hsupport i x y z h).1.symm
    · simp
  rw [hsum]
  split_ifs with h
  · rfl
  · symm
    by_contra hb
    exact h ((hsupport (ly y) x y z hb).2.symm)

namespace Character

/-- Branch labels determined by both non-shared coordinates can be inserted
or forgotten without changing a character. -/
theorem value_sharedFirstTensor_eq_sum (χ : Character K)
    (B : Fin M → Tensor K X Y Z) (ly : Y → Fin M) (lz : Z → Fin M)
    (hsupport : ∀ i x y z, B i x y z ≠ 0 → ly y = i ∧ lz z = i) :
    χ.value (sharedFirstTensor B) = χ.value (∑ i, B i) := by
  have hs : ∀ x y z, sharedFirstTensor B x y z ≠ 0 →
      x ∈ Set.range (id : X → X) ∧
        y ∈ Set.range (fun y => (ly y, y)) ∧
        z ∈ Set.range (fun z => (lz z, z)) := by
    intro x y z h
    have hyz : y.1 = z.1 := by
      by_contra hne
      exact h (by simp [sharedFirstTensor, hne])
    have hb : B y.1 x y.2 z.2 ≠ 0 := by
      simpa only [sharedFirstTensor, hyz, ↓reduceIte] using h
    obtain ⟨hy, hz⟩ := hsupport y.1 x y.2 z.2 hb
    exact ⟨⟨x, rfl⟩, ⟨y.2, Prod.ext hy rfl⟩,
      ⟨z.2, Prod.ext (hz.trans hyz) rfl⟩⟩
  have heq := χ.value_eq_pullback_of_support (sharedFirstTensor B) id
    (fun y => (ly y, y)) (fun z => (lz z, z)) Function.injective_id
    (fun _ _ h => congrArg Prod.snd h) (fun _ _ h => congrArg Prod.snd h) hs
  rw [sharedFirstTensor_pullback_labels B ly lz hsupport] at heq
  exact heq

end Character
end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
