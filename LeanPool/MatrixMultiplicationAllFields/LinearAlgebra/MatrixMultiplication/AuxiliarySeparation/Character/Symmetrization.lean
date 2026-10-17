/-
Copyright (c) 2026 OpenAI and Jeroen Zuiddam. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI, Jeroen Zuiddam
-/
module

/-
Modified from openai/math (adc7f1241), file
`lean/OAI/LinearAlgebra/MatrixMultiplication/AuxiliarySeparation/Character/Symmetrization.lean`,
by Jeroen Zuiddam, 2026: `ℂ` replaced by a field `K`; no declaration here needs `K`
algebraically closed.
-/
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Growth.PermutationProduct
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Character.Basic
public import LeanPool.MatrixMultiplicationAllFields.LinearAlgebra.MatrixMultiplication.AuxiliarySeparation.Convolution.Basic
public import Mathlib.Analysis.SpecialFunctions.Pow.Real
public import Mathlib.FieldTheory.IsAlgClosed.Basic

/- Ported to Lean Pool with project-local modules and namespaces. -/

/-!
# The symmetrized tensor-character product

The sixfold product is defined on arbitrary finite, possibly different, leg
spaces. Its symmetry follows by permuting the factors and requires no symmetry
of the character itself.
-/

@[expose] public section

namespace MatrixMultiplicationAllFields

variable {K : Type} [Field K]



noncomputable section

namespace MatrixMultiplication.AuxiliarySeparation

namespace Character

open MatrixMultiplication.Foundation

variable (χ : Character K)
variable {X Y Z X' Y' Z' : Type}
variable [Fintype X] [Fintype Y] [Fintype Z]
variable [Fintype X'] [Fintype Y'] [Fintype Z']

/-- The product of character values in the six orders of possibly different legs. -/
def sixfoldProduct (T : Tensor K X Y Z) : ℝ :=
  χ.value T *
    χ.value (fun y z x => T x y z) *
    χ.value (fun z x y => T x y z) *
    χ.value (fun x z y => T x y z) *
    χ.value (fun z y x => T x y z) *
    χ.value (fun y x z => T x y z)

/-- Cycling the legs permutes the six factors. -/
theorem sixfoldProduct_cyclic (T : Tensor K X Y Z) :
    χ.sixfoldProduct (fun y z x => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]
  ring

/-- Exchanging the first two legs permutes the six factors. -/
theorem sixfoldProduct_swap12 (T : Tensor K X Y Z) :
    χ.sixfoldProduct (fun y x z => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]
  ring

/-- The leg exchange used by the middle convolution branch preserves the product. -/
theorem sixfoldProduct_swap23 (T : Tensor K X Y Z) :
    χ.sixfoldProduct (fun x z y => T x y z) = χ.sixfoldProduct T := by
  dsimp [sixfoldProduct]
  ring

/-- Changing coordinates separately on the legs preserves the sixfold product. -/
theorem sixfoldProduct_reindex (T : Tensor K X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.sixfoldProduct (Tensor.pullback ex ey ez T) = χ.sixfoldProduct T := by
  unfold sixfoldProduct
  rw [χ.value_reindex T ex ey ez]
  have h1 := χ.value_reindex (fun y z x => T x y z) ey ez ex
  have h2 := χ.value_reindex (fun z x y => T x y z) ez ex ey
  have h3 := χ.value_reindex (fun x z y => T x y z) ex ez ey
  have h4 := χ.value_reindex (fun z y x => T x y z) ez ey ex
  have h5 := χ.value_reindex (fun y x z => T x y z) ey ex ez
  change χ.value (fun y z x => T (ex x) (ey y) (ez z)) =
    χ.value (fun y z x => T x y z) at h1
  change χ.value (fun z x y => T (ex x) (ey y) (ez z)) =
    χ.value (fun z x y => T x y z) at h2
  change χ.value (fun x z y => T (ex x) (ey y) (ez z)) =
    χ.value (fun x z y => T x y z) at h3
  change χ.value (fun z y x => T (ex x) (ey y) (ez z)) =
    χ.value (fun z y x => T x y z) at h4
  change χ.value (fun y x z => T (ex x) (ey y) (ez z)) =
    χ.value (fun y x z => T x y z) at h5
  simp only [Tensor.pullback]
  rw [h1, h2, h3, h4, h5]

/-- Commuting convolution inputs preserves the sixfold character product. -/
theorem sixfoldProduct_convolution_comm (a b : ℕ) :
    χ.sixfoldProduct (convolution K a b) = χ.sixfoldProduct (convolution K b a) := by
  let e : Fin (a + b - 1) ≃ Fin (b + a - 1) := finCongr (by omega)
  have heq : Tensor.pullback (Equiv.refl (Fin b)) (Equiv.refl (Fin a)) e
      (convolution K b a) = fun j i k => convolution K a b i j k := by
    funext j i k
    exact (convolution_comm a b i j k).symm
  have h := χ.sixfoldProduct_reindex (convolution K b a)
    (Equiv.refl (Fin b)) (Equiv.refl (Fin a)) e
  rw [heq, χ.sixfoldProduct_swap12] at h
  exact h

/-- The Section 5 symmetrized value with mean singleton-leg exponent `t`. -/
def symmetrizedProfile (t : ℝ) (T : Tensor K X Y Z) : ℝ :=
  χ.sixfoldProduct T ^ (1 / (6 * t))

theorem symmetrizedProfile_cyclic (t : ℝ) (T : Tensor K X Y Z) :
    χ.symmetrizedProfile t (fun y z x => T x y z) = χ.symmetrizedProfile t T := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * t))) (χ.sixfoldProduct_cyclic T)

theorem symmetrizedProfile_swap12 (t : ℝ) (T : Tensor K X Y Z) :
    χ.symmetrizedProfile t (fun y x z => T x y z) = χ.symmetrizedProfile t T := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * t))) (χ.sixfoldProduct_swap12 T)

theorem symmetrizedProfile_swap23 (t : ℝ) (T : Tensor K X Y Z) :
    χ.symmetrizedProfile t (fun x z y => T x y z) = χ.symmetrizedProfile t T := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * t))) (χ.sixfoldProduct_swap23 T)

theorem symmetrizedProfile_reindex (t : ℝ) (T : Tensor K X Y Z)
    (ex : X' ≃ X) (ey : Y' ≃ Y) (ez : Z' ≃ Z) :
    χ.symmetrizedProfile t (Tensor.pullback ex ey ez T) = χ.symmetrizedProfile t T := by
  exact congrArg (fun s : ℝ => s ^ (1 / (6 * t))) (χ.sixfoldProduct_reindex T ex ey ez)

end Character

end MatrixMultiplication.AuxiliarySeparation

end

end MatrixMultiplicationAllFields
