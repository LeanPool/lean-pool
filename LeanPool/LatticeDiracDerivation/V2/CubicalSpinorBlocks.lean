/-
Copyright (c) 2026 G. D. Partin. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: G. D. Partin
-/

-- Upstream source is used under the MIT option in G. D. Partin’s dual license.

module

public import LeanPool.LatticeDiracDerivation.V2.CubicalClifford
public import LeanPool.LatticeDiracDerivation.V2.UniformVacuumPhase
import Mathlib.Logic.Equiv.Fin.Basic

/-! # Upper and lower blocks of four-component cubical spinors -/

@[expose] public section

namespace LeanDirac.V2

noncomputable section

/-- Assemble a spinor from its two Pauli coordinate blocks. -/
def cubicalSpinorOfBlocks (upper lower : UniformCell2) : CubicalCell4 :=
  Fin.append upper lower

@[simp] theorem cubical_spinor_of_blocks_zero (upper lower : UniformCell2) :
    cubicalSpinorOfBlocks upper lower 0 = upper 0 := rfl

@[simp] theorem cubical_spinor_of_blocks_one (upper lower : UniformCell2) :
    cubicalSpinorOfBlocks upper lower 1 = upper 1 := rfl

@[simp] theorem cubical_spinor_of_blocks_two (upper lower : UniformCell2) :
    cubicalSpinorOfBlocks upper lower 2 = lower 0 := rfl

@[simp] theorem cubical_spinor_of_blocks_three (upper lower : UniformCell2) :
    cubicalSpinorOfBlocks upper lower 3 = lower 1 := rfl

/-- Restrict a four-component spinor to its upper two components. -/
def cubicalCell4Upper (spinor : CubicalCell4) : UniformCell2 :=
  ((Fin.appendEquiv 2 2).symm spinor).1

/-- Restrict a four-component spinor to its lower two components. -/
def cubicalCell4LowerHalf (spinor : CubicalCell4) : UniformCell2 :=
  ((Fin.appendEquiv 2 2).symm spinor).2

@[simp] theorem cubical_cell4_upper_zero (spinor : CubicalCell4) :
    cubicalCell4Upper spinor 0 = spinor 0 := rfl

@[simp] theorem cubical_cell4_upper_one (spinor : CubicalCell4) :
    cubicalCell4Upper spinor 1 = spinor 1 := rfl

@[simp] theorem cubical_cell4_lower_zero (spinor : CubicalCell4) :
    cubicalCell4LowerHalf spinor 0 = spinor 2 := rfl

@[simp] theorem cubical_cell4_lower_one (spinor : CubicalCell4) :
    cubicalCell4LowerHalf spinor 1 = spinor 3 := rfl

@[simp] theorem cubical_cell4_upper_of_blocks (upper lower : UniformCell2) :
    cubicalCell4Upper (cubicalSpinorOfBlocks upper lower) = upper :=
  congrArg Prod.fst ((Fin.appendEquiv 2 2).symm_apply_apply (upper, lower))

@[simp] theorem cubical_cell4_lower_of_blocks (upper lower : UniformCell2) :
    cubicalCell4LowerHalf (cubicalSpinorOfBlocks upper lower) = lower :=
  congrArg Prod.snd ((Fin.appendEquiv 2 2).symm_apply_apply (upper, lower))

theorem cubical_spinor_of_its_blocks (spinor : CubicalCell4) :
    cubicalSpinorOfBlocks (cubicalCell4Upper spinor) (cubicalCell4LowerHalf spinor) = spinor :=
  (Fin.appendEquiv 2 2).apply_symm_apply spinor

/-- Embed the native transverse position in the upper spinor block. -/
def cubicalUpperEmbedding (position : UniformCell2) : CubicalCell4 :=
  cubicalSpinorOfBlocks position 0

/-- Assemble a spinor from its two blocks by a complex-linear map. -/
def cubicalSpinorOfBlocksLinear : (UniformCell2 × UniformCell2) →ₗ[ℂ] CubicalCell4 where
  toFun blocks := cubicalSpinorOfBlocks blocks.1 blocks.2
  map_add' first second := by
    funext component
    fin_cases component <;> rfl
  map_smul' scalar blocks := by
    funext component
    fin_cases component <;> rfl

end
end LeanDirac.V2
