/-
Copyright (c) 2026 Foresight Quantum. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Foresight Quantum
-/

/- Modified for Lean Pool: updated module paths. -/

module

public import LeanPool.SuzukiCancellation.Algebra.Lie.IteratedCommutator

/-!
# The binary quintic commutator family

The eight degree-five right-nested commutators are indexed by `Fin 8`.
They form a redundant family, as used in Childs et al., Appendix J, Proposition J.1.
The definition and eight evaluation lemmas require only a ring with its associative Lie bracket.
Weighted sums of their norms are developed in `FQFP.Analysis.Normed.Algebra.BCH.CommutatorWeights`.

## Main definitions

* `FQFP.BCH.binaryQuinticCommutator` indexes the eight right-nested degree-five commutators built
  from two letters.
-/

@[expose] public section

namespace FQFP.BCH

attribute [local instance] LieRing.ofAssociativeRing

section Algebra

variable {𝔸 : Type*} [Ring 𝔸]

/-! ### The eight commutators -/

/-- The eight binary degree-five commutators, as a `Fin 8`-indexed family. Branch `i` is the
concrete bracket expression `[X₁,[X₂,[X₃,[B,A]]]]`; the evaluation lemmas give its eight forms.
Jacobi identifies zero-based indices `1` and `2`, and indices `5` and `6`. -/
def binaryQuinticCommutator (A B : 𝔸) : Fin 8 → 𝔸
  | 0 => ⁅A, ⁅A, ⁅A, ⁅B, A⁆⁆⁆⁆
  | 1 => ⁅A, ⁅A, ⁅B, ⁅B, A⁆⁆⁆⁆
  | 2 => ⁅A, ⁅B, ⁅A, ⁅B, A⁆⁆⁆⁆
  | 3 => ⁅A, ⁅B, ⁅B, ⁅B, A⁆⁆⁆⁆
  | 4 => ⁅B, ⁅A, ⁅A, ⁅B, A⁆⁆⁆⁆
  | 5 => ⁅B, ⁅A, ⁅B, ⁅B, A⁆⁆⁆⁆
  | 6 => ⁅B, ⁅B, ⁅A, ⁅B, A⁆⁆⁆⁆
  | _ => ⁅B, ⁅B, ⁅B, ⁅B, A⁆⁆⁆⁆

/-- The first commutator in the binary quintic family. The evaluation lemmas normalize
literal indices to bracket expressions while leaving symbolic indices unchanged. -/
@[simp] lemma binaryQuinticCommutator_zero (A B : 𝔸) :
    binaryQuinticCommutator A B 0 = ⁅A, ⁅A, ⁅A, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma binaryQuinticCommutator_one (A B : 𝔸) :
    binaryQuinticCommutator A B 1 = ⁅A, ⁅A, ⁅B, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma binaryQuinticCommutator_two (A B : 𝔸) :
    binaryQuinticCommutator A B 2 = ⁅A, ⁅B, ⁅A, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma binaryQuinticCommutator_three (A B : 𝔸) :
    binaryQuinticCommutator A B 3 = ⁅A, ⁅B, ⁅B, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma binaryQuinticCommutator_four (A B : 𝔸) :
    binaryQuinticCommutator A B 4 = ⁅B, ⁅A, ⁅A, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma binaryQuinticCommutator_five (A B : 𝔸) :
    binaryQuinticCommutator A B 5 = ⁅B, ⁅A, ⁅B, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma binaryQuinticCommutator_six (A B : 𝔸) :
    binaryQuinticCommutator A B 6 = ⁅B, ⁅B, ⁅A, ⁅B, A⁆⁆⁆⁆ := rfl
@[simp] lemma binaryQuinticCommutator_seven (A B : 𝔸) :
    binaryQuinticCommutator A B 7 = ⁅B, ⁅B, ⁅B, ⁅B, A⁆⁆⁆⁆ := rfl

end Algebra

end FQFP.BCH
