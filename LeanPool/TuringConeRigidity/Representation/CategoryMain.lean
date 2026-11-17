/-
Copyright (c) 2026 OpenAI. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: OpenAI
-/

/-
Adapted for Lean Pool from bjoernkjoshanssen/tt-
auto/OAI/Computability/DegreeRigidity/Representation/CategoryMain.lean.
Module paths, interfaces, and proofs are ported to the pool's toolchain and gates.
Inherited from OpenAI's Apache-2.0 DegreeRigidity development, with upstream port repairs.
-/

module

public import LeanPool.TuringConeRigidity.Representation.Reduction
public import LeanPool.TuringConeRigidity.Representation.CategoryAvoidance

/-!
# Category Main
-/


@[expose] public section

namespace OAI

namespace TuringRigidity

theorem inverse_le_realDegree_of_representation (hrep : BorelRepresentation)
    (π : Degree ≃o Degree) (t : ℝ) (ht : Irrational t) (ht0 : 0 < t) (ht1 : t < 1) :
    π.symm (realDegree t) ≤ realDegree t :=
  inverse_le_realDegree_of_obligations hrep cut_arithmetic four_value_recovery
    CategorySearch.category_avoidance π t ht ht0 ht1

theorem main_of_two_obligations (hrep : BorelRepresentation)
    (hcover : IrrationalDegreeCoverage) : MainTheorem :=
  main_of_three_obligations hrep hcover CategorySearch.category_avoidance

end TuringRigidity

end OAI
