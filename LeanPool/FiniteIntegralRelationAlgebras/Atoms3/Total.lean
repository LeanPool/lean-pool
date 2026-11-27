/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms3.Symm0Nsymm1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms3.Symm2Nsymm0

/-! Combine the counts by symmetry type for relation algebras with 3 atoms. -/

public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofAtoms_three : Nat.card (ofAtoms 3) = 10 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(card_ofSymmNsymm_two_zero) + $(card_ofSymmNsymm_zero_one))

end FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass
