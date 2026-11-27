/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.Symm1Nsymm2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.Symm3Nsymm1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.Symm5Nsymm0

/-! Combine the counts by symmetry type for relation algebras with 6 atoms. -/

public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofAtoms_six : Nat.card (ofAtoms 6) = 4886349 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm, Finset.sum_range_succ] using
    congr($(card_ofSymmNsymm_five_zero) + $(card_ofSymmNsymm_three_one) +
      $(card_ofSymmNsymm_one_two))

end FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass
