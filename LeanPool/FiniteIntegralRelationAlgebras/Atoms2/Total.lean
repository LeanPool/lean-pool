/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms2.Symm1Nsymm0

/-! Combine the counts by symmetry type for relation algebras with 2 atoms. -/

public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofAtoms_two : Nat.card (ofAtoms 2) = 2 := by
  simpa [card_ofAtoms_succ_eq_sum_ofSymmNsymm] using card_ofSymmNsymm_one_zero

end FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass
