/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Foundations.RelationAlgebra.IntegralAtomStructure
import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S1N2.Group

/-! Count the isomorphism classes with the specified symmetric and nonsymmetric atoms. -/

public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_one_two : Nat.card (ofSymmNsymm 1 2) = 47965 :=
  RACert.S1N2.count

end FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass
