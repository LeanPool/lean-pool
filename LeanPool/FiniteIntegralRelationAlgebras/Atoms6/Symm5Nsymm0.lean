/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Foundations.RelationAlgebra.IntegralAtomStructure
import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S5N0.Group

/-! Count the isomorphism classes with the specified symmetric and nonsymmetric atoms. -/

public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_five_zero : Nat.card (ofSymmNsymm 5 0) = 3849920 :=
  RACert.S5N0.count

end FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass
