/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Foundations.RelationAlgebra.IntegralAtomStructure
import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.S2N1.Group

/-! Count the isomorphism classes with the specified symmetric and nonsymmetric atoms. -/

public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_two_one : Nat.card (ofSymmNsymm 2 1) = 1316 :=
  RACert.S2N1.count

end FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass
