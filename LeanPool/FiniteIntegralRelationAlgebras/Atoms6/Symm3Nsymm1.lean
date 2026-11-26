/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Foundations.RelationAlgebra.IntegralAtomStructure
import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S3N1.Group

/-! Count the isomorphism classes with the specified symmetric and nonsymmetric atoms. -/

public section

namespace FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass

theorem card_ofSymmNsymm_three_one : Nat.card (ofSymmNsymm 3 1) = 988464 :=
  RACert.S3N1.count

end FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass
