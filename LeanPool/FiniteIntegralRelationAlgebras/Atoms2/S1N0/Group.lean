/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Group
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms2.S1N0.C0

/-! Generated certificate (see `certgen`): Burnside count for type (1, 0). -/

@[expose] public section

namespace RACert.S1N0

open RACert

/-- Representatives of the conjugacy classes of the symmetry group. -/
def reps : List (List ℕ) :=
  [[0, 1]]

/-- All elements of the symmetry group, with their class and a conjugator. -/
def elems : List (List ℕ × ℕ × List ℕ) :=
  [([0, 1], 0, [0, 1])]

theorem groupCert : checkGroup 1 0 reps elems = true := by decide +kernel

/-- The number of isomorphism classes of integral relation algebras of type (1, 0). -/
theorem count : Nat.card
  (FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.ofSymmNsymm 1 0) = 2 :=
  card_ofSymmNsymm_of_groupCert' 1 0 2 reps elems [2] groupCert
    (.cons C0.count (.nil))
    (by decide +kernel)

end RACert.S1N0
