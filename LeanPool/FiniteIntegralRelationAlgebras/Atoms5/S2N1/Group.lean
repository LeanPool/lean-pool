/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Group
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.S2N1.C0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.S2N1.C1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.S2N1.C2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.S2N1.C3

/-! Generated certificate (see `certgen`): Burnside count for type (2, 1). -/

@[expose] public section

namespace RACert.S2N1

open RACert

/-- Representatives of the conjugacy classes of the symmetry group. -/
def reps : List (List ℕ) :=
  [[0, 1, 2, 3, 4], [0, 1, 2, 4, 3], [0, 2, 1, 3, 4], [0, 2, 1, 4, 3]]

/-- All elements of the symmetry group, with their class and a conjugator. -/
def elems : List (List ℕ × ℕ × List ℕ) :=
  [([0, 1, 2, 3, 4], 0, [0, 1, 2, 3, 4]),
   ([0, 1, 2, 4, 3], 1, [0, 1, 2, 3, 4]),
   ([0, 2, 1, 3, 4], 2, [0, 1, 2, 3, 4]),
   ([0, 2, 1, 4, 3], 3, [0, 1, 2, 3, 4])]

theorem groupCert : checkGroup 2 1 reps elems = true := by decide +kernel

/-- The number of isomorphism classes of integral relation algebras of type (2, 1). -/
theorem count : Nat.card
  (FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.ofSymmNsymm 2 1) = 1316 :=
  card_ofSymmNsymm_of_groupCert' 2 1 1316 reps elems [3720, 1318, 92, 134] groupCert
    (.cons C0.count (.cons C1.count (.cons C2.count (.cons C3.count (.nil)))))
    (by decide +kernel)

end RACert.S2N1
