/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Group
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C3
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C4
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C5
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C6
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C7
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C8
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C9

/-! Generated certificate (see `certgen`): Burnside count for type (0, 3). -/

@[expose] public section

namespace RACert.S0N3

open RACert

/-- Representatives of the conjugacy classes of the symmetry group. -/
def reps : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 6, 5], [0, 1, 2, 4, 3, 6, 5], [0, 1, 2, 5, 6, 3, 4], [0,
    1, 2, 5, 6, 4, 3], [0, 2, 1, 4, 3, 6, 5], [0, 2, 1, 5, 6, 3, 4], [0, 2, 1, 5, 6, 4, 3], [0, 3,
    4, 5, 6, 1, 2], [0, 3, 4, 5, 6, 2, 1]]

/-- All elements of the symmetry group, with their class and a conjugator. -/
def elems : List (List ℕ × ℕ × List ℕ) :=
  [([0, 1, 2, 3, 4, 5, 6], 0, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 1, 2, 3, 4, 6, 5], 1, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 1, 2, 4, 3, 5, 6], 1, [0, 1, 2, 5, 6, 3, 4]),
   ([0, 1, 2, 4, 3, 6, 5], 2, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 1, 2, 5, 6, 3, 4], 3, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 1, 2, 5, 6, 4, 3], 4, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 1, 2, 6, 5, 3, 4], 4, [0, 1, 2, 3, 4, 6, 5]),
   ([0, 1, 2, 6, 5, 4, 3], 3, [0, 1, 2, 3, 4, 6, 5]),
   ([0, 2, 1, 3, 4, 5, 6], 1, [0, 3, 4, 5, 6, 1, 2]),
   ([0, 2, 1, 3, 4, 6, 5], 2, [0, 3, 4, 1, 2, 5, 6]),
   ([0, 2, 1, 4, 3, 5, 6], 2, [0, 5, 6, 1, 2, 3, 4]),
   ([0, 2, 1, 4, 3, 6, 5], 5, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 2, 1, 5, 6, 3, 4], 6, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 2, 1, 5, 6, 4, 3], 7, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 2, 1, 6, 5, 3, 4], 7, [0, 1, 2, 3, 4, 6, 5]),
   ([0, 2, 1, 6, 5, 4, 3], 6, [0, 1, 2, 3, 4, 6, 5]),
   ([0, 3, 4, 1, 2, 5, 6], 3, [0, 5, 6, 1, 2, 3, 4]),
   ([0, 3, 4, 1, 2, 6, 5], 6, [0, 5, 6, 1, 2, 3, 4]),
   ([0, 3, 4, 2, 1, 5, 6], 4, [0, 5, 6, 1, 2, 3, 4]),
   ([0, 3, 4, 2, 1, 6, 5], 7, [0, 5, 6, 1, 2, 3, 4]),
   ([0, 3, 4, 5, 6, 1, 2], 8, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 3, 4, 5, 6, 2, 1], 9, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 3, 4, 6, 5, 1, 2], 9, [0, 1, 2, 3, 4, 6, 5]),
   ([0, 3, 4, 6, 5, 2, 1], 8, [0, 1, 2, 3, 4, 6, 5]),
   ([0, 4, 3, 1, 2, 5, 6], 4, [0, 5, 6, 1, 2, 4, 3]),
   ([0, 4, 3, 1, 2, 6, 5], 7, [0, 5, 6, 1, 2, 4, 3]),
   ([0, 4, 3, 2, 1, 5, 6], 3, [0, 5, 6, 1, 2, 4, 3]),
   ([0, 4, 3, 2, 1, 6, 5], 6, [0, 5, 6, 1, 2, 4, 3]),
   ([0, 4, 3, 5, 6, 1, 2], 9, [0, 1, 2, 4, 3, 6, 5]),
   ([0, 4, 3, 5, 6, 2, 1], 8, [0, 1, 2, 4, 3, 6, 5]),
   ([0, 4, 3, 6, 5, 1, 2], 8, [0, 1, 2, 4, 3, 5, 6]),
   ([0, 4, 3, 6, 5, 2, 1], 9, [0, 1, 2, 4, 3, 5, 6]),
   ([0, 5, 6, 1, 2, 3, 4], 8, [0, 1, 2, 5, 6, 3, 4]),
   ([0, 5, 6, 1, 2, 4, 3], 9, [0, 1, 2, 5, 6, 4, 3]),
   ([0, 5, 6, 2, 1, 3, 4], 9, [0, 1, 2, 5, 6, 3, 4]),
   ([0, 5, 6, 2, 1, 4, 3], 8, [0, 1, 2, 5, 6, 4, 3]),
   ([0, 5, 6, 3, 4, 1, 2], 3, [0, 3, 4, 1, 2, 5, 6]),
   ([0, 5, 6, 3, 4, 2, 1], 4, [0, 3, 4, 1, 2, 5, 6]),
   ([0, 5, 6, 4, 3, 1, 2], 6, [0, 3, 4, 1, 2, 5, 6]),
   ([0, 5, 6, 4, 3, 2, 1], 7, [0, 3, 4, 1, 2, 5, 6]),
   ([0, 6, 5, 1, 2, 3, 4], 9, [0, 1, 2, 6, 5, 4, 3]),
   ([0, 6, 5, 1, 2, 4, 3], 8, [0, 1, 2, 6, 5, 3, 4]),
   ([0, 6, 5, 2, 1, 3, 4], 8, [0, 1, 2, 6, 5, 4, 3]),
   ([0, 6, 5, 2, 1, 4, 3], 9, [0, 1, 2, 6, 5, 3, 4]),
   ([0, 6, 5, 3, 4, 1, 2], 4, [0, 3, 4, 1, 2, 6, 5]),
   ([0, 6, 5, 3, 4, 2, 1], 3, [0, 3, 4, 1, 2, 6, 5]),
   ([0, 6, 5, 4, 3, 1, 2], 7, [0, 3, 4, 1, 2, 6, 5]),
   ([0, 6, 5, 4, 3, 2, 1], 6, [0, 3, 4, 1, 2, 6, 5])]

theorem groupCert : checkGroup 0 3 reps elems = true := by decide +kernel

/-- The number of isomorphism classes of integral relation algebras of type (0, 3). -/
theorem count : Nat.card
  (FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.ofSymmNsymm 0 3) = 4492953
  :=
  card_ofSymmNsymm_of_groupCert' 0 3 4492953 reps elems [203664497, 1363629, 1083289, 11481, 1565,
    4287373, 44581, 1557, 1502, 250] groupCert
    (.cons C0.count (.cons C1.count (.cons C2.count (.cons C3.count (.cons C4.count (.cons C5.count
      (.cons C6.count (.cons C7.count (.cons C8.count (.cons C9.count (.nil)))))))))))
    (by decide +kernel)

end RACert.S0N3
