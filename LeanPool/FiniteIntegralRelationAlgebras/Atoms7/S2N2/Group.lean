/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Group
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C3
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C4
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C5
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C6
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C7
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C8
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C9

/-! Generated certificate (see `certgen`): Burnside count for type (2, 2). -/

@[expose] public section

namespace RACert.S2N2

open RACert

/-- Representatives of the conjugacy classes of the symmetry group. -/
def reps : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 6, 5], [0, 1, 2, 4, 3, 6, 5], [0, 1, 2, 5, 6, 3, 4], [0,
    1, 2, 5, 6, 4, 3], [0, 2, 1, 3, 4, 5, 6], [0, 2, 1, 3, 4, 6, 5], [0, 2, 1, 4, 3, 6, 5], [0, 2,
    1, 5, 6, 3, 4], [0, 2, 1, 5, 6, 4, 3]]

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
   ([0, 2, 1, 3, 4, 5, 6], 5, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 2, 1, 3, 4, 6, 5], 6, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 2, 1, 4, 3, 5, 6], 6, [0, 1, 2, 5, 6, 3, 4]),
   ([0, 2, 1, 4, 3, 6, 5], 7, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 2, 1, 5, 6, 3, 4], 8, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 2, 1, 5, 6, 4, 3], 9, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 2, 1, 6, 5, 3, 4], 9, [0, 1, 2, 3, 4, 6, 5]),
   ([0, 2, 1, 6, 5, 4, 3], 8, [0, 1, 2, 3, 4, 6, 5])]

theorem groupCert : checkGroup 2 2 reps elems = true := by decide +kernel

/-- The number of isomorphism classes of integral relation algebras of type (2, 2). -/
theorem count : Nat.card
  (FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.ofSymmNsymm 2 2) =
  2186435732 :=
  card_ofSymmNsymm_of_groupCert' 2 2 2186435732 reps elems [34608025790, 129381732, 105880110,
    1301168, 26170, 1296088, 1315498, 3604496, 51034, 7012] groupCert
    (.cons C0.count (.cons C1.count (.cons C2.count (.cons C3.count (.cons C4.count (.cons C5.count
      (.cons C6.count (.cons C7.count (.cons C8.count (.cons C9.count (.nil)))))))))))
    (by decide +kernel)

end RACert.S2N2
