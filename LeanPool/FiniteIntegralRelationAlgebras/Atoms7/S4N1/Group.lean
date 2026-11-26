/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Group
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C3
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C4
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C5
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C6
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C7
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C8
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S4N1.C9

/-! Generated certificate (see `certgen`): Burnside count for type (4, 1). -/

@[expose] public section

namespace RACert.S4N1

open RACert

/-- Representatives of the conjugacy classes of the symmetry group. -/
def reps : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5, 6], [0, 1, 2, 3, 4, 6, 5], [0, 1, 2, 4, 3, 5, 6], [0, 1, 2, 4, 3, 6, 5], [0,
    1, 3, 4, 2, 5, 6], [0, 1, 3, 4, 2, 6, 5], [0, 2, 1, 4, 3, 5, 6], [0, 2, 1, 4, 3, 6, 5], [0, 2,
    3, 4, 1, 5, 6], [0, 2, 3, 4, 1, 6, 5]]

/-- All elements of the symmetry group, with their class and a conjugator. -/
def elems : List (List ℕ × ℕ × List ℕ) :=
  [([0, 1, 2, 3, 4, 5, 6], 0, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 1, 2, 3, 4, 6, 5], 1, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 1, 2, 4, 3, 5, 6], 2, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 1, 2, 4, 3, 6, 5], 3, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 1, 3, 2, 4, 5, 6], 2, [0, 1, 4, 2, 3, 5, 6]),
   ([0, 1, 3, 2, 4, 6, 5], 3, [0, 1, 4, 2, 3, 5, 6]),
   ([0, 1, 3, 4, 2, 5, 6], 4, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 1, 3, 4, 2, 6, 5], 5, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 1, 4, 2, 3, 5, 6], 4, [0, 1, 2, 4, 3, 5, 6]),
   ([0, 1, 4, 2, 3, 6, 5], 5, [0, 1, 2, 4, 3, 5, 6]),
   ([0, 1, 4, 3, 2, 5, 6], 2, [0, 1, 3, 2, 4, 5, 6]),
   ([0, 1, 4, 3, 2, 6, 5], 3, [0, 1, 3, 2, 4, 5, 6]),
   ([0, 2, 1, 3, 4, 5, 6], 2, [0, 3, 4, 1, 2, 5, 6]),
   ([0, 2, 1, 3, 4, 6, 5], 3, [0, 3, 4, 1, 2, 5, 6]),
   ([0, 2, 1, 4, 3, 5, 6], 6, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 2, 1, 4, 3, 6, 5], 7, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 2, 3, 1, 4, 5, 6], 4, [0, 4, 1, 2, 3, 5, 6]),
   ([0, 2, 3, 1, 4, 6, 5], 5, [0, 4, 1, 2, 3, 5, 6]),
   ([0, 2, 3, 4, 1, 5, 6], 8, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 2, 3, 4, 1, 6, 5], 9, [0, 1, 2, 3, 4, 5, 6]),
   ([0, 2, 4, 1, 3, 5, 6], 8, [0, 1, 2, 4, 3, 5, 6]),
   ([0, 2, 4, 1, 3, 6, 5], 9, [0, 1, 2, 4, 3, 5, 6]),
   ([0, 2, 4, 3, 1, 5, 6], 4, [0, 3, 1, 2, 4, 5, 6]),
   ([0, 2, 4, 3, 1, 6, 5], 5, [0, 3, 1, 2, 4, 5, 6]),
   ([0, 3, 1, 2, 4, 5, 6], 4, [0, 4, 1, 3, 2, 5, 6]),
   ([0, 3, 1, 2, 4, 6, 5], 5, [0, 4, 1, 3, 2, 5, 6]),
   ([0, 3, 1, 4, 2, 5, 6], 8, [0, 1, 3, 4, 2, 5, 6]),
   ([0, 3, 1, 4, 2, 6, 5], 9, [0, 1, 3, 4, 2, 5, 6]),
   ([0, 3, 2, 1, 4, 5, 6], 2, [0, 2, 4, 1, 3, 5, 6]),
   ([0, 3, 2, 1, 4, 6, 5], 3, [0, 2, 4, 1, 3, 5, 6]),
   ([0, 3, 2, 4, 1, 5, 6], 4, [0, 2, 1, 3, 4, 5, 6]),
   ([0, 3, 2, 4, 1, 6, 5], 5, [0, 2, 1, 3, 4, 5, 6]),
   ([0, 3, 4, 1, 2, 5, 6], 6, [0, 1, 3, 2, 4, 5, 6]),
   ([0, 3, 4, 1, 2, 6, 5], 7, [0, 1, 3, 2, 4, 5, 6]),
   ([0, 3, 4, 2, 1, 5, 6], 8, [0, 1, 3, 2, 4, 5, 6]),
   ([0, 3, 4, 2, 1, 6, 5], 9, [0, 1, 3, 2, 4, 5, 6]),
   ([0, 4, 1, 2, 3, 5, 6], 8, [0, 1, 4, 3, 2, 5, 6]),
   ([0, 4, 1, 2, 3, 6, 5], 9, [0, 1, 4, 3, 2, 5, 6]),
   ([0, 4, 1, 3, 2, 5, 6], 4, [0, 3, 1, 4, 2, 5, 6]),
   ([0, 4, 1, 3, 2, 6, 5], 5, [0, 3, 1, 4, 2, 5, 6]),
   ([0, 4, 2, 1, 3, 5, 6], 4, [0, 2, 1, 4, 3, 5, 6]),
   ([0, 4, 2, 1, 3, 6, 5], 5, [0, 2, 1, 4, 3, 5, 6]),
   ([0, 4, 2, 3, 1, 5, 6], 2, [0, 2, 3, 1, 4, 5, 6]),
   ([0, 4, 2, 3, 1, 6, 5], 3, [0, 2, 3, 1, 4, 5, 6]),
   ([0, 4, 3, 1, 2, 5, 6], 8, [0, 1, 4, 2, 3, 5, 6]),
   ([0, 4, 3, 1, 2, 6, 5], 9, [0, 1, 4, 2, 3, 5, 6]),
   ([0, 4, 3, 2, 1, 5, 6], 6, [0, 1, 4, 2, 3, 5, 6]),
   ([0, 4, 3, 2, 1, 6, 5], 7, [0, 1, 4, 2, 3, 5, 6])]

theorem groupCert : checkGroup 4 1 reps elems = true := by decide +kernel

/-- The number of isomorphism classes of integral relation algebras of type (4, 1). -/
theorem count : Nat.card
  (FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.ofSymmNsymm 4 1) =
  50265788140 :=
  card_ofSymmNsymm_of_groupCert' 4 1 50265788140 reps elems [2400445740454, 11002581304, 124588184,
    91277262, 161275, 27451, 761050, 3501868, 1486, 1468] groupCert
    (.cons C0.count (.cons C1.count (.cons C2.count (.cons C3.count (.cons C4.count (.cons C5.count
      (.cons C6.count (.cons C7.count (.cons C8.count (.cons C9.count (.nil)))))))))))
    (by decide +kernel)

end RACert.S4N1
