/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Group
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.S0N2.C0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.S0N2.C1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.S0N2.C2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.S0N2.C3
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms5.S0N2.C4

/-! Generated certificate (see `certgen`): Burnside count for type (0, 2). -/

@[expose] public section

namespace RACert.S0N2

open RACert

/-- Representatives of the conjugacy classes of the symmetry group. -/
def reps : List (List ℕ) :=
  [[0, 1, 2, 3, 4], [0, 1, 2, 4, 3], [0, 2, 1, 4, 3], [0, 3, 4, 1, 2], [0, 3, 4, 2, 1]]

/-- All elements of the symmetry group, with their class and a conjugator. -/
def elems : List (List ℕ × ℕ × List ℕ) :=
  [([0, 1, 2, 3, 4], 0, [0, 1, 2, 3, 4]),
   ([0, 1, 2, 4, 3], 1, [0, 1, 2, 3, 4]),
   ([0, 2, 1, 3, 4], 1, [0, 3, 4, 1, 2]),
   ([0, 2, 1, 4, 3], 2, [0, 1, 2, 3, 4]),
   ([0, 3, 4, 1, 2], 3, [0, 1, 2, 3, 4]),
   ([0, 3, 4, 2, 1], 4, [0, 1, 2, 3, 4]),
   ([0, 4, 3, 1, 2], 4, [0, 1, 2, 4, 3]),
   ([0, 4, 3, 2, 1], 3, [0, 1, 2, 4, 3])]

theorem groupCert : checkGroup 0 2 reps elems = true := by decide +kernel

/-- The number of isomorphism classes of integral relation algebras of type (0, 2). -/
theorem count : Nat.card
  (FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.ofSymmNsymm 0 2) = 83 :=
  card_ofSymmNsymm_of_groupCert' 0 2 83 reps elems [241, 103, 177, 7, 13] groupCert
    (.cons C0.count (.cons C1.count (.cons C2.count (.cons C3.count (.cons C4.count (.nil))))))
    (by decide +kernel)

end RACert.S0N2
