/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Group
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms4.S3N0.C0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms4.S3N0.C1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms4.S3N0.C2

/-! Generated certificate (see `certgen`): Burnside count for type (3, 0). -/

@[expose] public section

namespace RACert.S3N0

open RACert

/-- Representatives of the conjugacy classes of the symmetry group. -/
def reps : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 1, 3, 2], [0, 2, 3, 1]]

/-- All elements of the symmetry group, with their class and a conjugator. -/
def elems : List (List ℕ × ℕ × List ℕ) :=
  [([0, 1, 2, 3], 0, [0, 1, 2, 3]),
   ([0, 1, 3, 2], 1, [0, 1, 2, 3]),
   ([0, 2, 1, 3], 1, [0, 3, 1, 2]),
   ([0, 2, 3, 1], 2, [0, 1, 2, 3]),
   ([0, 3, 1, 2], 2, [0, 1, 3, 2]),
   ([0, 3, 2, 1], 1, [0, 2, 1, 3])]

theorem groupCert : checkGroup 3 0 reps elems = true := by decide +kernel

/-- The number of isomorphism classes of integral relation algebras of type (3, 0). -/
theorem count : Nat.card
  (FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.ofSymmNsymm 3 0) = 65 :=
  card_ofSymmNsymm_of_groupCert' 3 0 65 reps elems [294, 26, 9] groupCert
    (.cons C0.count (.cons C1.count (.cons C2.count (.nil))))
    (by decide +kernel)

end RACert.S3N0
