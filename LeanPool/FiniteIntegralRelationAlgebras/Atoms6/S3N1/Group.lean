/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Group
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S3N1.C0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S3N1.C1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S3N1.C2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S3N1.C3
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S3N1.C4
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S3N1.C5

/-! Generated certificate (see `certgen`): Burnside count for type (3, 1). -/

@[expose] public section

namespace RACert.S3N1

open RACert

/-- Representatives of the conjugacy classes of the symmetry group. -/
def reps : List (List ℕ) :=
  [[0, 1, 2, 3, 4, 5], [0, 1, 2, 3, 5, 4], [0, 1, 3, 2, 4, 5], [0, 1, 3, 2, 5, 4], [0, 2, 3, 1, 4,
    5], [0, 2, 3, 1, 5, 4]]

/-- All elements of the symmetry group, with their class and a conjugator. -/
def elems : List (List ℕ × ℕ × List ℕ) :=
  [([0, 1, 2, 3, 4, 5], 0, [0, 1, 2, 3, 4, 5]),
   ([0, 1, 2, 3, 5, 4], 1, [0, 1, 2, 3, 4, 5]),
   ([0, 1, 3, 2, 4, 5], 2, [0, 1, 2, 3, 4, 5]),
   ([0, 1, 3, 2, 5, 4], 3, [0, 1, 2, 3, 4, 5]),
   ([0, 2, 1, 3, 4, 5], 2, [0, 3, 1, 2, 4, 5]),
   ([0, 2, 1, 3, 5, 4], 3, [0, 3, 1, 2, 4, 5]),
   ([0, 2, 3, 1, 4, 5], 4, [0, 1, 2, 3, 4, 5]),
   ([0, 2, 3, 1, 5, 4], 5, [0, 1, 2, 3, 4, 5]),
   ([0, 3, 1, 2, 4, 5], 4, [0, 1, 3, 2, 4, 5]),
   ([0, 3, 1, 2, 5, 4], 5, [0, 1, 3, 2, 4, 5]),
   ([0, 3, 2, 1, 4, 5], 2, [0, 2, 1, 3, 4, 5]),
   ([0, 3, 2, 1, 5, 4], 3, [0, 2, 1, 3, 4, 5])]

theorem groupCert : checkGroup 3 1 reps elems = true := by decide +kernel

/-- The number of isomorphism classes of integral relation algebras of type (3, 1). -/
theorem count : Nat.card
  (FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.ofSymmNsymm 3 1) = 988464 :=
  card_ofSymmNsymm_of_groupCert' 3 1 988464 reps elems [11044515, 680611, 17413, 27433, 645, 307]
    groupCert
    (.cons C0.count (.cons C1.count (.cons C2.count (.cons C3.count (.cons C4.count (.cons C5.count
      (.nil)))))))
    (by decide +kernel)

end RACert.S3N1
