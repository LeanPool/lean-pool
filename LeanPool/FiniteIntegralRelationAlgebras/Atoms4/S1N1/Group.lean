/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Cert.Group
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms4.S1N1.C0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms4.S1N1.C1

/-! Generated certificate (see `certgen`): Burnside count for type (1, 1). -/

@[expose] public section

namespace RACert.S1N1

open RACert

/-- Representatives of the conjugacy classes of the symmetry group. -/
def reps : List (List ℕ) :=
  [[0, 1, 2, 3], [0, 1, 3, 2]]

/-- All elements of the symmetry group, with their class and a conjugator. -/
def elems : List (List ℕ × ℕ × List ℕ) :=
  [([0, 1, 2, 3], 0, [0, 1, 2, 3]),
   ([0, 1, 3, 2], 1, [0, 1, 2, 3])]

theorem groupCert : checkGroup 1 1 reps elems = true := by decide +kernel

/-- The number of isomorphism classes of integral relation algebras of type (1, 1). -/
theorem count : Nat.card
  (FiniteIntegralRelationAlgebras.RelationAlgebra.IntegralAtom.IsoClass.ofSymmNsymm 1 1) = 37 :=
  card_ofSymmNsymm_of_groupCert' 1 1 37 reps elems [42, 32] groupCert
    (.cons C0.count (.cons C1.count (.nil)))
    (by decide +kernel)

end RACert.S1N1
