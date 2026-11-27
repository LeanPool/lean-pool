/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.Defs
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S0
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S1
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S2
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S3
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S4
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S5
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S6
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S7
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S8
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S9
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S10
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S11
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S12
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S13
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S14
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S15
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S16
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S17
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S18
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S19
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S20
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S21
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S22
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S23
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S24
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S25
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S26
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S27
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S28
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S29
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S30
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S31
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S32
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S33
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S34
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S35
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S36
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S37
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S38
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S39
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S40
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S41
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S42
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S43
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S44
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S45
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S46
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S47
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S48
public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C0.S49

/-! Generated certificate (see `certgen`): symmetry class 0 of type (2, 2). -/

@[expose] public section

namespace RACert.S2N2.C0

open RACert RACert.Problem

theorem total : OrbitSeg 22 perms (P.leaf (20 + 2)) 0 4194304 4194304 34608025790 :=
  OrbitSeg.cast ((S0.total).append ((S1.total).append ((S2.total).append ((S3.total).append
    ((S4.total).append ((S5.total).append ((S6.total).append ((S7.total).append ((S8.total).append
    ((S9.total).append ((S10.total).append ((S11.total).append ((S12.total).append
    ((S13.total).append ((S14.total).append ((S15.total).append ((S16.total).append
    ((S17.total).append ((S18.total).append ((S19.total).append ((S20.total).append
    ((S21.total).append ((S22.total).append ((S23.total).append ((S24.total).append
    ((S25.total).append ((S26.total).append ((S27.total).append ((S28.total).append
    ((S29.total).append ((S30.total).append ((S31.total).append ((S32.total).append
    ((S33.total).append ((S34.total).append ((S35.total).append ((S36.total).append
    ((S37.total).append ((S38.total).append ((S39.total).append ((S40.total).append
    ((S41.total).append ((S42.total).append ((S43.total).append ((S44.total).append
    ((S45.total).append ((S46.total).append ((S47.total).append ((S48.total).append
    (S49.total))))))))))))))))))))))))))))))))))))))))))))))))))
    (by decide +kernel) (by decide +kernel)

/-- The number of lawful cycle sets invariant under the symmetry of this class. -/
theorem count : fixCountL 2 2 [0, 1, 2, 3, 4, 5, 6] = 34608025790 :=
  fixCountL_of_orbits (P := P) check rows (by decide +kernel) (by decide +kernel) (by
    decide +kernel)
    symsOK grpOK total

end RACert.S2N2.C0
