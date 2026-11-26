/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C3.Defs

/-! The values of the generated certificate are paired with kernel checks. -/

@[expose] public section

namespace RACert.S2N2.C3

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 4), (3, 2), (5, 2), (6, 2), (7, 4), (15, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := []

private def checkedCount0 :
    { total : ℕ // P.sumEvE 20 2 qt ow qmFlat seg0 ev0 0 total = true } :=
  ⟨1301168, by decide +kernel⟩

theorem sumOK0 :
    P.sumEvE 20 2 qt ow qmFlat seg0 ev0 0 1301168 = true := checkedCount0.property

/-- All orbit minima of this file. -/
def seg : List (ℕ × ℕ) := seg0

theorem segOK : checkSeg 4 perms 0 16 seg = true := by decide +kernel

theorem total : OrbitSeg 4 perms (P.leaf (20 + 2)) 0 16 16 1301168 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    (sumEvE_sum check rows elimOK flatOK sumOK0)
    (by decide +kernel)

end S0

end RACert.S2N2.C3
