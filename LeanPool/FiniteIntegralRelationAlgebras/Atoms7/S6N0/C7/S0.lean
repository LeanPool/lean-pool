/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C7.Defs

/-! The values of the generated certificate are paired with kernel checks. -/

@[expose] public section

namespace RACert.S6N0.C7

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 6), (3, 3), (5, 3), (6, 6), (7, 6), (12, 3), (13, 6), (15, 3), (19, 6), (23, 3), (25,
    2), (27, 6), (30, 3), (31, 6), (63, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := []

private def checkedCount0 :
    { total : ℕ // P.sumEvE 19 3 qt ow qmFlat seg0 ev0 0 total = true } :=
  ⟨4202168, by decide +kernel⟩

theorem sumOK0 :
    P.sumEvE 19 3 qt ow qmFlat seg0 ev0 0 4202168 = true := checkedCount0.property

/-- All orbit minima of this file. -/
def seg : List (ℕ × ℕ) := seg0

theorem segOK : checkSeg 6 perms 0 64 seg = true := by decide +kernel

theorem total : OrbitSeg 6 perms (P.leaf (19 + 3)) 0 64 64 4202168 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    (sumEvE_sum check rows elimOK flatOK sumOK0)
    (by decide +kernel)

end S0

end RACert.S6N0.C7
