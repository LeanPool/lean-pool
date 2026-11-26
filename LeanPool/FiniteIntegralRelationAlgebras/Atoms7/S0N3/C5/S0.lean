/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C5.Defs

/-! The values of the generated certificate are paired with kernel checks. -/

@[expose] public section

namespace RACert.S0N3.C5

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 3), (3, 3), (7, 1), (8, 4), (9, 12), (11, 12), (15, 4), (24, 6), (25, 12), (27, 6),
    (28, 6), (29, 12), (31, 6), (56, 4), (57, 12), (59, 12), (63, 4), (120, 1), (121, 3), (123, 3),
    (127, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := []

private def checkedCount0 :
    { total : ℕ // P.sumEvE 21 0 qt ow qmFlat seg0 ev0 0 total = true } :=
  ⟨4287373, by decide +kernel⟩

theorem sumOK0 :
    P.sumEvE 21 0 qt ow qmFlat seg0 ev0 0 4287373 = true := checkedCount0.property

/-- All orbit minima of this file. -/
def seg : List (ℕ × ℕ) := seg0

theorem segOK : checkSeg 7 perms 0 128 seg = true := by decide +kernel

theorem total : OrbitSeg 7 perms (P.leaf (21 + 0)) 0 128 128 4287373 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    (sumEvE_sum check rows elimOK flatOK sumOK0)
    (by decide +kernel)

end S0

end RACert.S0N3.C5
