/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S3N1.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

@[expose] public section

namespace RACert.S3N1.C0

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 1), (2, 6), (3, 6), (6, 3), (7, 3), (10, 6), (11, 6), (12, 6), (13, 6), (14, 12),
    (15, 12), (30, 3), (31, 3), (42, 2), (43, 2), (44, 6), (45, 6), (46, 6), (47, 6), (54, 6), (55,
    6), (62, 6), (63, 6), (126, 1), (127, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := []

theorem sumOK0 : P.sumEvE 20 3 qt ow qmFlat seg0 ev0 0 11044515 = true := by decide +kernel

/-- All orbit minima of this file. -/
def seg : List (ℕ × ℕ) := seg0

theorem segOK : checkSeg 7 perms 0 128 seg = true := by decide +kernel

theorem total : OrbitSeg 7 perms (P.leaf (20 + 3)) 0 128 128 11044515 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    (sumEvE_sum check rows elimOK flatOK sumOK0)
    (by decide +kernel)

end S0

end RACert.S3N1.C0
