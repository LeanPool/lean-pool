/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S5N0.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

@[expose] public section

namespace RACert.S5N0.C0

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 10), (3, 30), (7, 10), (11, 20), (12, 15), (13, 60), (15, 60), (30, 15), (31, 30),
    (63, 5), (75, 5), (76, 30), (77, 60), (79, 30), (86, 60), (87, 60), (94, 60), (95, 60), (116,
    10), (117, 60), (119, 60), (127, 20), (222, 10), (223, 10), (235, 15), (236, 12), (237, 60),
    (239, 60), (254, 30), (255, 30), (507, 15), (511, 10), (1023, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := [0, 0, 0, 0, 0, 12, 12, 12, 12, 12]

theorem sumOK0 : P.sumEvE 20 5 qt ow qmFlat seg0 ev0 0 454897503 = true := by decide +kernel

/-- All orbit minima of this file. -/
def seg : List (ℕ × ℕ) := seg0

theorem segOK : checkSeg 10 perms 0 1024 seg = true := by decide +kernel

theorem total : OrbitSeg 10 perms (P.leaf (20 + 5)) 0 1024 1024 454897503 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    (sumEvE_sum check rows elimOK flatOK sumOK0)
    (by decide +kernel)

end S0

end RACert.S5N0.C0
