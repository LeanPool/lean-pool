/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S0N3.C1.Defs

/-! The values of the generated certificate are paired with kernel checks. -/

@[expose] public section

namespace RACert.S0N3.C1

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 4), (3, 2), (5, 4), (7, 4), (15, 1), (16, 4), (17, 8), (18, 8), (19, 8), (21, 8),
    (22, 4), (23, 8), (25, 4), (27, 8), (31, 4), (48, 4), (49, 4), (50, 4), (51, 4), (52, 8), (53,
    8), (54, 8), (55, 8), (60, 4), (61, 4), (62, 4), (63, 4), (96, 2), (97, 8), (99, 4), (101, 4),
    (102, 4), (103, 8), (111, 2), (112, 4), (113, 8), (114, 8), (115, 8), (117, 8), (118, 4), (119,
    8), (121, 4), (123, 8), (127, 4), (240, 1), (241, 4), (243, 2), (245, 4), (247, 4), (255, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := [0, 0, 0, 0, 0, 0, 68, 0, 68, 0, 0, 68, 0, 0, 0, 0, 68, 0, 68, 0, 68, 0, 68, 0,
  0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 68, 0, 68, 0, 0, 68]

private def checkedCount0 :
    { total : ℕ // P.sumEvE 19 1 qt ow qmFlat seg0 ev0 0 total = true } :=
  ⟨1363629, by decide +kernel⟩

theorem sumOK0 :
    P.sumEvE 19 1 qt ow qmFlat seg0 ev0 0 1363629 = true := checkedCount0.property

/-- All orbit minima of this file. -/
def seg : List (ℕ × ℕ) := seg0

theorem segOK : checkSeg 8 perms 0 256 seg = true := by decide +kernel

theorem total : OrbitSeg 8 perms (P.leaf (19 + 1)) 0 256 256 1363629 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    (sumEvE_sum check rows elimOK flatOK sumOK0)
    (by decide +kernel)

end S0

end RACert.S0N3.C1
