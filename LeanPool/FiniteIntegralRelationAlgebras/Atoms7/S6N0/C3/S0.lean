/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C3.Defs

/-! The values of the generated certificate are paired with kernel checks. -/

@[expose] public section

namespace RACert.S6N0.C3

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
private noncomputable def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 4), (3, 2), (5, 2), (6, 2), (7, 4), (15, 1), (16, 4), (17, 8), (18, 8), (19, 8), (21,
    4), (22, 8), (23, 8), (26, 4), (27, 8), (31, 4), (48, 2), (49, 8), (51, 4), (53, 4), (54, 4),
    (55, 8), (63, 2), (80, 2), (81, 4), (82, 4), (83, 4), (85, 2), (86, 4), (87, 4), (90, 2), (91,
    4), (95, 2), (96, 2), (97, 8), (99, 4), (101, 4), (102, 4), (103, 8), (111, 2), (112, 4), (113,
    8), (114, 8), (115, 8), (117, 4), (118, 8), (119, 8), (122, 4), (123, 8), (127, 4), (240, 1),
    (241, 4), (243, 2), (245, 2), (246, 2), (247, 4), (255, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
private noncomputable def ev0 : List ℕ :=
  [0, 0, 0, 0, 0, 0, 0, 26, 26, 0, 0, 26, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 26,
  26, 0, 0, 26]

private def checkedCount0 :
    { total : ℕ // P.sumEvE 20 4 qt ow qmFlat seg0 ev0 0 total = true } :=
  ⟨93632936, by decide +kernel⟩

private theorem sumOK0 :
    P.sumEvE 20 4 qt ow qmFlat seg0 ev0 0 93632936 = true := checkedCount0.property

/-- All orbit minima of this file. -/
private noncomputable def seg : List (ℕ × ℕ) := seg0

private theorem segOK : checkSeg 8 perms 0 256 seg = true := by decide +kernel

theorem total : OrbitSeg 8 perms (P.leaf (20 + 4)) 0 256 256 93632936 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    (sumEvE_sum check rows elimOK flatOK sumOK0)
    (by decide +kernel)

end S0

end RACert.S6N0.C3
