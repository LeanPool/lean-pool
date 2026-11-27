/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

-- Modified for Lean Pool, including adaptations to its Lean module layout.

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S2N2.C7.Defs

/-! The values of the generated certificate are paired with kernel checks. -/

@[expose] public section

namespace RACert.S2N2.C7

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
private noncomputable def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 1), (2, 2), (3, 2), (6, 1), (7, 1), (8, 4), (9, 4), (10, 8), (11, 8), (14, 4), (15,
    4), (24, 4), (25, 4), (26, 4), (27, 4), (28, 4), (29, 4), (30, 4), (31, 4), (48, 2), (49, 2),
    (50, 4), (51, 4), (54, 2), (55, 2), (56, 4), (57, 4), (58, 8), (59, 8), (62, 4), (63, 4), (120,
    1), (121, 1), (122, 2), (123, 2), (126, 1), (127, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
private noncomputable def ev0 : List ℕ := []

private def checkedCount0 :
    { total : ℕ // P.sumEvE 20 1 qt ow qmFlat seg0 ev0 0 total = true } :=
  ⟨3604496, by decide +kernel⟩

private theorem sumOK0 :
    P.sumEvE 20 1 qt ow qmFlat seg0 ev0 0 3604496 = true := checkedCount0.property

/-- All orbit minima of this file. -/
private noncomputable def seg : List (ℕ × ℕ) := seg0

private theorem segOK : checkSeg 7 perms 0 128 seg = true := by decide +kernel

theorem total : OrbitSeg 7 perms (P.leaf (20 + 1)) 0 128 128 3604496 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    (sumEvE_sum check rows elimOK flatOK sumOK0)
    (by decide +kernel)

end S0

end RACert.S2N2.C7
