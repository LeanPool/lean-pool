/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms7.S6N0.C2.Defs

/-! The values of the generated certificate are paired with kernel checks. -/

@[expose] public section

namespace RACert.S6N0.C2

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
private noncomputable def seg0 : List (ℕ × ℕ) :=
  [(0, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
private noncomputable def ev0 : List ℕ := []

private def checkedCount0 :
    { total : ℕ // P.sumEvE 22 4 qt ow qmFlat seg0 ev0 0 total = true } :=
  ⟨3216325, by decide +kernel⟩

private theorem sumOK0 :
    P.sumEvE 22 4 qt ow qmFlat seg0 ev0 0 3216325 = true := checkedCount0.property

/-- All orbit minima of this file. -/
private noncomputable def seg : List (ℕ × ℕ) := seg0

private theorem segOK : checkSeg 0 perms 0 1 seg = true := by decide +kernel

theorem total : OrbitSeg 0 perms (P.leaf (22 + 4)) 0 1 1 3216325 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    (sumEvE_sum check rows elimOK flatOK sumOK0)
    (by decide +kernel)

end S0

end RACert.S6N0.C2
