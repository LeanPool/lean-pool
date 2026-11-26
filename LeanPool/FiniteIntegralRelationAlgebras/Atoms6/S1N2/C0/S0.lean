/-
Copyright (c) 2026 Chris Henson. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Chris Henson
-/

module

public import LeanPool.FiniteIntegralRelationAlgebras.Atoms6.S1N2.C0.Defs

/-! Generated certificate segment; see `certgen`. -/

@[expose] public section

namespace RACert.S1N2.C0

open RACert RACert.Problem

namespace S0

/-- Orbit minima `(α, orbit size)`, part 0. -/
def seg0 : List (ℕ × ℕ) :=
  [(0, 1), (1, 4), (3, 2), (5, 4), (7, 4), (15, 1)]

/-- Evidence: `i + 1` for a leaf killed by the `i`-th quadruple of `qmFlat`, `0` (or nothing) for an
evaluated leaf. -/
def ev0 : List ℕ := []

theorem sumOK0 : P.sumEvE 20 1 qt ow qmFlat seg0 ev0 0 312508 = true := by decide +kernel

/-- All orbit minima of this file. -/
def seg : List (ℕ × ℕ) := seg0

theorem segOK : checkSeg 4 perms 0 16 seg = true := by decide +kernel

theorem total : OrbitSeg 4 perms (P.leaf (20 + 1)) 0 16 16 312508 :=
  OrbitSeg.of_checkSum segOK (by decide +kernel)
    (sumEvE_sum check rows elimOK flatOK sumOK0)
    (by decide +kernel)

end S0

end RACert.S1N2.C0
