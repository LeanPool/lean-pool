/-
Copyright (c) 2026 George Lee. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: George Lee
-/

/- Modified for Lean Pool: module exports, namespaces, and Lean 4.35 compatibility. -/

module

public import LeanPool.MultiplicativeErgodic.Birkhoff.Ergodic

/-!
# Birkhoff convergence and maximal estimates

This module retains the upstream maximal ergodic theorem, weak-type inequality,
coboundary convergence, density transfer and independent Hilbert-space proof of `L²`
convergence. The general `L¹` endpoint reuses
`LeanPool.PointwiseBirkhoff.birkhoffErgodicTheorem` through a short adapter, avoiding a
second truncation proof. Its dependency graph contains no Kingman theorem.

The maximal estimate follows Garsia's direct argument (`∫_{Eₙ} f ≥ 0`), rather than the
integer-shift covering route in the author's write-up. The square-integrable proof uses
orthogonal decomposition into invariant functions and the closure of coboundaries.
The ergodic endpoint then identifies the limit as the integral.

| Module | Reusable results |
|---|---|
| `Maximal` | Maximal ergodic theorem and weak-type inequality |
| `Mean` | Coboundaries, `L²` orbit decay and Hilbert-space input |
| `OscIO` | Oscillation sets and density transfer |
| `Average` | Independent `L²` convergence and the reused `L¹` endpoint |
| `Ergodic` | Identification of the ergodic limit as `∫ f` |
-/
@[expose] public section

namespace MultiplicativeErgodic


end MultiplicativeErgodic
