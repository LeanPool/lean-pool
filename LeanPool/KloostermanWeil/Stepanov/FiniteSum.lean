/-
Copyright (c) 2026 Charlie Dorsey (Raccoon Labs). All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Charlie Dorsey
-/
module

public import LeanPool.KloostermanWeil.Carlitz.RecurrencePackage


/-!
Adapted from Charlie Dorsey’s Apache-2.0 Weil Bounds Toolkit for Lean Pool’s
module system, Mathlib version, quality requirements and compilation performance.

# Finite spectral aggregates

Defines the finite sums linking spectral power sums and curve-point data. Reference:
Harcos (2015), equation (3).
-/

@[expose] public section

namespace KloostermanWeil.Stepanov

open scoped BigOperators
open KloostermanWeil.Carlitz

/-- Finite aggregate appearing in the Stepanov point-count argument.
For the specialized curve, this is identified with
`#C_n - p^n` exactly, with no asymptotic notation. -/
noncomputable def errorAggregate
    (p n : ℕ) [Fact p.Prime] (c : ZMod p) : ℂ := by
  classical
  exact -1 +
    ∑ m : {m : ZMod p // m ≠ 0},
      Kseq p (m.1 ^ 2 * c) n


end KloostermanWeil.Stepanov
