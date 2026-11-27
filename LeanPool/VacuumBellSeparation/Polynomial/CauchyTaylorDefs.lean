/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import LeanPool.VacuumBellSeparation.Gaussian.PolydiscCoefficientDefs
public import Mathlib.Data.Fintype.Pi

/-! # Taylor polynomials on polydiscs -/

@[expose] public section

namespace VacuumBellSeparation

open scoped BigOperators
open Gaussian

/-- All multiindices of total degree strictly less than N, including the
empty index precisely when N is positive. -/
def multiIndexBelow (d N : ℕ) : Finset (Fin d → ℕ) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.range N)).filter (fun k => ∑ j, k j < N)

/-- The actual Taylor polynomial, evaluated at x. -/
noncomputable def cauchyTaylor (d N : ℕ) (R : ℝ)
    (F : (Fin d → ℂ) → ℂ) (x : Fin d → ℂ) : ℂ :=
  ∑ k ∈ multiIndexBelow d N, polydiscCoefficient d R F k * ∏ j, x j ^ k j

end VacuumBellSeparation
