/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Complex.CauchyIntegral

/-! # Contour coefficients on polydiscs -/

@[expose] public section

namespace VacuumBellSeparation.Gaussian

open Complex MeasureTheory Set Metric
open scoped BigOperators

/-- Circle coefficient given by `(2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(0, R), z⁻¹ ^ k • z⁻¹ • f z`. -/
noncomputable def circleCoefficient (R : ℝ) (f : ℂ → ℂ) (k : ℕ) : ℂ :=
  (2 * Real.pi * I : ℂ)⁻¹ • ∮ z in C(0, R), z⁻¹ ^ k • z⁻¹ • f z

/-- An actual normalized contour in each of the finitely many coordinates. -/
noncomputable def polydiscCoefficient :
    (n : ℕ) → ℝ → ((Fin n → ℂ) → ℂ) → (Fin n → ℕ) → ℂ
  | 0, _, F, _ => F Fin.elim0
  | n + 1, R, F, k => circleCoefficient R
      (fun z => polydiscCoefficient n R (fun w => F (Fin.cons z w)) (fun j => k j.succ))
      (k 0)

/-- Coordinate closed polydisc with membership specified by `{z | ∀ j, ‖z j‖ ≤ R}`. -/
def coordinateClosedPolydisc (n : ℕ) (R : ℝ) : Set (Fin n → ℂ) :=
  {z | ∀ j, ‖z j‖ ≤ R}

end VacuumBellSeparation.Gaussian
