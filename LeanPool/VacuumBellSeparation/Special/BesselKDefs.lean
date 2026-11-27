/-
Copyright (c) 2026 Physical Superintelligence PBC. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: David Turturean
-/
-- Adapted by Lean Pool for its pinned Lean and Mathlib versions.
module

public import Mathlib.Analysis.Complex.Trigonometric
public import Mathlib.MeasureTheory.Integral.Bochner.Basic
public import Mathlib.MeasureTheory.Measure.Lebesgue.Basic

/-!
# Statement seed extracted from Special/BesselK

Literal declarations are unchanged; theorem conclusions remain in the implementation module.
-/

@[expose] public section

open MeasureTheory Set Filter Topology

namespace VacuumBellSeparation

/-- The modified Bessel function of the second kind `K_ν(z)`, defined by the integral
representation [DLMF 10.32.9] that the manuscript uses (Section 6 preamble):
`K_ν(z) = ∫₀^∞ exp(-z cosh u) cosh(ν u) du`. The integral converges absolutely for `Re z > 0`
(`integrableOn_besselK_integrand`). For `Re z ≤ 0` the integrand is not integrable and the
definition takes Lean's junk value `0`; no statement in this file uses that range. -/
noncomputable def besselK (ν : ℝ) (z : ℂ) : ℂ :=
  ∫ u in Ioi (0 : ℝ), Complex.exp (-(z * Real.cosh u)) * Real.cosh (ν * u)

/-- The real form `K_ν(x) = ∫₀^∞ exp(-x cosh u) cosh(ν u) du` of `besselK` for real `x`;
`besselK ν x = besselKReal ν x` (`besselK_ofReal`). -/
noncomputable def besselKReal (ν x : ℝ) : ℝ :=
  ∫ u in Ioi (0 : ℝ), Real.exp (-(x * Real.cosh u)) * Real.cosh (ν * u)


end VacuumBellSeparation
