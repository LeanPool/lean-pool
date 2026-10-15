/-
Copyright (c) 2026 JD Jones. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: JD Jones
-/
module

public import LeanPool.PlanarMidpoint.DifferentialRigidity
public import Mathlib.Tactic.FinCases

/-! Five exact direction tests determine the quartic obstruction at each point. -/

@[expose] public section
namespace PlanarMidpoint

/-- Five fixed directions suffice because each obstruction component is quartic. -/
theorem obstruction_zero_of_five (c : Coeff) (J : E →L[ℝ] Coeff)
    (htest : ∀ j : Fin 5, obstruction c J (vec (j : ℝ) 1) = 0) :
    ∀ h : E, obstruction c J h = 0 := by
  have hk := kernel_of_five_arrayObstruction_zero c (derivativeArray J) (fun j ↦ by
    simpa only [arrayObstruction_derivativeArray] using htest j)
  intro h
  simpa only [arrayObstruction_derivativeArray] using
    (kernel_iff_arrayObstruction_zero c (derivativeArray J)).mp hk h

/-- Exact tests in the five directions `(j,1)`, at every point of the domain,
force a differentiable planar cubic field to be constant. -/
theorem planar_five_direction_rigidity
    (Ω : Set E) (C : E → Coeff)
    (openΩ : IsOpen Ω) (connectedΩ : IsPreconnected Ω)
    (diffC : DifferentiableOn ℝ C Ω)
    (tests : ∀ p ∈ Ω, ∀ j : Fin 5,
      obstruction (C p) (fderiv ℝ C p) (vec (j : ℝ) 1) = 0) :
    ∃ c : Coeff, ∀ p ∈ Ω, C p = c := by
  apply planar_obstruction_rigidity Ω C openΩ connectedΩ diffC
  intro p hp
  exact obstruction_zero_of_five (C p) (fderiv ℝ C p) (tests p hp)

end PlanarMidpoint
