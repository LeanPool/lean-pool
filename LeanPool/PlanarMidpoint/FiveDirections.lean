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
  let z := derivativeArray J
  have ht : ∀ j : Fin 5, arrayObstruction c z (vec (j : ℝ) 1) = 0 := by
    intro j
    simpa only [z, arrayObstruction_derivativeArray] using htest j
  have h0 : ∀ j : Fin 5,
      rows c z 0 * (j : ℝ) ^ 4 + rows c z 1 * (j : ℝ) ^ 3 + rows c z 2 * (j : ℝ) ^ 2 + rows c z 3
          * (j : ℝ) + rows c z 4 = 0 := by
    intro j
    simpa [arrayObstruction_component_0, vec] using
      congrArg (fun v : E ↦ v 0) (ht j)
  have h1 : ∀ j : Fin 5,
      rows c z 5 * (j : ℝ) ^ 4 + rows c z 6 * (j : ℝ) ^ 3 + rows c z 7 * (j : ℝ) ^ 2 + rows c z 8
          * (j : ℝ) + rows c z 9 = 0 := by
    intro j
    simpa [arrayObstruction_component_1, vec] using
      congrArg (fun v : E ↦ v 1) (ht j)
  have hs0 := quartic_coefficients_zero _ _ _ _ _ h0
  have hs1 := quartic_coefficients_zero _ _ _ _ _ h1
  obtain ⟨h0, h1, h2, h3, h4⟩ := hs0
  obtain ⟨h5, h6, h7, h8, h9⟩ := hs1
  have hrows : ∀ i, rows c z i = 0 := by
    intro i
    fin_cases i <;> assumption
  have hk := (kernel_iff_rows c z).mpr hrows
  intro h
  simpa only [z, arrayObstruction_derivativeArray] using
    (kernel_iff_arrayObstruction_zero c z).mp hk h

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
