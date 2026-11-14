/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.FaceMeasure
public import LeanPool.LiebThirring.Electrostatics.Screened
import all LeanPool.LiebThirring.Electrostatics.Basic

/-!
# Trivial cases of the energy deficit

The square-completion deficit input is unconditional when the charge is zero.

The square-completion deficit input for one nucleus is entirely unconditional.
-/

public section

open Set MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

@[simp] theorem baxterCorrection_one (Z : ℝ≥0) (R : Fin 1 → Position) :
    baxterCorrection Z R = 0 := by
  simp [baxterCorrection]

@[simp] theorem nuclearRepulsion_one (Z : ℝ≥0) (R : Fin 1 → Position) :
    nuclearRepulsion (fun _ => Z) R = 0 := by
  classical
  have hi (k : Fin 1) : Finset.univ.filter (fun l : Fin 1 => k < l) = ∅ := by
    ext l
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
    exact not_lt_of_ge (le_of_eq (Subsingleton.elim _ _))
  simp only [nuclearRepulsion, hi, Finset.sum_empty, Finset.sum_const_zero]

/-- The square-completion deficit input for one nucleus is entirely unconditional. -/
theorem energyDeficit_one (Z : ℝ≥0) (R : Fin 1 → Position) (hR : Function.Injective R) :
    coulombEnergy (voronoiFaceMeasure R hR (Z : ℝ)) (voronoiFaceMeasure R hR (Z : ℝ)) / 2 +
      baxterCorrection Z R ≤ nuclearRepulsion (fun _ => Z) R := by
  simp [coulombEnergy, voronoiFaceMeasure_one]

end LiebThirring

end
