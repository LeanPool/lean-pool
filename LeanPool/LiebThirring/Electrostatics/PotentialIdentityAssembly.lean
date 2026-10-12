/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.PotentialIdentity
import LeanPool.LiebThirring.Electrostatics.EnergyDeficit
import LeanPool.LiebThirring.Electrostatics.SquareCompletion

/-!
# The basic electrostatic inequality from the Voronoi face charge

Finite face-charge self-energy, the potential identity, and the energy deficit give the basic
electrostatic inequality for distinct nuclei by square completion.
-/

public section

open MeasureTheory Laplacian
open scoped NNReal ContDiff

namespace LiebThirring

/-- the basic electrostatic inequality with no analytic premises: the Voronoi charge supplies
square completion. -/
theorem basicElectrostaticInequality_of_injective {M : ℕ}
    (hM : 1 ≤ M) (Z : ℝ≥0) (R : Fin M → Position) (hR : Function.Injective R) :
    BasicElectrostaticInequality Z R := by
  have := isFiniteMeasure_voronoiFaceMeasure R hR Z.coe_nonneg
  have hPhi := screenedPotential_eq_coulombPotential_voronoiFaceMeasure hM Z R hR
  exact basicElectrostaticInequality_of_potential Z R (voronoiFaceMeasure R hR (Z : ℝ))
    (ne_of_lt (coulombEnergy_voronoiFaceMeasure_lt_top R hR Z.coe_nonneg)) hPhi
    (energyDeficit_of_potential_eq hM Z R hR hPhi)

end LiebThirring

end
