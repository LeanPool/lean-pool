/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.Coulomb
import LeanPool.LiebThirring.Electrostatics.PotentialIdentityAssembly
import LeanPool.LiebThirring.Electrostatics.Collisions

/-!
# Baxter

Baxter’s electrostatic inequality, including collisions and empty configurations, from the
Voronoi boundary measure argument.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

theorem baxter (N M : ℕ) (Z : ℝ≥0) (R : Fin M → Position) (x : Configuration N) :
    attraction (fun _ => Z) R x + baxterCorrection Z R ≤
      electronRepulsion x + nuclearRepulsion (fun _ => Z) R +
        nearestNucleusControl Z R x :=
  baxter_of_basicElectrostaticInequality
    (fun _ Z R hM hR => basicElectrostaticInequality_of_injective hM Z R hR) N M Z R x

end LiebThirring

end
