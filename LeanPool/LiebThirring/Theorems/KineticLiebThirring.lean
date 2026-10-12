/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Defs.Antisymmetric
public import LeanPool.LiebThirring.Defs.KineticEnergy
public import LeanPool.LiebThirring.Defs.Density
public import LeanPool.LiebThirring.Defs.RuminConstant
import LeanPool.LiebThirring.Kinetic.KineticLT

/-!
# Kinetic Lieb–Thirring inequality

The kinetic Lieb–Thirring inequality for normalized antisymmetric L² states, from the Pauli
occupation estimate and Rumin integration.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

theorem kinetic_lieb_thirring (q : ℕ) (hq : 1 ≤ q) (N : ℕ) (ψ : State N q)
    (hanti : antisymmetric ψ) (hnorm : ‖ψ‖ = 1) :
    (ruminConstant : ℝ≥0∞) * (q : ℝ≥0∞) ^ (-(2 : ℝ) / 3) *
      (∫⁻ x : Position, density ψ x ^ ((5 : ℝ) / 3)) ≤ kineticEnergy ψ :=
  Kinetic.kinetic_lieb_thirring q hq N ψ hanti hnorm

end LiebThirring

end
