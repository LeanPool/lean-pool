/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.Basic

/-!
# The screened nuclear potential and the basic electrostatic inequality

`screenedPotential Z R x` omits a nearest nucleus. The basic electrostatic inequality for
positive finite-energy measures connects the Voronoi face-charge argument with shell assembly.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- The potential of all nuclei except a nearest one: `min_k Σ_{p ≠ k} Z |x - R_p|⁻¹`. -/
noncomputable def screenedPotential {M : ℕ} (Z : ℝ≥0) (R : Fin M → Position)
    (x : Position) : ℝ≥0∞ :=
  ⨅ k : Fin M, ∑ p ∈ Finset.univ.erase k, (Z : ℝ≥0∞) * coulombKernel x (R p)

/-- the basic electrostatic inequality,, for positive finite measures of finite Coulomb energy:
`∫ Φ dμ + C_R ≤ D(μ, μ) + U`. -/
def BasicElectrostaticInequality {M : ℕ} (Z : ℝ≥0) (R : Fin M → Position) : Prop :=
  ∀ μ : Measure Position, IsFiniteMeasure μ → coulombEnergy μ μ ≠ ⊤ →
    (∫⁻ x, screenedPotential Z R x ∂μ) + baxterCorrection Z R ≤
      coulombEnergy μ μ / 2 + nuclearRepulsion (fun _ => Z) R

end LiebThirring

end
