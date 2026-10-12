/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.Screened
import LeanPool.LiebThirring.Electrostatics.CoulombPositivity
import all LeanPool.LiebThirring.Electrostatics.Basic
import all LeanPool.LiebThirring.Electrostatics.Screened

/-!
# Abstract square completion for the basic electrostatic inequality

Coulomb positivity gives the basic electrostatic inequality from a finite-energy screening
measure with the prescribed potential and nuclear-energy deficit.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- the basic electrostatic inequality from a finite-energy screening measure with the prescribed
potential and nuclear-energy deficit. -/
theorem basicElectrostaticInequality_of_potential {M : ℕ}
    (Z : ℝ≥0) (R : Fin M → Position) (ν : Measure Position) [IsFiniteMeasure ν]
    (hνE : coulombEnergy ν ν ≠ ⊤)
    (hΦ : ∀ x, screenedPotential Z R x = coulombPotential ν x)
    (hdef : coulombEnergy ν ν / 2 + baxterCorrection Z R ≤
      nuclearRepulsion (fun _ => Z) R) :
    BasicElectrostaticInequality Z R := by
  intro μ hμ hμE
  have : IsFiniteMeasure μ := hμ
  have hpotential : (∫⁻ x, screenedPotential Z R x ∂μ) = coulombEnergy μ ν := by
    unfold coulombEnergy
    exact lintegral_congr hΦ
  have henergy : coulombEnergy μ ν ≤ coulombEnergy μ μ / 2 + coulombEnergy ν ν / 2 := by
    have h := ENNReal.div_le_div_right (two_mul_coulombEnergy_le μ ν hμE hνE) 2
    rwa [ENNReal.add_div, mul_comm (2 : ℝ≥0∞),
      ENNReal.mul_div_cancel_right (by norm_num) (by norm_num)] at h
  rw [hpotential]
  calc
    coulombEnergy μ ν + baxterCorrection Z R ≤
        (coulombEnergy μ μ / 2 + coulombEnergy ν ν / 2) + baxterCorrection Z R :=
      add_le_add henergy le_rfl
    _ = coulombEnergy μ μ / 2 + (coulombEnergy ν ν / 2 + baxterCorrection Z R) :=
      add_assoc _ _ _
    _ ≤ coulombEnergy μ μ / 2 + nuclearRepulsion (fun _ => Z) R :=
      add_le_add le_rfl hdef

end LiebThirring

end
