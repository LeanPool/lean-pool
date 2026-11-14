/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.Newton
import LeanPool.LiebThirring.Electrostatics.Gaussian
import all LeanPool.LiebThirring.Electrostatics.Basic

/-!
# Energies, comparison, and regularity of spherical shells

Interacting with a point charge evaluates the potential at that point.

A point charge in the first energy argument also evaluates the potential.
-/

public section

open MeasureTheory Set
open scoped ENNReal

namespace LiebThirring

/-- Newton's potential is no greater than the potential of the center point. -/
theorem coulombPotential_shell_le_kernel (a : Position) {r : ℝ} (hr : 0 < r)
    (x : Position) : coulombPotential (shell a r) x ≤ coulombKernel x a := by
  rw [coulombPotential_shell a hr x, coulombKernel]
  exact ENNReal.inv_le_inv.mpr (ENNReal.ofReal_le_ofReal (le_max_left _ _))

/-- Outside or on the shell, its potential equals the point-charge potential. -/
theorem coulombPotential_shell_of_radius_le (a : Position) {r : ℝ} (hr : 0 < r)
    (x : Position) (hx : r ≤ ‖x - a‖) :
    coulombPotential (shell a r) x = coulombKernel x a := by
  rw [coulombPotential_shell a hr x, max_eq_left hx]
  rfl

/-- The self-energy has no factor `1/2`, in accordance with the shared definition. -/
theorem coulombEnergy_shell_self (a : Position) {r : ℝ} (hr : 0 < r) :
    coulombEnergy (shell a r) (shell a r) = (ENNReal.ofReal r)⁻¹ := by
  unfold coulombEnergy
  calc
    _ = ∫⁻ _x, (ENNReal.ofReal r)⁻¹ ∂shell a r := by
      apply lintegral_congr_ae
      filter_upwards [ae_shell_norm a hr.le] with x hx
      rw [coulombPotential_shell a hr x, hx, max_self]
    _ = _ := by rw [lintegral_const, measure_univ, mul_one]

/-- Spherical smearing decreases mutual Coulomb energy, even for coincident centers. -/
theorem coulombEnergy_shell_le_kernel (a b : Position) {r s : ℝ}
    (hr : 0 < r) (hs : 0 < s) :
    coulombEnergy (shell a r) (shell b s) ≤ coulombKernel a b := by
  calc
    _ ≤ ∫⁻ x, coulombKernel x b ∂shell a r := by
      unfold coulombEnergy
      exact lintegral_mono (fun x => coulombPotential_shell_le_kernel b hs x)
    _ = coulombPotential (shell a r) b := by
      unfold coulombPotential
      simp_rw [coulombKernel_symm _ b]
    _ ≤ coulombKernel a b := by
      rw [coulombKernel_symm a b]
      exact coulombPotential_shell_le_kernel a hr b

end LiebThirring

end
