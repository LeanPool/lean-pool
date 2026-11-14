/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.LowMomentumFormula
public import LeanPool.LiebThirring.Kinetic.PauliOccupation

/-!
# The unconditional low-momentum density bound

Each low-field spin component is bounded by the phase-space volume.

Summing the spin components gives `q` times the low-region volume.
-/

public section

open MeasureTheory

namespace LiebThirring

/-- Each low-field spin component is bounded by the phase-space volume. -/
theorem lowFourierField_density_component_bound {N q : ℕ} (i : Fin N)
    (ψ : State N q) (hψ : antisymmetric ψ) (hnorm : ‖ψ‖ = 1)
    (E : ℝ) (hE : 0 ≤ E) (x : Position) (s : Fin q) :
    ‖lowFourierField (densityField i ψ) E x s‖ ^ 2 ≤
      (volume (lowMomentumRegion E)).toReal := by
  rw [lowFourierField_density_component_norm_sq]
  exact (oneParticleContraction_pauli_of_norm_eq_one i ψ hψ hnorm
    (lowMomentumTest E x s hE)).trans_eq (lowMomentumTest_norm_sq E hE x s)

/-- Summing the spin components gives `q` times the low-region volume. -/
theorem lowFourierField_density_bound_volume {N q : ℕ} (i : Fin N)
    (ψ : State N q) (hψ : antisymmetric ψ) (hnorm : ‖ψ‖ = 1)
    (E : ℝ) (hE : 0 ≤ E) (x : Position) :
    ‖lowFourierField (densityField i ψ) E x‖ ^ 2 ≤
      (q : ℝ) * (volume (lowMomentumRegion E)).toReal := by
  rw [PiLp.norm_sq_eq_of_L2]
  calc
    _ ≤ ∑ s : Fin q, (volume (lowMomentumRegion E)).toReal :=
      Finset.sum_le_sum (fun s _ =>
        lowFourierField_density_component_bound i ψ hψ hnorm E hE x s)
    _ = _ := by
      simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]

/-- the low-momentum bound: the scaled density field has the exact three-dimensional low-momentum
bound at every spatial point, with no finite-energy or positive-spin premise. -/
theorem lowFourierField_density_bound {N q : ℕ} (i : Fin N)
    (ψ : State N q) (hψ : antisymmetric ψ) (hnorm : ‖ψ‖ = 1)
    (E : ℝ) (hE : 0 ≤ E) (x : Position) :
    ‖lowFourierField (densityField i ψ) E x‖ ^ 2 ≤
      (q : ℝ) * (1 / (6 * Real.pi ^ 2)) * E ^ ((3 : ℝ) / 2) := by
  have hvol : (volume (lowMomentumRegion E)).toReal =
      (1 / (6 * Real.pi ^ 2)) * E ^ ((3 : ℝ) / 2) := by
    rw [volume_lowMomentumRegion E hE, ENNReal.toReal_ofReal]
    positivity
  exact (lowFourierField_density_bound_volume i ψ hψ hnorm E hE x).trans_eq (by
    rw [hvol, mul_assoc])

end LiebThirring
end
