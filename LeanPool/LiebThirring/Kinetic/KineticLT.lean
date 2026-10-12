/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Kinetic.RuminIntegration
public import LeanPool.LiebThirring.Kinetic.LowMomentumBound
public import LeanPool.LiebThirring.Kinetic.KineticLTVacuum

/-!
# Kinetic Lieb--Thirring inequality on the state carrier

The non-vacuum Rumin estimate and the vacuum density identity give the kinetic Lieb–Thirring
inequality.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.Kinetic

/-- Conditional assembly with exactly the pointwise low-momentum estimate
as its sole extra premise. The final theorem supplies it from the unconditional low-momentum
theorem. -/
theorem kinetic_lieb_thirring_of_lowMomentumBound (q : ℕ) (hq : 1 ≤ q)
    (N : ℕ) (ψ : State N q) (hanti : antisymmetric ψ)
    (hLow : ∀ i : Fin N, ∀ E : ℝ, 0 ≤ E → ∀ x : Position,
      ‖lowFourierField (densityField i ψ) E x‖ ^ 2 ≤
        (q : ℝ) * (1 / (6 * Real.pi ^ 2)) * E ^ ((3 : ℝ) / 2)) :
    (ruminConstant : ℝ≥0∞) * (q : ℝ≥0∞) ^ (-(2 : ℝ) / 3) *
      (∫⁻ x : Position, density ψ x ^ ((5 : ℝ) / 3)) ≤ kineticEnergy ψ := by
  cases N with
  | zero =>
      rw [lintegral_density_rpow_vacuum ψ _ (by norm_num), mul_zero]
      exact zero_le
  | succ N =>
      let i : Fin (N + 1) := ⟨0, Nat.succ_pos N⟩
      exact rumin_bound_of_lowMomentumBound q hq i ψ hanti (hLow i)

/-- Proof of the kinetic Lieb--Thirring theorem. -/
theorem kinetic_lieb_thirring (q : ℕ) (hq : 1 ≤ q) (N : ℕ) (ψ : State N q)
    (hanti : antisymmetric ψ) (hnorm : ‖ψ‖ = 1) :
    (ruminConstant : ℝ≥0∞) * (q : ℝ≥0∞) ^ (-(2 : ℝ) / 3) *
      (∫⁻ x : Position, density ψ x ^ ((5 : ℝ) / 3)) ≤ kineticEnergy ψ :=
  kinetic_lieb_thirring_of_lowMomentumBound q hq N ψ hanti
    (fun i E hE x => lowFourierField_density_bound i ψ hanti hnorm E hE x)

end LiebThirring.Kinetic
end
