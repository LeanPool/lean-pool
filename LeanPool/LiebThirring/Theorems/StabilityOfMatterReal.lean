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
public import LeanPool.LiebThirring.Defs.Coulomb
public import LeanPool.LiebThirring.Assembly.RealFormStability
import LeanPool.LiebThirring.Analysis.Hardy

/-!
# Real quadratic-form stability

Finiteness of Coulomb expectations and real quadratic-form stability, using the Fourier Hardy
bound and extended stability with the same constant.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

theorem stability_of_matter_real (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : State N q),
        (∀ k, z k ≤ Z) → Function.Injective R →
          antisymmetric ψ → ‖ψ‖ = 1 → kineticEnergy ψ < ⊤ →
            (∫⁻ x : Configuration N,
              attraction z R x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) < ⊤ ∧
            (∫⁻ x : Configuration N,
              electronRepulsion x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) < ⊤ ∧
            nuclearRepulsion z R < ⊤ ∧
            -(C : ℝ) * ((N + M : ℕ) : ℝ) ≤
              (kineticEnergy ψ).toReal +
                (∫⁻ x : Configuration N,
                  electronRepulsion x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2).toReal +
                (nuclearRepulsion z R).toReal -
                (∫⁻ x : Configuration N,
                  attraction z R x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2).toReal := by
  exact LiebThirring.Assembly.stability_of_matter_real_of_one_body_bound q hq Z
    (fun _ c u => LiebThirring.lintegral_coulomb_le_of_fourier c u)

end LiebThirring

end
