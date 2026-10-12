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
import LeanPool.LiebThirring.Theorems.Baxter
import LeanPool.LiebThirring.Theorems.KineticLiebThirring
import LeanPool.LiebThirring.Assembly.Stability

/-!
# Stability of matter

Stability of matter in nonnegative extended additive form, from Baxter’s electrostatic
inequality and the kinetic Lieb–Thirring inequality.
-/

public section

open MeasureTheory WithLp
open scoped ENNReal NNReal

namespace LiebThirring

theorem stability_of_matter (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0) :
    ∃ C : ℝ≥0, 0 < C ∧
      ∀ (N M : ℕ) (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : State N q),
        (∀ k, z k ≤ Z) → antisymmetric ψ → ‖ψ‖ = 1 →
          (∫⁻ x : Configuration N, attraction z R x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) ≤
            kineticEnergy ψ +
              (∫⁻ x : Configuration N, electronRepulsion x * (‖ψ x‖₊ : ℝ≥0∞) ^ 2) +
              nuclearRepulsion z R + (C : ℝ≥0∞) * (N + M : ℕ) :=
  Assembly.stability_of_matter_of_baxter_of_lt LiebThirring.baxter
    LiebThirring.kinetic_lieb_thirring q hq Z

end LiebThirring

end
