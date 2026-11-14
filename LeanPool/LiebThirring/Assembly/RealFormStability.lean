/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Assembly.RealFormPairs
public import LeanPool.LiebThirring.Theorems.StabilityOfMatter

/-!
# Real-form stability conditional on the one-body Hardy bound

The one-body Hardy bound gives finite Coulomb expectations and a real quadratic-form inequality
with the same constant as extended stability.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring.Assembly

/-- Real-form stability from additive stability and the one-body Fourier Coulomb bound. -/
theorem stability_of_matter_real_of_one_body_bound (q : ℕ) (hq : 1 ≤ q) (Z : ℝ≥0)
    (hHardy : ∀ (N : ℕ) (c : Position)
      (u : Lp (SpinAmplitudes N q) 2 (volume : Measure Position)),
      (∫⁻ x : Position, coulombKernel x c * (‖u x‖₊ : ℝ≥0∞) ^ 2) ≤
        (‖u‖₊ : ℝ≥0∞) ^ 2 + 4 * ∫⁻ ξ : Position,
          ENNReal.ofReal ((2 * Real.pi) ^ 2) * (‖ξ‖₊ : ℝ≥0∞) ^ 2 *
            (‖(Lp.fourierTransformₗᵢ Position (SpinAmplitudes N q) u) ξ‖₊ : ℝ≥0∞) ^ 2) :
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
  obtain ⟨C, hC, hstability⟩ := LiebThirring.stability_of_matter q hq Z
  refine ⟨C, hC, ?_⟩
  intro N M z R ψ hz hR hψ hnorm hT
  have hB := lintegral_electronRepulsion_lt_top_of_one_body_bound (hHardy N) ψ hT
  have hU := nuclearRepulsion_lt_top z R hR
  have hreal := real_form_of_extended_bound C (N + M) hT hB hU
    (hstability N M z R ψ hz hψ hnorm)
  exact ⟨hreal.1, hB, hU, hreal.2⟩

end LiebThirring.Assembly
end
