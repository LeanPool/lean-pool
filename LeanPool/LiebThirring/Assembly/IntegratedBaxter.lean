/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Assembly.WeakBaxter
public import LeanPool.LiebThirring.Kinetic.DensityBasic

/-!
# Integrated weak Baxter inequality

Testing nearest-nucleus control against a state yields the density integral.

The integrated weak Baxter bound, conditional on the exact Baxter proposition, for every
normalized state and bounded-charge configuration.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal
namespace LiebThirring.Assembly

/-- Testing nearest-nucleus control against a state yields the density integral. -/
theorem lintegral_nearestNucleusControl {N q M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (ψ : State N q) :
    (∫⁻ X : Configuration N, nearestNucleusControl Z R X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) =
      (2 * (Z : ℝ≥0∞) + 1) *
        (∫⁻ x : Position, (nearestNucleusDistance R x)⁻¹ * density ψ x) := by
  have hf (i : Fin N) : Measurable (fun X : Configuration N =>
      (nearestNucleusDistance R (particlePosition X i))⁻¹ * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) :=
    ((measurable_nearestNucleusInverse R).comp (measurable_particlePosition i)).mul
      (measurable_state_norm_sq ψ)
  simp only [nearestNucleusControl, mul_assoc, Finset.sum_mul]
  rw [lintegral_const_mul _ (Finset.measurable_sum _ (fun i _ => hf i)),
    lintegral_finsetSum _ (fun i _ => hf i),
    ← density_testing N q ψ _ (measurable_nearestNucleusInverse R)]

private theorem integrated_weak_baxter {N q M : ℕ} (Z : ℝ≥0)
    (z : Fin M → ℝ≥0) (R : Fin M → Position) (ψ : State N q) (hψ : ‖ψ‖ = 1)
    (hW : ∀ X : Configuration N, attraction z R X ≤
      electronRepulsion X + nuclearRepulsion z R + nearestNucleusControl Z R X) :
    (∫⁻ X : Configuration N, attraction z R X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) ≤
      (∫⁻ X : Configuration N, electronRepulsion X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) +
        nuclearRepulsion z R + (2 * (Z : ℝ≥0∞) + 1) *
          (∫⁻ x : Position, (nearestNucleusDistance R x)⁻¹ * density ψ x) := by
  have hnorm : ‖ψ‖₊ = 1 := NNReal.eq hψ
  have hm := measurable_state_norm_sq ψ
  have he : Measurable (fun X : Configuration N =>
      electronRepulsion X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) :=
    (measurable_electronRepulsion (N := N)).mul hm
  have hn : Measurable (fun X : Configuration N =>
      nuclearRepulsion z R * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) :=
    (measurable_const (a := nuclearRepulsion z R)).mul hm
  calc
    _ ≤ ∫⁻ X : Configuration N,
        (electronRepulsion X + nuclearRepulsion z R + nearestNucleusControl Z R X) *
          (‖ψ X‖₊ : ℝ≥0∞) ^ 2 :=
      lintegral_mono (fun X => mul_le_mul_left (hW X) _)
    _ = _ := by
      conv_lhs => simp only [add_mul]
      have hes : Measurable (fun X : Configuration N =>
          electronRepulsion X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2 +
          nuclearRepulsion z R * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) := he.add hn
      rw [lintegral_add_left hes, lintegral_add_left he,
        lintegral_const_mul _ hm, lintegral_state_norm_sq, hnorm,
        ENNReal.coe_one, one_pow, mul_one, lintegral_nearestNucleusControl]
/-- The integrated weak Baxter bound, conditional on the exact Baxter
proposition, for every normalized state and bounded-charge configuration. -/
theorem integratedBaxter_of_baxter
    (hB : ∀ (N M : ℕ) (Z : ℝ≥0) (R : Fin M → Position) (x : Configuration N),
      attraction (fun _ => Z) R x + baxterCorrection Z R ≤
        electronRepulsion x + nuclearRepulsion (fun _ => Z) R +
          nearestNucleusControl Z R x)
    {N q M : ℕ} (Z : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (ψ : State N q) (hz : ∀ k, z k ≤ Z) (hψ : ‖ψ‖ = 1) :
    (∫⁻ X : Configuration N, attraction z R X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) ≤
      (∫⁻ X : Configuration N, electronRepulsion X * (‖ψ X‖₊ : ℝ≥0∞) ^ 2) +
        nuclearRepulsion z R + (2 * (Z : ℝ≥0∞) + 1) *
          (∫⁻ x : Position, (nearestNucleusDistance R x)⁻¹ * density ψ x) := by
  exact integrated_weak_baxter Z z R ψ hψ
    (fun X => weakBaxter_of_baxter hB N M Z z R X hz)

end LiebThirring.Assembly

end
