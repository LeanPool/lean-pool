/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.ShellAssemblyGeometry
public import LeanPool.LiebThirring.Electrostatics.ShellAssemblyEnergy
import all LeanPool.LiebThirring.Electrostatics.Screened

/-!
# Baxter shell assembly from the basic electrostatic inequality

The inverse half-distance is twice the inverse distance, in the extended reals.

Shell assembly for nonempty nuclei and electrons away from nuclear singularities. No electron
separation is needed in this additive extended proof.
-/

public section

open MeasureTheory
open scoped ENNReal NNReal

namespace LiebThirring

/-- The inverse half-distance is twice the inverse distance, in the extended reals. -/
theorem inv_ofReal_half (d : ℝ) :
    (ENNReal.ofReal (d / 2))⁻¹ = 2 * (ENNReal.ofReal d)⁻¹ := by
  rw [ENNReal.ofReal_div_of_pos (by norm_num : (0 : ℝ) < 2)]
  norm_num only [ENNReal.ofReal_ofNat]
  rw [ENNReal.inv_div (Or.inl (by norm_num)) (Or.inl (by norm_num)), div_eq_mul_inv]

/-- Shell assembly for nonempty nuclei and electrons away from nuclear singularities.
No electron separation is needed in this additive extended proof. -/
theorem baxter_of_basicElectrostaticInequality_of_separated {N M : ℕ}
    (Z : ℝ≥0) (R : Fin M → Position) (x : Configuration N)
    (hM : 1 ≤ M) (hB12 : BasicElectrostaticInequality Z R)
    (hx : ∀ i k, particlePosition x i ≠ R k) :
    attraction (fun _ => Z) R x + baxterCorrection Z R ≤
      electronRepulsion x + nuclearRepulsion (fun _ => Z) R +
        nearestNucleusControl Z R x := by
  classical
  choose k hk using fun i : Fin N => exists_nearest_nucleus hM R (particlePosition x i)
  let d : Fin N → ℝ := fun i => ‖particlePosition x i - R (k i)‖
  have hd (i : Fin N) : 0 < d i := norm_pos_iff.mpr (sub_ne_zero.mpr (hx i (k i)))
  have hbound (i : Fin N) (l : Fin M) : d i ≤ ‖particlePosition x i - R l‖ := hk i l
  let μ : Measure Position := ∑ i, shell (particlePosition x i) (d i / 2)
  have hμ : IsFiniteMeasure μ := by dsimp [μ]; infer_instance
  have he : coulombEnergy μ μ ≠ ⊤ :=
    coulombEnergy_sum_shell_ne_top _ _ (fun i => half_pos (hd i))
  have hb := hB12 μ hμ he
  let S : ℝ≥0∞ := ∫⁻ y, screenedPotential Z R y ∂μ
  let T : ℝ≥0∞ := ∑ i, (ENNReal.ofReal (d i / 2))⁻¹
  have ha : attraction (fun _ => Z) R x ≤ S + (Z : ℝ≥0∞) * T := by
    dsimp [attraction, S, T, μ]
    rw [lintegral_finsetSum_measure, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_le_sum (fun i _ => nuclearPotential_le_shell_screened_add
      hM Z R _ (hd i) (hbound i))
  have henergy : coulombEnergy μ μ / 2 ≤ electronRepulsion x + T / 2 :=
    coulombEnergy_sum_shell_div_two_le x _ (fun i => half_pos (hd i))
  have hT : T = 2 * ∑ i, (nearestNucleusDistance R (particlePosition x i))⁻¹ := by
    dsimp [T]
    simp_rw [nearestNucleusDistance_eq_of_min R _ _ (hk _), inv_ofReal_half]
    exact (Finset.mul_sum _ _ _).symm
  calc
    attraction (fun _ => Z) R x + baxterCorrection Z R ≤
        (S + (Z : ℝ≥0∞) * T) + baxterCorrection Z R := add_le_add_left ha _
    _ = (S + baxterCorrection Z R) + (Z : ℝ≥0∞) * T := by ac_rfl
    _ ≤ (coulombEnergy μ μ / 2 + nuclearRepulsion (fun _ => Z) R) + (Z : ℝ≥0∞) * T :=
      add_le_add_left hb _
    _ ≤ (electronRepulsion x + T / 2 + nuclearRepulsion (fun _ => Z) R) + (Z : ℝ≥0∞) * T :=
      add_le_add_left (add_le_add_left henergy _) _
    _ = electronRepulsion x + nuclearRepulsion (fun _ => Z) R + nearestNucleusControl Z R x := by
      rw [hT, ENNReal.mul_div_right_comm, ENNReal.div_self (by norm_num) (by norm_num)]
      unfold nearestNucleusControl
      ring

end LiebThirring

end
