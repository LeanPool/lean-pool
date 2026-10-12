/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Assembly.Coulomb
public import LeanPool.LiebThirring.Assembly.NuclearReindex
public import LeanPool.LiebThirring.Assembly.FiniteAveraging

/-!
# Conditional bounded-charge Baxter inequality

Weak Baxter for arbitrary bounded nonnegative charges, conditional only on the exact
equal-charge Baxter proposition.
-/

public section

open scoped ENNReal NNReal

namespace LiebThirring.Assembly

private theorem vertex_baxter
    (hB : ∀ (N M : ℕ) (Z : ℝ≥0) (R : Fin M → Position) (x : Configuration N),
      attraction (fun _ => Z) R x + baxterCorrection Z R ≤
        electronRepulsion x + nuclearRepulsion (fun _ => Z) R +
          nearestNucleusControl Z R x)
    (N M : ℕ) (Z : ℝ≥0) (R : Fin M → Position) (x : Configuration N)
    (v : Fin M → Bool) :
    attraction (fun k => if v k then Z else 0) R x ≤
      electronRepulsion x + nuclearRepulsion (fun k => if v k then Z else 0) R +
        nearestNucleusControl Z R x := by
  classical
  let I : Set (Fin M) := {k | v k = true}
  let e : Fin (Fintype.card I) ≃ I := (Fintype.equivFin I).symm
  have hz (k : Fin M) (hk : k ∉ I) : (if v k then Z else 0) = 0 := by
    exact ite_eq_right hk
  have he (j : Fin (Fintype.card I)) : (if v (e j).val then Z else 0) = Z :=
    ite_eq_left (e j).property
  rw [attraction_restrict I e _ _ _ hz, nuclearRepulsion_reindex_support I e _ _ hz]
  simp_rw [he]
  calc
    _ ≤ attraction (fun _ => Z) (fun j => R (e j).val) x +
        baxterCorrection Z (fun j => R (e j).val) := le_self_add
    _ ≤ _ := hB N (Fintype.card I) Z (fun j => R (e j).val) x
    _ ≤ _ := add_le_add le_rfl
      (nearestNucleusControl_restrict_le Z R (fun j => (e j).val) x)

private theorem averaged_attraction {N M : ℕ} (w : Fin M → Bool → ℝ≥0∞)
    (c : Fin M → Bool → ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (x : Configuration N) (hw : ∀ k, ∑ b, w k b = 1)
    (hc : ∀ k, ∑ b, w k b * (c k b : ℝ≥0∞) = (z k : ℝ≥0∞)) :
    (∑ v : Fin M → Bool, (∏ k, w k (v k)) * attraction (fun k => c k (v k)) R x) =
      attraction z R x := by
  classical
  unfold attraction
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro i _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  exact congrArg (fun a => a * coulombKernel (particlePosition x i) (R k))
    ((sum_product_weights_first w (fun k b => (c k b : ℝ≥0∞)) hw k).trans (hc k))

private theorem averaged_nuclearRepulsion {M : ℕ} (w : Fin M → Bool → ℝ≥0∞)
    (c : Fin M → Bool → ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (hw : ∀ k, ∑ b, w k b = 1)
    (hc : ∀ k, ∑ b, w k b * (c k b : ℝ≥0∞) = (z k : ℝ≥0∞)) :
    (∑ v : Fin M → Bool, (∏ k, w k (v k)) * nuclearRepulsion (fun k => c k (v k)) R) =
      nuclearRepulsion z R := by
  classical
  unfold nuclearRepulsion
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro k _
  rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro l hl
  have hkl : k ≠ l := (Finset.mem_filter.mp hl).2.ne
  simp_rw [← mul_assoc]
  rw [← Finset.sum_mul]
  have hs := sum_product_weights_second w (fun k b => (c k b : ℝ≥0∞)) hw k l hkl
  have hs' : (∑ v : Fin M → Bool, (∏ k, w k (v k)) *
      (c k (v k) : ℝ≥0∞) * (c l (v l) : ℝ≥0∞)) =
      (∑ b, w k b * (c k b : ℝ≥0∞)) * (∑ b, w l b * (c l b : ℝ≥0∞)) := by
    simpa only [mul_assoc] using hs
  rw [hs', hc, hc]

/-- Weak Baxter for arbitrary bounded nonnegative charges, conditional only on
the exact equal-charge Baxter proposition. -/
theorem weakBaxter_of_baxter
    (hB : ∀ (N M : ℕ) (Z : ℝ≥0) (R : Fin M → Position) (x : Configuration N),
      attraction (fun _ => Z) R x + baxterCorrection Z R ≤
        electronRepulsion x + nuclearRepulsion (fun _ => Z) R +
          nearestNucleusControl Z R x)
    (N M : ℕ) (Z : ℝ≥0) (z : Fin M → ℝ≥0) (R : Fin M → Position)
    (x : Configuration N) (hz : ∀ k, z k ≤ Z) :
    attraction z R x ≤ electronRepulsion x + nuclearRepulsion z R +
      nearestNucleusControl Z R x := by
  classical
  by_cases hZ : Z = 0
  · have hz0 : z = fun _ => 0 := funext (fun k => le_zero_iff.mp (hZ ▸ hz k))
    rw [hz0, attraction_zero]
    exact zero_le
  let t : Fin M → ℝ≥0 := fun k => z k / Z
  have ht (k : Fin M) : t k ≤ 1 := (div_le_one (pos_iff_ne_zero.mpr hZ)).mpr (hz k)
  let w : Fin M → Bool → ℝ≥0∞ := fun k b => if b then (t k : ℝ≥0∞) else (1 - t k : ℝ≥0)
  let c : Fin M → Bool → ℝ≥0 := fun _ b => if b then Z else 0
  have hw (k : Fin M) : ∑ b, w k b = 1 := by
    simp only [w, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true]
    rw [← ENNReal.coe_add, add_tsub_cancel_of_le (ht k), ENNReal.coe_one]
  have hc (k : Fin M) : ∑ b, w k b * (c k b : ℝ≥0∞) = (z k : ℝ≥0∞) := by
    simp only [w, c, Fintype.sum_bool, Bool.false_eq_true, ite_false, ite_true,
      ENNReal.coe_zero, mul_zero, add_zero, ← ENNReal.coe_mul]
    exact congrArg (fun a : ℝ≥0 => (a : ℝ≥0∞)) (div_mul_cancel₀ (z k) hZ)
  have hav := Finset.sum_le_sum (s := Finset.univ) (fun v _ =>
    mul_le_mul_right (vertex_baxter hB N M Z R x v) (∏ k, w k (v k)))
  change (∑ v : Fin M → Bool, (∏ k, w k (v k)) * attraction (fun k => c k (v k)) R x) ≤
    ∑ v : Fin M → Bool, (∏ k, w k (v k)) *
      (electronRepulsion x + nuclearRepulsion (fun k => c k (v k)) R +
        nearestNucleusControl Z R x) at hav
  simp_rw [mul_add, Finset.sum_add_distrib] at hav
  rw [averaged_attraction w c z R x hw hc, averaged_nuclearRepulsion w c z R hw hc,
    ← Finset.sum_mul, ← Finset.sum_mul, sum_product_weights w hw, one_mul, one_mul] at hav
  exact hav

end LiebThirring.Assembly

end
