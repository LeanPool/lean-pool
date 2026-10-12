/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import LeanPool.LiebThirring.Electrostatics.Screened
public import LeanPool.LiebThirring.Electrostatics.VoronoiBasic
import all LeanPool.LiebThirring.Electrostatics.Screened
import LeanPool.LiebThirring.Electrostatics.ShellAssemblyGeometry

/-!
# Finiteness and continuity of the screened potential

The extended screened potential and its real representative agree on their finite locus.
-/

public section

open scoped ENNReal NNReal

namespace LiebThirring

/-- The real form of the shared extended screened potential. -/
@[expose] noncomputable def screenedPotentialReal {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (x : Position) : ℝ :=
  (screenedPotential Z R x).toReal

/-- Every retained pole is separated from a closed nearest-nucleus cell. -/
theorem nuclear_separation_le_twice_dist {M : ℕ} (R : Fin M → Position)
    (k p : Fin M) {x : Position} (hx : x ∈ closedVoronoiCell R k) :
    ‖R p - R k‖ ≤ 2 * ‖x - R p‖ := by
  have ht := norm_sub_le_norm_sub_add_norm_sub (R p) x (R k)
  rw [norm_sub_rev (R p) x] at ht
  have hk : ‖x - R k‖ ≤ ‖x - R p‖ := by
    simpa only [dist_eq_norm] using hx p
  linarith

theorem ne_nucleus_of_mem_closedVoronoiCell {M : ℕ} (R : Fin M → Position)
    (hR : Function.Injective R) (k p : Fin M) (hpk : p ≠ k)
    {x : Position} (hx : x ∈ closedVoronoiCell R k) : x ≠ R p := by
  intro he
  have ht := nuclear_separation_le_twice_dist R k p hx
  rw [he, sub_self, norm_zero, mul_zero] at ht
  exact hpk (hR (sub_eq_zero.mp (norm_eq_zero.mp (le_antisymm ht (norm_nonneg _)))))

/-- The shared minimum is the explicit formula on every closed cell. -/
theorem screenedPotential_eq_on_closedVoronoiCell {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (k : Fin M) {x : Position}
    (hx : x ∈ closedVoronoiCell R k) :
    screenedPotential Z R x =
      ∑ p ∈ Finset.univ.erase k, (Z : ℝ≥0∞) * coulombKernel x (R p) := by
  apply screenedPotential_eq_of_min
  intro p
  simpa only [dist_eq_norm] using hx p

/-- Distinct nuclei make the screened potential finite even at a nucleus. -/
theorem screenedPotential_ne_top {M : ℕ} (hM : 1 ≤ M) (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (x : Position) :
    screenedPotential Z R x ≠ ⊤ := by
  classical
  obtain ⟨k, hk⟩ := exists_nearest_nucleus hM R x
  have hx : x ∈ closedVoronoiCell R k := by
    intro p
    simpa only [dist_eq_norm] using hk p
  rw [screenedPotential_eq_on_closedVoronoiCell Z R k hx]
  apply ENNReal.sum_ne_top.mpr
  intro p hp
  apply ENNReal.mul_ne_top (by simp)
  change (ENNReal.ofReal ‖x - R p‖)⁻¹ ≠ ⊤
  rw [ENNReal.inv_ne_top, ENNReal.ofReal_ne_zero_iff, norm_pos_iff, sub_ne_zero]
  exact ne_nucleus_of_mem_closedVoronoiCell R hR k p (Finset.mem_erase.mp hp).1 hx

/-- Extended continuity also holds without separation of the nuclei. -/
theorem continuous_screenedPotential {M : ℕ} (Z : ℝ≥0) (R : Fin M → Position) :
    Continuous (screenedPotential Z R) := by
  classical
  have hc (k : Fin M) : Continuous (fun x : Position =>
      ∑ p ∈ Finset.univ.erase k, (Z : ℝ≥0∞) * coulombKernel x (R p)) := by
    apply continuous_finsetSum
    intro p hp
    exact (ENNReal.continuous_const_mul (by simp)).comp
      ((ENNReal.continuous_ofReal.comp (continuous_id.sub continuous_const).norm).fun_inv)
  have hi := Continuous.finset_inf_apply (s := Finset.univ) (fun k _ => hc k)
  unfold screenedPotential
  simpa only [Finset.inf_eq_iInf, Finset.mem_univ, iInf_true] using hi

theorem continuous_screenedPotentialReal {M : ℕ} (hM : 1 ≤ M) (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) :
    Continuous (screenedPotentialReal Z R) := by
  apply continuous_iff_continuousAt.mpr
  intro x
  exact (ENNReal.continuousAt_toReal (screenedPotential_ne_top hM Z R hR x)).comp
    (continuous_screenedPotential Z R).continuousAt

/-- The real closed-cell formula has no singular retained denominators. -/
theorem screenedPotentialReal_eq_on_closedVoronoiCell {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k : Fin M)
    {x : Position} (hx : x ∈ closedVoronoiCell R k) :
    screenedPotentialReal Z R x =
      ∑ p ∈ Finset.univ.erase k, (Z : ℝ) * ‖x - R p‖⁻¹ := by
  classical
  unfold screenedPotentialReal
  rw [screenedPotential_eq_on_closedVoronoiCell Z R k hx, ENNReal.toReal_sum]
  · apply Finset.sum_congr rfl
    intro p hp
    simp only [ENNReal.toReal_mul, ENNReal.coe_toReal, coulombKernel,
      ENNReal.toReal_inv, ENNReal.toReal_ofReal (norm_nonneg _)]
  · intro p hp
    apply ENNReal.mul_ne_top (by simp)
    change (ENNReal.ofReal ‖x - R p‖)⁻¹ ≠ ⊤
    rw [ENNReal.inv_ne_top, ENNReal.ofReal_ne_zero_iff, norm_pos_iff, sub_ne_zero]
    exact ne_nucleus_of_mem_closedVoronoiCell R hR k p (Finset.mem_erase.mp hp).1 hx

theorem screenedPotentialReal_nonneg {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (x : Position) : 0 ≤ screenedPotentialReal Z R x :=
  ENNReal.toReal_nonneg

end LiebThirring

end
