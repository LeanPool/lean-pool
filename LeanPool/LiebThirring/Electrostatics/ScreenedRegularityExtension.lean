/-
Copyright (c) 2026 Scott Armstrong, Amélie Loher. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Scott Armstrong, Amélie Loher
-/
module

-- Imported from upstream commit 8bf4656f07f5aaa227b0b850d77b16976915bbd4.
-- Imports adapted for Lean Pool.

public import Mathlib.Analysis.Calculus.BumpFunction.FiniteDimension
public import LeanPool.LiebThirring.Electrostatics.ScreenedRegularityCells

/-!
# Globally smooth extensions of screened cell representatives

Small inner bumps remove the retained Coulomb poles. Their transition balls
lie strictly outside the associated closed cell, so the extension agrees
with the cell representative on a neighborhood of each point of that cell.
-/

public section

open Filter Set
open scoped Topology ContDiff NNReal

namespace LiebThirring

/-- Smooth cutoff around a nuclear position for removing its Coulomb singularity. -/
@[expose] noncomputable def screenedInnerBump (c : Position) (d : ℝ) (hd : 0 < d) :
    ContDiffBump c := ⟨d / 8, d / 4, by positivity, by linarith⟩

/-- A smooth replacement of the inverse distance near a nuclear position. -/
@[expose] noncomputable def screenedSmoothInverse (c : Position) (d : ℝ) (hd : 0 < d)
    (x : Position) : ℝ := (1 - screenedInnerBump c d hd x) * ‖x - c‖⁻¹

theorem contDiff_screenedSmoothInverse (c : Position) (d : ℝ) (hd : 0 < d) :
    ContDiff ℝ ∞ (screenedSmoothInverse c d hd) := by
  rw [contDiff_iff_contDiffAt]
  intro x
  by_cases hx : x = c
  · subst x
    apply (contDiffAt_const : ContDiffAt ℝ ∞ (fun _ : Position => (0 : ℝ)) c).congr_of_eventuallyEq
    filter_upwards [(screenedInnerBump c d hd).eventuallyEq_one] with x hx
    simp only [screenedSmoothInverse, hx, Pi.one_apply, sub_self, zero_mul]
  · exact (contDiffAt_const.sub (screenedInnerBump c d hd).contDiffAt).mul
      (contDiffAt_inv_nuclear_distance c x hx ∞)

theorem eventuallyEq_screenedSmoothInverse (c x : Position) (d : ℝ) (hd : 0 < d)
    (hx : d / 4 < ‖x - c‖) :
    screenedSmoothInverse c d hd =ᶠ[𝓝 x] (fun y => ‖y - c‖⁻¹) := by
  have hn : ∀ᶠ y in 𝓝 x, d / 4 < ‖y - c‖ :=
    (isOpen_lt continuous_const (continuous_id.sub continuous_const).norm).mem_nhds hx
  filter_upwards [hn] with y hy
  have hz : screenedInnerBump c d hd y = 0 :=
    (screenedInnerBump c d hd).zero_of_le_dist (by
      simpa only [screenedInnerBump, dist_eq_norm] using hy.le)
  simp only [screenedSmoothInverse, hz, sub_zero, one_mul]

/-- Smooth extension of the screened potential from a closed Voronoi cell. -/
@[expose] noncomputable def screenedCellSmooth {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k : Fin M) (x : Position) : ℝ :=
  ∑ p : {p : Fin M // p ≠ k}, (Z : ℝ) *
    screenedSmoothInverse (R p.val) ‖R p.val - R k‖
      (norm_pos_iff.mpr (sub_ne_zero.mpr (hR.ne p.property))) x

theorem contDiff_screenedCellSmooth {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k : Fin M) :
    ContDiff ℝ ∞ (screenedCellSmooth Z R hR k) := by
  classical
  apply ContDiff.sum
  intro p _
  exact contDiff_const.mul (contDiff_screenedSmoothInverse _ _ _)

theorem eventuallyEq_screenedCellSmooth {M : ℕ} (Z : ℝ≥0)
    (R : Fin M → Position) (hR : Function.Injective R) (k : Fin M)
    {x : Position} (hx : x ∈ closedVoronoiCell R k) :
    screenedCellSmooth Z R hR k =ᶠ[𝓝 x] screenedCellPotential Z R k := by
  classical
  have he (p : {p : Fin M // p ≠ k}) :
      screenedSmoothInverse (R p.val) ‖R p.val - R k‖
        (norm_pos_iff.mpr (sub_ne_zero.mpr (hR.ne p.property))) =ᶠ[𝓝 x]
        (fun y => ‖y - R p.val‖⁻¹) := by
    apply eventuallyEq_screenedSmoothInverse
    have hs := nuclear_separation_le_twice_dist R k p.val hx
    have hp : 0 < ‖R p.val - R k‖ := norm_pos_iff.mpr (sub_ne_zero.mpr (hR.ne p.property))
    linarith only [hs, hp]
  filter_upwards [eventually_all.mpr he] with y hy
  unfold screenedCellSmooth screenedCellPotential
  simp_rw [hy]
  exact (Finset.sum_subtype (p := fun p : Fin M => p ≠ k) (Finset.univ.erase k)
    (by intro p; simp only [Finset.mem_erase, Finset.mem_univ, and_true])
    (fun p : Fin M => (Z : ℝ) * ‖y - R p‖⁻¹)).symm

end LiebThirring

end
