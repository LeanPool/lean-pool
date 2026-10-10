/-
Copyright (c) 2026 Bingqi Yu. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Bingqi Yu
-/

module

public import LeanPool.ArnoldKAM.Arnold1963.Geometry.Erosion
public import LeanPool.ArnoldKAM.Arnold1963.Analysis.MeanValue
public import Mathlib.Topology.Order.IntermediateValue
public import Mathlib.Analysis.Normed.Affine.AddTorsor
public import Mathlib.Tactic.Linarith

/-!
Coverage of eroded domains via continuous induction along a segment, allowing nonconvex
compact domains and proving the required boundary behavior from local inverses.
-/

@[expose] public section
noncomputable section
open Set Filter Metric AffineMap
open scoped Topology NNReal
namespace KamProject.Arnold1963

theorem mem_interior_of_local_inverse {n : ℕ}
    {A g : ComplexSpace n → ComplexSpace n} {G Ω : Set (ComplexSpace n)}
    {p : ComplexSpace n} (hA : ContinuousAt A p) (hg : MapsTo g Ω G)
    (hl : ∀ᶠ x in 𝓝 p, g (A x) = x) (hp : A p ∈ interior Ω) : p ∈ interior G := by
  apply mem_interior_iff_mem_nhds.mpr
  have hm : ∀ᶠ x in 𝓝 p, A x ∈ Ω := hA (mem_interior_iff_mem_nhds.mp hp)
  filter_upwards [hm, hl] with x hx he
  simpa only [he] using hg hx

theorem mem_erosion_of_image_buffer {n : ℕ}
    {A : ComplexSpace n → ComplexSpace n} {G Ω : Set (ComplexSpace n)}
    {C r : ℝ≥0} (hG : IsClosed G) (hC : 0 < C)
    (hA : AnalyticOnNhd ℂ A G) (hd : ∀ p ∈ G, ‖fderiv ℂ A p‖ ≤ C)
    (hback : ∀ p ∈ G, A p ∈ interior Ω → p ∈ interior G)
    {p : ComplexSpace n} (hp : p ∈ G) (hy : A p ∈ erosion Ω (C * r)) :
    p ∈ erosion G r := by
  by_cases hr : r = 0
  · simpa [hr] using hp
  have hrpos : (0 : ℝ) < r := NNReal.coe_pos.mpr (pos_iff_ne_zero.mpr hr)
  intro z hz
  let l : ℝ →ᵃ[ℝ] ComplexSpace n := lineMap p z
  have hl : Continuous l := lineMap_continuous
  have hzero : (0 : ℝ) ∈ l ⁻¹' G := by simpa [l] using hp
  have hall : Icc (0 : ℝ) 1 ⊆ l ⁻¹' G := by
    apply ((hG.preimage hl).inter isClosed_Icc).Icc_subset_of_forall_mem_nhdsGT_of_Icc_subset hzero
    intro t ht hprefix
    have hpt : l t ∈ G := hprefix ⟨ht.1, le_rfl⟩
    have hseg : segment ℝ p (l t) ⊆ G := by
      have himage : l '' Icc 0 t = segment ℝ p (l t) := by
        rw [← segment_eq_Icc ht.1, image_segment]
        simp [l]
      rw [← himage]
      exact image_subset_iff.mpr hprefix
    have hdist : dist (A (l t)) (A p) ≤ (C : ℝ) * dist (l t) p := by
      simpa only [dist_eq_norm] using norm_sub_le_of_analytic_segment_bound hseg hA
        (show NormBoundOn (fderiv ℂ A) G C from ⟨C.coe_nonneg, hd⟩)
    have hsmall : dist (l t) p < (r : ℝ) := by
      rw [show dist (l t) p = |t| * dist p z from dist_lineMap_left p z t,
        abs_of_nonneg ht.1]
      have hz' : dist p z ≤ (r : ℝ) := by simpa only [mem_closedBall, dist_comm] using hz
      exact (mul_le_mul_of_nonneg_left hz' ht.1).trans_lt
        (by nlinarith [ht.2])
    have hi : A (l t) ∈ interior Ω :=
      interior_mono hy (ball_subset_interior_closedBall
        (hdist.trans_lt (mul_lt_mul_of_pos_left hsmall (show (0 : ℝ) < C from hC))))
    exact nhdsWithin_le_nhds (hl.continuousAt
      (mem_interior_iff_mem_nhds.mp (hback _ hpt hi)))
  simpa [l] using hall (show (1 : ℝ) ∈ Icc (0 : ℝ) 1 by simp)

end KamProject.Arnold1963
