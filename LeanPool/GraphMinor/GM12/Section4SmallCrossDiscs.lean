/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section4DistinctCrossDirections
public import LeanPool.GraphMinor.Surface.Cap

/-!
# Small discs in crossing coordinates

In XII (4.5), page 253, a small disc is chosen around each
crossing. A translated real-linear coordinate change sends
small round discs to closed discs inside any prescribed open
neighborhood. Their boundaries are the images of the circles,
and the two coordinate lines map to the crossing lines.
-/

public section

namespace GraphMinor.GM12

open Set Metric Topology

/-- A translated real-linear equivalence takes the line through
two points to the line through their images. -/
theorem image_line_cross_coordinates (A : ℂ ≃L[ℝ] ℂ) (x a b : ℂ) :
    (fun z => x + A z) '' (line[ℝ, a, b] : Set ℂ) =
      (line[ℝ, x + A a, x + A b] : Set ℂ) := by
  let f : ℂ ≃ᵃ[ℝ] ℂ := A.toLinearEquiv.toAffineEquiv.trans
    (AffineEquiv.constVAdd ℝ ℂ x)
  have h := congrArg (fun s : AffineSubspace ℝ ℂ => (s : Set ℂ))
    (AffineSubspace.map_span (f : ℂ →ᵃ[ℝ] ℂ) ({a, b} : Set ℂ))
  rw [AffineSubspace.coe_map, image_pair] at h
  exact h

/-- The centre lies in the interior of every positive-radius
coordinate crossing disc. This keeps crossings out of the
residual edge halves in XII (4.5), page 253. -/
theorem cross_disc_center_mem_interior (A : ℂ ≃L[ℝ] ℂ) (x : ℂ)
    {r : ℝ} (hr : 0 < r) :
    x ∈ interior ((fun z => x + A z) '' closedBall 0 r) := by
  let h : ℂ ≃ₜ ℂ := A.toHomeomorph.trans (Homeomorph.addLeft x)
  have h0 : h 0 = x := by simp [h]
  apply mem_interior.mpr
  refine ⟨h '' ball 0 r, image_mono ball_subset_closedBall, h.isOpenMap _ isOpen_ball, ?_⟩
  exact ⟨0, mem_ball_self hr, h0⟩

/-- Crossing coordinates give arbitrarily small closed discs,
with the expected boundary circle. The neighborhood is any
open set containing the crossing, so finitely many such choices
can be made within disjoint neighborhoods. -/
theorem exists_small_cross_disc (A : ℂ ≃L[ℝ] ℂ) (x : ℂ)
    {U : Set ℂ} (hU : IsOpen U) (hx : x ∈ U) :
    ∃ r : ℝ, 0 < r ∧
      Surface.IsClosedDisc ((fun z => x + A z) '' closedBall 0 r) ∧
      Surface.discBd ((fun z => x + A z) '' closedBall 0 r) =
        (fun z => x + A z) '' sphere 0 r ∧
      (fun z => x + A z) '' closedBall 0 r ⊆ U := by
  let h : ℂ ≃ₜ ℂ := A.toHomeomorph.trans (Homeomorph.addLeft x)
  have h0 : h 0 = x := by simp [h]
  have hopen : IsOpen (h ⁻¹' U) := hU.preimage h.continuous
  obtain ⟨ε, hε, hball⟩ := Metric.isOpen_iff.mp hopen 0 (by simpa only [mem_preimage, h0] using hx)
  let r := ε / 2
  have hr : 0 < r := half_pos hε
  have hD : Surface.IsClosedDisc (closedBall (0 : ℂ) r) ∧
      Surface.discBd (closedBall (0 : ℂ) r) = sphere 0 r := by
    have hi : interior (closedBall (0 : ℂ) r) = ball 0 r := interior_closedBall _ (ne_of_gt hr)
    obtain ⟨hdisc, hbd⟩ := Surface.isClosedDisc_of_convex (convex_closedBall (0 : ℂ) r)
      (by rw [hi]; exact ⟨0, mem_ball_self hr⟩)
      (isBounded_closedBall) isClosed_closedBall
    refine ⟨hdisc, hbd.trans ?_⟩
    exact frontier_closedBall _ (ne_of_gt hr)
  obtain ⟨hd, hb⟩ := hD.1.image h.continuous.continuousOn h.symm.continuous.continuousOn
    (fun z _ => h.symm_apply_apply z)
  refine ⟨r, hr, hd, ?_, ?_⟩
  · exact hb.trans (congrArg (fun s : Set ℂ => h '' s) hD.2)
  · rintro _ ⟨z, hz, rfl⟩
    apply hball
    exact (closedBall_subset_ball (by dsimp [r]; exact half_lt_self hε)) hz

end GraphMinor.GM12
