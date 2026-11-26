/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar
import LeanPool.GraphMinor.GM12.Section4DiscEnlargement
import LeanPool.GraphMinor.GM12.Section4RadialResize
import LeanPool.GraphMinor.Surface.PushOff

/-!
# Compressing a disc inside an assigned neighborhood

For XII (4.3), claim (7), page 251, a source disc can be made small
before it is moved into its assigned target disc. Give the source a
collar avoiding the protected closed set. A radial change inside the
collar compresses the disc into any neighborhood of its center and
fixes the protected set pointwise.
-/

public section

namespace GraphMinor.GM12

open Set Surface Metric Topology

/-- A disc disjoint from a closed protected set has a center about
which it can be compressed into any open neighborhood. -/
theorem exists_disc_compression_center
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) {D B : Set S} (hD : IsClosedDisc D)
    (hB : IsClosed B) (hDB : Disjoint D B) :
    ∃ p ∈ D, ∀ U : Set S, IsOpen U → p ∈ U →
      ∃ e : S ≃ₜ S, e '' D ⊆ U ∧ e p = p ∧ ∀ x ∈ B, e x = x := by
  obtain ⟨E, hE, hDE, hEB⟩ := exists_disc_enlargement_avoiding hS hD hB hDB
  obtain ⟨pD⟩ := hD.isOArc_discBd
  obtain ⟨c, c', hcc, hcc', hcm, hcm', hl, hr, hc1, hc2, _⟩ :=
    exists_disc_collar hD hE hDE pD
  have hzero : (0 : ℂ) ∈ closedBall 0 1 := by simp
  have hpD : c 0 ∈ D := hc1 ▸ mem_image_of_mem c hzero
  refine ⟨c 0, hpD, ?_⟩
  intro U hU hpU
  have hc0 : ContinuousAt c 0 := hcc.continuousAt (closedBall_mem_nhds _ (by norm_num))
  obtain ⟨ε, hε, hεU⟩ := Metric.mem_nhds_iff.mp (hc0.preimage_mem_nhds (hU.mem_nhds hpU))
  let w := min (ε / 2) (1 / 2 : ℝ)
  have hw : 0 < w := lt_min (half_pos hε) (by norm_num)
  have hwε : w < ε := (min_le_left _ _).trans_lt (by linarith)
  have hwt : w < (3 / 2 : ℝ) := (min_le_right _ _).trans_lt (by norm_num)
  obtain ⟨Θ, hΘfix, hΘnorm, hΘball⟩ := exists_radial_disc_resize
    (show (0 : ℝ) < 1 by norm_num) (show (1 : ℝ) < 3 / 2 by norm_num) hw hwt
  obtain ⟨e, hec, hefix⟩ := exists_homeomorph_of_collar
    (fun x => (hS.2.2 x).isManifoldPoint) hE hcc hcc' hcm hcm' hl hr hc2 Θ hΘfix
  refine ⟨e, ?_, ?_, ?_⟩
  · rintro _ ⟨x, hxD, rfl⟩
    obtain ⟨z, hz, rfl⟩ := hc1.symm ▸ hxD
    rw [hec z (closedBall_subset_closedBall (by norm_num) hz)]
    apply hεU
    have hzw : Θ z ∈ closedBall 0 w := hΘball ▸ mem_image_of_mem Θ hz
    rw [mem_ball_zero_iff]
    exact (mem_closedBall_zero_iff.mp hzw).trans_lt hwε
  · have hΘzero : Θ 0 = 0 := by
      apply norm_eq_zero.mp
      rw [hΘnorm, norm_zero, tentMap, tent_low (by norm_num) (by norm_num) le_rfl,
        mul_zero, add_zero]
    rw [hec 0 (by simp), hΘzero]
  · intro x hx
    exact hefix x (fun hxE => Set.disjoint_left.mp hEB hxE hx)

end GraphMinor.GM12
