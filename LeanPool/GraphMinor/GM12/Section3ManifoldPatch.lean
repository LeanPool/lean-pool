/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.Cuffs
import LeanPool.GraphMinor.GM12.Section3ConvexPatch

/-!
# Simply connected patches at manifold points

The homotopy-preserving circle rerouting used in the Section 8 argument
for XII (3.1), page 245, needs small simply connected patches. Restrict
a half-plane chart to a ball about the chosen point. The intersection
of the ball and half-plane is convex. Mapping it back gives an open
simply connected neighbourhood, including at boundary points.
-/

public section

namespace GraphMinor.GM12

open Set Topology Metric Surface

/-- Every manifold point, including a boundary point, has an open
simply connected neighbourhood obtained from a convex half-plane patch. -/
theorem exists_simplyConnected_patch_of_isManifoldPoint
    {S : Type*} [TopologicalSpace S] {x : S} (hx : IsManifoldPoint x) :
    ∃ V : Set S, IsOpen V ∧ x ∈ V ∧ IsSimplyConnectedSet V := by
  obtain ⟨U, O, j, k, hU, hO, hxU, hj, hk, hm, hk', hl, hr⟩ := hx.exists_chart
  let z := j x
  have hz : z ∈ O ∩ halfPlane := hm hxU
  obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.mp hO z hz.1
  let A : Set ℂ := ball z δ ∩ halfPlane
  have hA : A ⊆ O ∩ halfPlane := fun _ hw => ⟨hball hw.1, hw.2⟩
  have himage : k '' A ⊆ U := by
    rintro y ⟨w, hw, rfl⟩
    exact hk' (hA hw)
  have hhalf : Convex ℝ halfPlane :=
    (convex_Ici (0 : ℝ)).linear_preimage Complex.reCLM.toLinearMap
  have hsimp : IsSimplyConnectedSet (k '' A) := image_convex_isSimplyConnected
    (hk.mono hA) (hj.mono himage) (fun w hw => hr (hA hw))
    ((convex_ball z δ).inter hhalf) ⟨mem_ball_self hδ, hz.2⟩
  have heq : k '' A = U ∩ j ⁻¹' ball z δ := by
    ext y
    constructor
    · rintro ⟨w, hw, rfl⟩
      refine ⟨hk' (hA hw), ?_⟩
      change j (k w) ∈ ball z δ
      rw [hr (hA hw)]
      exact hw.1
    · rintro ⟨hyU, hyball⟩
      exact ⟨j y, ⟨hyball, (hm hyU).2⟩, hl hyU⟩
  refine ⟨k '' A, ?_, ?_, hsimp⟩
  · rw [heq]
    exact hj.isOpen_inter_preimage hU isOpen_ball
  · exact ⟨z, ⟨mem_ball_self hδ, hz.2⟩, hl hxU⟩

end GraphMinor.GM12
