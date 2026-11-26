/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.GM07.Section46UniqueLiftLimit
import LeanPool.GraphMinor.Surface.InvarianceOfDomain
import LeanPool.GraphMinor.GM07.Defs

/-!
# Small connected approaches in a closed disc

The lift of the open net disc in VII (4.6), page 226, is extended to
the boundary by a limit. In a closed disc each point has small open
neighbourhoods which meet the open disc in a convex set. So the part
of each such neighbourhood in the open disc is connected.
-/

public section

namespace GraphMinor.GM07

open Set Topology Metric GraphMinor.Surface

theorem closed_disc_connected_approach {D : Type*} [TopologicalSpace D]
    (e : ClosedUnitDisc ≃ₜ D) (x : D) (O : Set D) (hO : IsOpen O) (hx : x ∈ O) :
    ∃ W : Set D, IsOpen W ∧ x ∈ W ∧ W ⊆ O ∧ IsPreconnected (W ∩ (bd D)ᶜ) := by
  have hO' : IsOpen (e ⁻¹' O) := hO.preimage e.continuous
  obtain ⟨r, hr, hball⟩ := Metric.isOpen_iff.mp hO' (e.symm x) (by simpa using hx)
  have hbdD : bd D = e '' bd ClosedUnitDisc := (image_bd_homeomorph e).symm
  have hWeq : e '' ball (e.symm x) r ∩ (bd D)ᶜ =
      e '' (ball (e.symm x) r ∩ (bd ClosedUnitDisc)ᶜ) := by
    rw [hbdD, image_inter e.injective, image_compl_eq e.bijective]
  refine ⟨e '' ball (e.symm x) r, ?_, ⟨_, mem_ball_self hr, by simp⟩, ?_, ?_⟩
  · exact e.isOpenMap _ isOpen_ball
  · rintro _ ⟨y, hy, rfl⟩
    exact hball hy
  · rw [hWeq]
    apply IsPreconnected.image _ e e.continuous.continuousOn
    rw [Topology.IsInducing.subtypeVal.isPreconnected_image.symm]
    apply Convex.isPreconnected
    have hset : Subtype.val '' (ball (e.symm x) r ∩ (bd ClosedUnitDisc)ᶜ) =
        ball (e.symm x).1 r ∩ ball 0 1 := by
      ext z
      constructor
      · rintro ⟨y, ⟨hy, hyb⟩, rfl⟩
        refine ⟨hy, ?_⟩
        rw [bd_closedUnitDisc] at hyb
        have h1 : ‖y.1‖ ≤ 1 := by simpa [ClosedUnitDisc] using y.2
        have h2 : ‖y.1‖ ≠ 1 := fun h => hyb (by simpa [UnitCircle] using h)
        simpa using lt_of_le_of_ne h1 h2
      · rintro ⟨hz, hz1⟩
        have hzn : ‖z‖ < 1 := by simpa using hz1
        refine ⟨⟨z, by simpa [ClosedUnitDisc] using hzn.le⟩, ⟨hz, ?_⟩, rfl⟩
        rw [bd_closedUnitDisc]
        intro h
        have : ‖z‖ = 1 := by simpa [UnitCircle] using h
        exact hzn.ne this
    rw [hset]
    exact (convex_ball _ _).inter (convex_ball _ _)

end GraphMinor.GM07
