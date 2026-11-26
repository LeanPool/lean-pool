/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Section46LongEdges
public import LeanPool.GraphMinor.GM11.Rotation
import LeanPool.GraphMinor.GM07.Section46EdgeSegments
import LeanPool.GraphMinor.GM07.Section46WIntersections

/-!
# The ends of central edges

For `K` in VII (4.6), pages 225–226, the central edge on a long old
edge has exactly the two ends `W(e)`. Its closed parameter interval
lies inside that old edge, so it contains no old seam vertex and no
cut point belonging to another old edge.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface GraphMinor.GM11

/-- The two ends of a central edge in `J⁺` are precisely `W(e)`,
in VII (4.6), pages 225–226. -/
theorem central_edge_ends {S : Type*} [TopologicalSpace S] [T2Space S]
    {G J J' : Drawing S} {γ : Set S → unitInterval → S} (hγ : EdgePar J γ)
    {μ w : ℕ} (W : longSeamEdges G J μ w → Set S) (hW : ∀ f, W f ⊆ f.1)
    (hV : J'.V = J.V ∪ ⋃ f, W f) (e : longSeamEdges G J μ w)
    {s t : unitInterval} (hs : s ∈ Ioo 0 1) (ht : t ∈ Ioo 0 1) (hst : s < t)
    (hWe : W e = {γ e.1 s, γ e.1 t}) :
    closure (γ e.1 '' Ioo s t) ∩ J'.V = W e := by
  rw [closure_image_Ioo_eq_Icc hγ e.2.1 hst (.inl hs.1), hV]
  apply Subset.antisymm
  · rintro x ⟨⟨u, hu, rfl⟩, hxV⟩
    have hu' : u ∈ Ioo (0 : unitInterval) 1 := ⟨hs.1.trans_le hu.1, hu.2.trans_lt ht.2⟩
    have hxE : γ e.1 u ∈ e.1 :=
      (congrArg (fun A => γ e.1 u ∈ A) (hγ.image e.1 e.2.1)).mp ⟨u, hu', rfl⟩
    rcases hxV with hxold | hxW
    · exact ((e.2.1.2.1 hxE).2 hxold).elim
    · have hx : γ e.1 u ∈ (⋃ f, W f) ∩ closure e.1 := ⟨hxW, subset_closure hxE⟩
      exact (W_inter_closed_long_edge W hW e) ▸ hx
  · intro x hx
    have hxW : x ∈ ⋃ f, W f := mem_iUnion.mpr ⟨e, hx⟩
    refine ⟨?_, .inr hxW⟩
    rw [hWe] at hx
    rcases hx with rfl | rfl
    · exact ⟨s, ⟨le_rfl, hst.le⟩, rfl⟩
    · exact ⟨t, ⟨hst.le, le_rfl⟩, rfl⟩

end GraphMinor.GM07
