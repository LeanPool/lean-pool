/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM07.Defs
import LeanPool.GraphMinor.GM07.Section46EdgeLift
import LeanPool.GraphMinor.Surface.ChartCells
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# A lifted edge has one incidence over each of its ends

The first-edge count in VII (4.6), page 225, assigns each indexed path to
a point over its initial vertex. We identify the closure of the preimage
of its open first edge with the lifted closed line. Injectivity on that
line then gives a unique incidence over each end.
-/

public section

namespace GraphMinor.GM07

open Set GraphMinor.Surface

universe u

/-- The preimage of a non-loop edge has a unique incidence over each end,
as used in choosing `l(z)` in VII (4.6), page 225. -/
theorem Net.exists_unique_lifted_edge_end {S : Type u} [TopologicalSpace S]
    (hS : IsSurface S) (N : Net S) {G J : Drawing S}
    (hJ : N.IsSeamGraphFor J) (hnorm : G.IsNormal J.U)
    {e : Set S} (he : e ∈ G.E) {a b : S}
    (hends : closure e ∩ G.V = {a, b}) (hline : IsLineWithEnds (closure e) a b) :
    ∃ a' : N.D, N.φ a' = a ∧ a' ∈ closure (N.φ ⁻¹' e) ∧
      ∀ x ∈ closure (N.φ ⁻¹' e), N.φ x = a → x = a' := by
  have : T2Space S := hS.2.1
  have : T2Space N.D := N.isSurface_D.2.1
  obtain ⟨L, a', b', hL, ha, hb, him, hinj, hcover⟩ :=
    N.exists_lift_closed_normal_edge hS hJ hnorm he hends hline
  have haV : a ∈ G.V := (hends ▸ (mem_insert a {b}) : a ∈ closure e ∩ G.V).2
  have hbV : b ∈ G.V := (hends ▸ (mem_insert_of_mem a (mem_singleton b)) : b ∈ closure e ∩ G.V).2
  have heq : N.φ ⁻¹' e = L \ {a', b'} := by
    apply Subset.antisymm
    · intro x hx
      have hxcl : N.φ x ∈ closure e := subset_closure hx
      have hxV : N.φ x ∉ G.V := by
        have hx' : N.φ x ∈ closure e \ G.V := by
          rw [G.closure_diff_V he]
          exact hx
        exact hx'.2
      have hxab : N.φ x ∉ ({a, b} : Set S) := by
        rintro (h | h)
        · exact hxV (h ▸ haV)
        · exact hxV (h ▸ hbV)
      refine ⟨hcover x ⟨hxcl, hxab⟩, ?_⟩
      rintro (rfl | rfl)
      · exact hxV (ha ▸ haV)
      · exact hxV (hb ▸ hbV)
    · intro x hx
      have hxcl : N.φ x ∈ closure e := him ▸ mem_image_of_mem N.φ hx.1
      have hxV : N.φ x ∉ G.V := by
        intro hxV
        have hxends : N.φ x ∈ ({a, b} : Set S) := hends ▸ ⟨hxcl, hxV⟩
        rcases hxends with hxend | hxend
        · exact hx.2 (.inl (hinj hx.1 hL.left_mem (hxend.trans ha.symm)))
        · exact hx.2 (.inr (hinj hx.1 hL.right_mem (hxend.trans hb.symm)))
      exact G.closure_diff_V he ▸ ⟨hxcl, hxV⟩
  have hcl : closure (N.φ ⁻¹' e) = L := by
    rw [heq]
    exact Subset.antisymm (closure_minimal sdiff_subset hL.isCompact.isClosed)
      hL.subset_closure_diff
  refine ⟨a', ha, hcl ▸ hL.left_mem, ?_⟩
  intro x hx hxa
  exact hinj (hcl ▸ hx) hL.left_mem (hxa.trans ha.symm)

end GraphMinor.GM07
