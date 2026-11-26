/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CirclePairGraph
import LeanPool.GraphMinor.GM12.Section3BridgeSeparation
import LeanPool.GraphMinor.GM11.RadialBasics
import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# Circles inside the first two-loop shape

In the Section 8 argument used by XII (3.1), page 245, the joining
edge of the first two-loop shape is a bridge. The finite-graph edge-or
lemma says that a circle either contains that edge or misses its open
part. Containing it contradicts connectedness after deleting the
midpoint. A circle missing its open part lies in the disjoint union
of the two original circles and hence in one of them.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Every circle in the first two-loop shape is contained in one of
its two original circles. The joining line cannot belong to a circle. -/
theorem oArc_subset_disjoint_circle_or
    {S : Type*} [TopologicalSpace S] [T2Space S] {F A P Z : Set S} {a b : S}
    (hF : IsOArc F) (hA : IsOArc A) (hdis : Disjoint F A)
    (hP : IsLineWithEnds P a b) (ha : a ∈ F) (hb : b ∈ A)
    (hPF : P ∩ F = {a}) (hPA : P ∩ A = {b})
    (hZ : IsOArc Z) (hZY : Z ⊆ F ∪ A ∪ P) : Z ⊆ F ∨ Z ⊆ A := by
  have hFc : IsClosed F := hF.isCompact.isClosed
  have hAc : IsClosed A := hA.isCompact.isClosed
  have hnoP : ¬ P ⊆ Z := by
    intro hPZ
    obtain ⟨p, U, V, hUc, hVc, hcover, hinter, haU, haV, hbV, hbU⟩ :=
      exists_closed_separation_of_joining_line hF hA hdis hP ha hb hPF hPA
    have hp : p ∈ U ∩ V := hinter.symm ▸ mem_singleton p
    have haZ : a ∈ Z \ {p} :=
      ⟨hPZ hP.left_mem, fun hap => haV (hap.symm ▸ hp.2)⟩
    have hbZ : b ∈ Z \ {p} :=
      ⟨hPZ hP.right_mem, fun hbp => hbU (hbp.symm ▸ hp.1)⟩
    have hsub : Z \ {p} ⊆ U ∪ V := by
      intro x hx
      rw [hcover]
      exact hZY hx.1
    have hmiss : ∀ x ∈ Z \ {p}, x ∈ U → x ∉ V := by
      intro x hx hxU hxV
      exact hx.2 (hinter ▸ (show x ∈ U ∩ V from ⟨hxU, hxV⟩))
    rcases subset_or_subset_of_closed (hZ.twoConn p) hUc hVc hsub hmiss with hZU | hZV
    · exact hbU (hZU hbZ)
    · exact haV (hZV haZ)
  obtain ⟨V, E, hG, hgr, hPE, hPV⟩ :=
    exists_graph_of_disjoint_circles_with_joining_line hF hA hdis hP ha hb hPF hPA
  have hZG : Z ⊆ gr V E := hZY.trans hgr.symm.le
  have hgap : Disjoint (P \ V) Z := (hG.edge_or hZ hZG hPE).resolve_left hnoP
  have hZA : Z ⊆ F ∪ A := by
    intro x hxZ
    rcases hZY hxZ with hxFA | hxP
    · exact hxFA
    · by_cases hxFA : x ∈ F ∪ A
      · exact hxFA
      · have hxV : x ∉ V := by
          intro hxV
          have hx : x ∈ P ∩ V := ⟨hxP, hxV⟩
          rw [hPV] at hx
          rcases hx with hxa | hxb
          · exact hxFA (Or.inl (hxa.symm ▸ ha))
          · exact hxFA (Or.inr (hxb.symm ▸ hb))
        exact False.elim (Set.disjoint_left.mp hgap ⟨hxP, hxV⟩ hxZ)
  exact subset_or_subset_of_closed hZ.isPreconnected hFc hAc hZA
    (fun x _ hxF hxA => Set.disjoint_left.mp hdis hxF hxA)

end GraphMinor.GM12
