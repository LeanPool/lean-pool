/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM11.Defs
import LeanPool.GraphMinor.GM11.PaintingRegions
import LeanPool.GraphMinor.GM11.DrawingConnectivity

/-!
# Paths in a drawing whose regions are discs

The path chosen in XII (4.3), page 249, exists because the surface is connected and all
regions are open discs. The closed-split criterion gives preconnectedness of the drawing.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- The walk-existence step in XII (4.3), page 249. -/
theorem exists_walk_of_open_disc_regions
    {S : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S]
    (hS : IsClosedSurface S) {D : Drawing S} (hD : ∀ r ∈ D.R, IsOpenDisc r)
    {a b : S} (ha : a ∈ D.V) (hb : b ∈ D.V) : Nonempty (GraphWalk D.toGraph a b) := by
  classical
  apply drawing_walk_of_isPreconnected_U (a := a) (b := b) ?_ ha hb
  apply isPreconnected_closed_iff.mpr
  intro C₁ C₂ hc₁ hc₂ hcover hne₁ hne₂
  by_contra hn
  have hdis : Disjoint (D.U ∩ C₁) (D.U ∩ C₂) := by
    apply disjoint_left.mpr
    intro x hx hy
    exact hn ⟨x, hx.1, hx.2, hy.2⟩
  have heq : (D.U ∩ C₁) ∪ (D.U ∩ C₂) = D.U := by
    apply subset_antisymm (union_subset inter_subset_left inter_subset_left)
    intro x hx
    exact (hcover hx).elim (fun h => Or.inl ⟨hx, h⟩) (fun h => Or.inr ⟨hx, h⟩)
  have hempty := eq_empty_of_split hS hD (D.isClosed_U.inter hc₁)
    (D.isClosed_U.inter hc₂) hdis heq hne₁
  exact hne₂.ne_empty hempty

end GraphMinor.GM12
