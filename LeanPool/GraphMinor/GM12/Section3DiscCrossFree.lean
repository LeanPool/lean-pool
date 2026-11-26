/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3FeasibilityDiscs
public import LeanPool.GraphMinor.GM06.Defs
import LeanPool.GraphMinor.GM06.Section3Dual
import LeanPool.GraphMinor.Surface.Disc
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs

/-!
# Topological feasibility gives a cross-free disc partition

For the application of VI (3.6) in XII (3.2), page 247, read the
topological feasibility discs in the complementary closed disc.
If two partition parts cross on its boundary, their feasibility
discs meet by the disc-crossing theorem. Their prescribed
disjointness excludes this. Thus the partition is cross-free.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM06

/-- Disjoint closed discs containing the partition parts exclude
crossing parts on the boundary of a closed disc space. -/
theorem isCrossFree_of_disjoint_enclosing_discs
    {S : Type*} [TopologicalSpace S] {p : ℕ} (hDisc : IsClosedDiscSpace S)
    (Zs D : Fin p → Set S) (hD : ∀ j, IsClosedDisc (D j))
    (hdis : ∀ i j, i ≠ j → Disjoint (D i) (D j)) (hZ : ∀ j, Zs j ⊆ D j) :
    GM06.IsCrossFree (bd S) (range Zs) := by
  rintro ⟨δ, hδ, δ', hδ', hne, a, ha, c, hc, b, hb, d, hd, hcross⟩
  obtain ⟨i, rfl⟩ := hδ
  obtain ⟨j, rfl⟩ := hδ'
  have hij : i ≠ j := fun h => hne (congrArg Zs h)
  have hmeet := GM06.discCrossing_of_isClosedDiscSpace hDisc
    (hD i).isCompact (hD j).isCompact
    (hD i).isPathConnected.isConnected (hD j).isPathConnected.isConnected
    (hZ i ha) (hZ i hc) (hZ j hb) (hZ j hd) hcross
  obtain ⟨x, hxi, hxj⟩ := hmeet
  exact Set.disjoint_left.mp (hdis i j hij) hxi hxj

/-- The topological feasibility condition of XII (3.2) gives the
cross-free hypothesis of VI (3.6) when the punctured surface is a
closed disc. -/
theorem isCrossFree_of_topological_feasible_in_discComplement
    {S : Type*} [TopologicalSpace S] [T2Space S] {t p : ℕ}
    (hS : IsClosedSurface S) (Δ : Fin t → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdis : Pairwise (fun i j => Disjoint (Δ i) (Δ j))) (Zs : Fin p → Set S)
    (hZ : ∀ j, Zs j ⊆ ⋃ i, discBd (Δ i)) (hfeasible : IsTopologicallyFeasible Δ Zs)
    (hDisc : GM06.IsClosedDiscSpace (discComplement Δ)) :
    GM06.IsCrossFree (bd (discComplement Δ))
      (range (fun j => (Subtype.val : discComplement Δ → S) ⁻¹' Zs j)) := by
  obtain ⟨D, hD, hDD, hcontact⟩ := hfeasible
  have hDC : ∀ j, D j ⊆ discComplement Δ := fun j =>
    feasibility_disc_subset_discComplement hS Δ hΔ hdis (hcontact j) (hZ j)
  apply isCrossFree_of_disjoint_enclosing_discs hDisc _
    (fun j => (Subtype.val : discComplement Δ → S) ⁻¹' D j)
    (fun j => (isClosedDisc_subtype_preimage (hDC j) (hD j)).1)
  · intro i j hij
    exact (hDD i j hij).preimage Subtype.val
  · intro j x hx
    exact ((hcontact j).symm.subset hx).1

end GraphMinor.GM12
