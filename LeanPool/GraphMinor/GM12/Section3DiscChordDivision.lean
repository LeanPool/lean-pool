/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3DivisionArcCount
import LeanPool.GraphMinor.GM06.Section3Dual
import LeanPool.GraphMinor.Surface.DiscGrow
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# The division-count form of the normal-chord inequality

For VI (3.6) in the one-disc case of XII (3.2), pages 247--248,
split the boundary circle into its two arcs between the chord ends.
Every counted division part meets each arc, so the division count
is at most both arc vertex counts. The proved minimum-arc chord
inequality then bounds it by the chord vertex count.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM06

/-- The minimum-arc chord inequality gives the division-count chord
bound used in the VI (3.6) application in XII (3.2). -/
theorem divisionCount_le_of_normal_chord_min_bound
    {S : Type*} [TopologicalSpace S] (G : Drawing S) (hDisc : IsClosedDiscSpace S)
    {Δ : Set (Set S)} (hΔ : IsDivision Δ) (hUnion : divisionUnion Δ = G.V ∩ bd S)
    (hmin : ∀ (x y : S) (A B P : Set S), IsLineWithEnds A x y → IsLineWithEnds B x y →
      IsLineWithEnds P x y → A ∩ B = {x, y} → A ∩ P = {x, y} → B ∩ P = {x, y} →
      bd S = A ∪ B → P ∩ bd S = {x, y} → G.IsNormal P →
        min (G.V ∩ A).ncard (G.V ∩ B).ncard ≤ (G.V ∩ P).ncard)
    {x y : S} (hx : x ∈ bd S) (hy : y ∈ bd S) (hxy : x ≠ y)
    (P : Set S) (hP : IsLineWithEnds P x y) (hcap : P ∩ bd S = {x, y}) (hn : G.IsNormal P) :
    divisionCount (bd S) Δ x y ≤ (G.V ∩ P).ncard := by
  let : T2Space S := GM06.t2Space_of_isClosedDiscSpace hDisc
  obtain ⟨a, b, hab, ha0, ha1, hrange⟩ := hDisc.isOArc_bd.exists_arcs hx hy hxy
  have hb0 : b 0 = x := hab.3.trans ha0
  have hb1 : b 1 = y := hab.4.trans ha1
  have hA : IsLineWithEnds (range a) x y := by
    simpa only [ha0, ha1] using hab.1.isLineWithEnds
  have hB : IsLineWithEnds (range b) x y := by
    simpa only [hb0, hb1] using hab.2.isLineWithEnds
  have hAB : range a ∩ range b = {x, y} := by simpa only [ha0, ha1] using hab.inter
  have hAbd : range a ⊆ bd S := subset_union_left.trans hrange.subset
  have hBbd : range b ⊆ bd S := subset_union_right.trans hrange.subset
  have hAP : range a ∩ P = {x, y} := by
    apply Subset.antisymm
    · exact fun z hz => hcap.subset ⟨hz.2, hAbd hz.1⟩
    · intro z hz
      rcases hz with rfl | rfl
      · exact ⟨⟨0, ha0⟩, (hcap.symm.subset (Or.inl rfl)).1⟩
      · exact ⟨⟨1, ha1⟩, (hcap.symm.subset (Or.inr rfl)).1⟩
  have hBP : range b ∩ P = {x, y} := by
    apply Subset.antisymm
    · exact fun z hz => hcap.subset ⟨hz.2, hBbd hz.1⟩
    · intro z hz
      rcases hz with rfl | rfl
      · exact ⟨⟨0, hb0⟩, (hcap.symm.subset (Or.inl rfl)).1⟩
      · exact ⟨⟨1, hb1⟩, (hcap.symm.subset (Or.inr rfl)).1⟩
  have hC : IsOArc (range a ∪ range b) := hrange.symm ▸ hDisc.isOArc_bd
  have hU : divisionUnion Δ ⊆ G.V := hUnion.subset.trans inter_subset_left
  have hcountA := divisionCount_le_boundary_arc_count G.finite_V hΔ hU hC hA hB
  have hcountB := divisionCount_le_boundary_arc_count G.finite_V hΔ hU
    ((union_comm (range a) (range b)) ▸ hC) hB hA
  rw [hrange] at hcountA
  rw [union_comm (range b) (range a), hrange] at hcountB
  exact (le_min hcountA hcountB).trans
    (hmin x y (range a) (range b) P hA hB hP hAB hAP hBP hrange.symm hcap hn)

end GraphMinor.GM12
