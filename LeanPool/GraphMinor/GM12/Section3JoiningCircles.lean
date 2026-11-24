/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3SolidConnections
import LeanPool.GraphMinor.GM12.Section2ChordGap
import LeanPool.GraphMinor.Surface.DiscMerge
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# A joining line between disjoint circles

In the Section 8 argument of VII used in XII (3.1), page 245, two
disjoint circles in the connected solid set can be joined by a line.
Take the first hit of the second circle and the last preceding hit
of the first. The resulting subline meets either circle only at its
corresponding endpoint, giving the first two-loop shape.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- Two disjoint circles in an arc-connected set have a joining line
whose only contacts with them are its two ends. -/
theorem exists_joining_line_between_disjoint_circles
    {S : Type*} [TopologicalSpace S] [T2Space S] {X A B : Set S}
    (hX : IsArcConnected X) (hA : IsOArc A) (hB : IsOArc B)
    (hAX : A ⊆ X) (hBX : B ⊆ X) (hdis : Disjoint A B) :
    ∃ (P : Set S) (a b : S), IsLineWithEnds P a b ∧ P ⊆ X ∧ a ∈ A ∧ b ∈ B ∧
      a ≠ b ∧ P ∩ A = {a} ∧ P ∩ B = {b} := by
  have hAc : IsClosed A := hA.isCompact.isClosed
  have hBc : IsClosed B := hB.isCompact.isClosed
  obtain ⟨φA⟩ := hA
  obtain ⟨φB⟩ := hB
  let a₀ := (φA 1).val
  let b₀ := (φB 1).val
  have ha₀ : a₀ ∈ A := (φA 1).property
  have hb₀ : b₀ ∈ B := (φB 1).property
  have hab₀ : a₀ ≠ b₀ := fun he => Set.disjoint_left.mp hdis ha₀ (he.symm ▸ hb₀)
  obtain ⟨L, hLX, φ, hφ0, hφ1⟩ := hX a₀ (hAX ha₀) b₀ (hBX hb₀) hab₀
  let g : unitInterval → S := fun t => (φ t).val
  have hgc : Continuous g := continuous_subtype_val.comp φ.continuous
  have hgi : Function.Injective g := fun t s he => φ.injective (Subtype.ext he)
  have hgX : range g ⊆ X := by
    rintro x ⟨t, rfl⟩
    exact hLX (φ t).property
  have h0 : g 0 ∈ A := by change (φ 0).val ∈ A; rw [hφ0]; exact ha₀
  have h1 : g 1 ∈ B := by change (φ 1).val ∈ B; rw [hφ1]; exact hb₀
  obtain ⟨P, a, b, hP, hPX, ha, hb, hab, hgap⟩ := exists_minimal_region_chord hgc hgi hgX
    (F := A ∪ B) inter_subset_left (hAc.preimage hgc)
    (hBc.preimage hgc) hdis h0 h1
  refine ⟨P, a, b, hP, hPX, ha, hb, hab, ?_, ?_⟩
  · apply Subset.antisymm
    · rintro x ⟨hxP, hxA⟩
      by_cases hxa : x = a
      · exact hxa
      · have hxb : x ≠ b := by
          intro he
          exact Set.disjoint_left.mp hdis hxA (he.symm ▸ hb)
        exact False.elim (Set.disjoint_left.mp hgap ⟨hxP, fun hx => hx.elim hxa hxb⟩ (Or.inl hxA))
    · intro x hx
      have hxa : x = a := hx
      rw [hxa]
      exact ⟨hP.left_mem, ha⟩
  · apply Subset.antisymm
    · rintro x ⟨hxP, hxB⟩
      by_cases hxb : x = b
      · exact hxb
      · have hxa : x ≠ a := by
          intro he
          exact Set.disjoint_left.mp hdis (he.symm ▸ ha) hxB
        exact False.elim (Set.disjoint_left.mp hgap ⟨hxP, fun hx => hx.elim hxa hxb⟩ (Or.inr hxB))
    · intro x hx
      have hxb : x = b := hx
      rw [hxb]
      exact ⟨hP.right_mem, hb⟩

end GraphMinor.GM12
