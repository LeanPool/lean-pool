/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section2ArcComponents
public import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Cutting a disc along a chord with prescribed boundary arcs

In Case 2 of XII (2.1), page 244, the three lines of a theta graph
bound three circles. If one line lies in the disc bounded by the other
two, the disc-cutting theorem gives two subdiscs. Identifying the two
components of the punctured boundary identifies their boundaries.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem line_interior_nonempty {S : Type*} [TopologicalSpace S]
    {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) : (L \ {a, b}).Nonempty :=
  Surface.IsLineWithEnds.nonempty_sdiff hL

private theorem remove_ends_union {S : Type*} {A L F : Set S} (hF : F ⊆ L) :
    (A \ F) ∪ L = A ∪ L := by
  ext x
  constructor
  · rintro (hx | hx)
    · exact Or.inl hx.1
    · exact Or.inr hx
  · rintro (hx | hx)
    · by_cases hxF : x ∈ F
      · exact Or.inr (hF hxF)
      · exact Or.inl ⟨hx, hxF⟩
    · exact Or.inr hx

/-- Cutting a disc along a line joining the common ends of its two
boundary arcs gives subdiscs bounded by that line and each boundary arc. -/
theorem disc_split_with_boundary_arcs {S : Type*} [TopologicalSpace S] [T2Space S]
    {D L A B : Set S} {a b : S} (hD : IsClosedDisc D)
    (hL : IsLineWithEnds L a b) (hA : IsLineWithEnds A a b) (hB : IsLineWithEnds B a b)
    (hAB : A ∩ B = {a, b}) (hLA : L ∩ A = {a, b}) (hLB : L ∩ B = {a, b})
    (hbd : discBd D = A ∪ B) (hLD : L ⊆ D) (hab : a ≠ b) :
    ∃ E₁ E₂ : Set S, IsClosedDisc E₁ ∧ IsClosedDisc E₂ ∧ E₁ ∪ E₂ = D ∧
      discBd E₁ = A ∪ L ∧ discBd E₂ = B ∪ L := by
  have hcap : L ∩ discBd D = {a, b} := by
    rw [hbd, inter_union_distrib_left, hLA, hLB, union_self]
  obtain ⟨C₁, C₂, E₁, E₂, _, hcomponents, hE₁, hE₂, hU, _, hb₁, hb₂, _⟩ :=
    disc_iArc D L a b hD hLD hab hL hcap
  have hcomp : componentsIn (discBd D \ {a, b}) = {A \ {a, b}, B \ {a, b}} := by
    rw [hbd]
    exact componentsIn_union_sdiff hA.isCompact.isClosed hB.isCompact.isClosed hAB.subset
      (GraphMinor.GM11.IsLineWithEnds.isPreconnected_sdiff_pair hA)
      (GraphMinor.GM11.IsLineWithEnds.isPreconnected_sdiff_pair hB)
      (line_interior_nonempty hA) (line_interior_nonempty hB)
  have hend : ({a, b} : Set S) ⊆ L := by
    intro x hx
    exact (hLA.symm ▸ hx).1
  have hpair : ({C₁, C₂} : Set (Set S)) = {A \ {a, b}, B \ {a, b}} :=
    hcomponents.symm.trans hcomp
  rcases Set.pair_eq_pair_iff.mp hpair with ⟨h₁, h₂⟩ | ⟨h₁, h₂⟩
  · exact ⟨E₁, E₂, hE₁, hE₂, hU,
      hb₁.trans (h₁ ▸ remove_ends_union hend), hb₂.trans (h₂ ▸ remove_ends_union hend)⟩
  · exact ⟨E₂, E₁, hE₂, hE₁, (union_comm _ _).trans hU,
      hb₂.trans (h₂ ▸ remove_ends_union hend), hb₁.trans (h₁ ▸ remove_ends_union hend)⟩

end GraphMinor.GM12
