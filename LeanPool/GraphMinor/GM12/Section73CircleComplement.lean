/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Defs
import LeanPool.GraphMinor.Surface.CutLift
import LeanPool.GraphMinor.Surface.EdgeLoop
import LeanPool.GraphMinor.GM11.Section6

/-!
# The complementary arc of a line in a circle

For XII (7.3), Claim (1), page 262, remove the arc of the old
circuit that is collapsed into the new hub. Its complement closes
to the other arc of that circle. Split the circle at the two
ends. The interior of the given line is connected, so it lies
in one of the two resulting arcs. A connected subset of a line
containing both ends is the whole line.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- A line contained in a circle has a complementary line with
the same ends. This splits the old circuit at its collapsed arc
in XII (7.3), Claim (1), page 262. -/
theorem exists_complementary_line_in_circle
    {S : Type*} [TopologicalSpace S] [T2Space S]
    {F L : Set S} {p q : S} (hF : IsOArc F) (hL : IsLineWithEnds L p q)
    (hLF : L ⊆ F) :
    ∃ B : Set S, IsLineWithEnds B p q ∧ L ∪ B = F ∧ L ∩ B = {p, q} := by
  obtain ⟨a, ha, hrange, h₀, h₁⟩ := hL.exists_arc
  have hpq : p ≠ q := by
    intro hpq
    have heq := ha.2 (h₀.trans (hpq.trans h₁.symm))
    exact (zero_ne_one : (0 : unitInterval) ≠ 1) heq
  obtain ⟨A, B, hA, hB, hAB, hcap⟩ := hF.lines (hLF hL.left_mem) (hLF hL.right_mem) hpq
  have hpre : IsPreconnected (L \ {p, q}) := GM11.IsLineWithEnds.isPreconnected_sdiff_pair hL
  have hcover : L \ {p, q} ⊆ A ∪ B := fun x hx => hAB.symm ▸ hLF hx.1
  have hside : L \ {p, q} ⊆ A ∨ L \ {p, q} ⊆ B := by
    by_cases hmeet : ((L \ {p, q}) ∩ A).Nonempty
    · left
      intro x hx
      by_contra hxn
      have hxB := (hcover hx).resolve_left hxn
      obtain ⟨z, hzL, hzA, hzB⟩ := isPreconnected_closed_iff.mp hpre A B
        hA.isCompact.isClosed hB.isCompact.isClosed hcover hmeet ⟨x, hx, hxB⟩
      exact hzL.2 (hcap.subset ⟨hzA, hzB⟩)
    · right
      intro x hx
      exact (hcover hx).resolve_left (fun hxA => hmeet ⟨x, hx, hxA⟩)
  have hpreL : IsPreconnected L := hrange ▸ isPreconnected_range ha.1
  have extend : ∀ (C : Set S), p ∈ C → q ∈ C → L \ {p, q} ⊆ C → L ⊆ C := by
    intro C hpC hqC hsub x hx
    by_cases hxpq : x ∈ ({p, q} : Set S)
    · rcases hxpq with rfl | rfl
      · exact hpC
      · exact hqC
    · exact hsub ⟨hx, hxpq⟩
  rcases hside with hLA | hLB
  · have hLA' := extend A hA.left_mem hA.right_mem hLA
    have hEq := hA.eq_of_subset hpreL hLA' hL.left_mem hL.right_mem
    exact ⟨B, hB, hEq.symm ▸ hAB, hEq.symm ▸ hcap⟩
  · have hLB' := extend B hB.left_mem hB.right_mem hLB
    have hEq := hB.eq_of_subset hpreL hLB' hL.left_mem hL.right_mem
    exact ⟨A, hA, hEq.symm ▸ (union_comm A B ▸ hAB),
      hEq.symm ▸ (inter_comm A B ▸ hcap)⟩

end GraphMinor.GM12
