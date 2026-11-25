/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM16.Defs
import LeanPool.GraphMinor.GM12.Section4PendantLine
import LeanPool.GraphMinor.GM09.DiscDrawing

/-!
# Drawing the small clique targets

The small cases in XII (4.4), page 251, follow from (4.3) because
the target clique can be drawn in the surface. For at most two
vertices, use an edgeless drawing or one line inside a surface
chart. The branch construction of (4.4) also works for three and
four vertices, since each vertex then has two other vertices.
-/

public section

namespace GraphMinor.GM12

open Set Graph Surface GM09

/-- A two-vertex clique can be drawn along a single line in any
nonempty closed surface, for the small cases of XII (4.4). -/
theorem exists_graphDrawing_complete_two
    {S : Type*} [TopologicalSpace S] [T2Space S] [Nonempty S]
    (hS : IsClosedSurface S) : Nonempty (GraphDrawing (GM16.completeGraph 2) S) := by
  classical
  let x : S := Classical.choice inferInstance
  obtain ⟨w, K, hK, hw, _⟩ := exists_line_at_isolated_point hS
    (show x ∈ ({x} : Set S) by simp) (by simp)
  let ν : Fin 2 → S := fun v => if v = 0 then x else w
  have hν0 : ν 0 = x := by simp [ν]
  have hν1 : ν 1 = w := by simp [ν]
  have hV : (GM16.completeGraph 2).vertexSet = ({0, 1} : Set (Fin 2)) := by
    ext v
    fin_cases v <;> simp [GM16.completeGraph, GraphMinor.completeGraph]
  have hE : (GM16.completeGraph 2).edgeSet = {s(0, 1)} := by
    ext e
    constructor
    · rintro ⟨i, j, hij, rfl⟩
      fin_cases i <;> fin_cases j <;> simp_all [Sym2.eq_swap]
    · intro he
      have heq := Set.mem_singleton_iff.mp he
      subst e
      exact ⟨0, 1, by decide, rfl⟩
  have hlink : (GM16.completeGraph 2).IsLink s(0, 1) 0 1 := ⟨by decide, rfl⟩
  have hνne : ν 0 ≠ ν 1 := by
    rw [hν0, hν1]
    intro heq
    exact hw (Set.mem_singleton_iff.mpr heq.symm)
  have hKν : IsLineWithEnds K (ν 0) (ν 1) := by rwa [hν0, hν1]
  obtain ⟨D, _, _⟩ := GraphDrawing.of_single_edge hV hE hlink hνne hKν
  exact ⟨D⟩

/-- The drawable targets needed for the cases with fewer than three
clique vertices in XII (4.4). -/
theorem exists_graphDrawing_complete_of_le_two
    {S : Type*} [TopologicalSpace S] [T2Space S] [Nonempty S]
    (hS : IsClosedSurface S) {p : ℕ} (hp : p ≤ 2) :
    Nonempty (GraphDrawing (GM16.completeGraph p) S) := by
  classical
  interval_cases p
  · have hE : (GM16.completeGraph 0).edgeSet = ∅ := by
      ext e
      constructor
      · rintro ⟨v, _, _⟩
        exact Fin.elim0 v
      · exact fun h => h.elim
    obtain ⟨D, _, _⟩ := GraphDrawing.of_edgeless (G := GM16.completeGraph 0) (Set.toFinite _) hE
      (ν := fun _ => Classical.choice ‹Nonempty S›) (fun _ _ _ _ _ => Subsingleton.elim _ _)
    exact ⟨D⟩
  · have hE : (GM16.completeGraph 1).edgeSet = ∅ := by
      ext e
      constructor
      · rintro ⟨v, w, hvw, _⟩
        exact False.elim (hvw (Subsingleton.elim _ _))
      · exact fun h => h.elim
    obtain ⟨D, _, _⟩ := GraphDrawing.of_edgeless (G := GM16.completeGraph 1) (Set.toFinite _) hE
      (ν := fun _ => Classical.choice ‹Nonempty S›) (fun _ _ _ _ _ => Subsingleton.elim _ _)
    exact ⟨D⟩
  · exact exists_graphDrawing_complete_two hS

end GraphMinor.GM12
