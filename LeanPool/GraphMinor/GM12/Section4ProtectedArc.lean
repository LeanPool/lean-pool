/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.CrossCut
import LeanPool.GraphMinor.GM12.Section4DiscEnlargement
import LeanPool.GraphMinor.GM12.Section3NormalPuncturedPaths
import LeanPool.GraphMinor.GM11.PaintingCells
import LeanPool.GraphMinor.Surface.ArcInPath

/-!
# Arcs outside a finite family of closed discs

For XII (4.3), claim (7), page 251, joining arcs for an ambient
motion must avoid all discs already fixed. Enlarge those discs
slightly without capturing either endpoint. A path outside the
interiors of the enlargements avoids the original closed discs.
Removing repetitions gives the required arc.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- Two distinct points outside disjoint closed discs are joined by
an arc avoiding all those discs. -/
theorem exists_arc_avoiding_closed_discs
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (D : ι → Set S) (hD : ∀ i, IsClosedDisc (D i))
    (hDD : Pairwise (fun i j => Disjoint (D i) (D j)))
    {x y : S} (hxy : x ≠ y) (hx : x ∉ ⋃ i, D i) (hy : y ∉ ⋃ i, D i) :
    ∃ a : unitInterval → S, IsArcMap a ∧ a 0 = x ∧ a 1 = y ∧
      Disjoint (range a) (⋃ i, D i) := by
  have hDB : ∀ i ∈ (univ : Set ι), Disjoint (D i) ({x, y} : Set S) := by
    intro i _
    apply Set.disjoint_right.mpr
    intro z hz hzD
    rcases hz with rfl | hz
    · exact hx (mem_iUnion.mpr ⟨i, hzD⟩)
    · have heq := Set.mem_singleton_iff.mp hz
      subst z
      exact hy (mem_iUnion.mpr ⟨i, hzD⟩)
  obtain ⟨E, hE, hEE⟩ := exists_disjoint_disc_enlargements hS (Set.toFinite (univ : Set ι)) D
    (fun i _ => hD i) (fun i _ j _ hij => hDD hij)
    {x, y} (isClosed_singleton.union isClosed_singleton) hDB
  have hEdisc : ∀ i, IsClosedDisc (E i) := fun i => (hE i (mem_univ i)).1
  have hxE : x ∈ discComplement E := by
    apply subset_closure
    intro hxunion
    obtain ⟨i, hxi⟩ := mem_iUnion.mp hxunion
    exact Set.disjoint_left.mp (hE i (mem_univ i)).2.2 hxi (by simp)
  have hyE : y ∈ discComplement E := by
    apply subset_closure
    intro hyunion
    obtain ⟨i, hyi⟩ := mem_iUnion.mp hyunion
    exact Set.disjoint_left.mp (hE i (mem_univ i)).2.2 hyi (by simp)
  let Γ : Drawing S := pointsDrawing (Set.finite_empty : (∅ : Set S).Finite)
  have hΓU : Γ.U = ∅ := rfl
  have hΓV : Γ.V = ∅ := rfl
  obtain ⟨q, hq, _⟩ := exists_normal_path_in_discComplement hS Γ E hEdisc
    (fun i j hij => hEE i (mem_univ i) j (mem_univ j) hij)
    (fun i => by rw [hΓU, hΓV, empty_inter, empty_inter]) hxE hyE
    (Or.inl (by rw [hΓU]; exact notMem_empty x))
    (Or.inl (by rw [hΓU]; exact notMem_empty y))
  have hends : q 0 ≠ q 1 := by simpa only [q.source, q.target] using hxy
  obtain ⟨a, hac, hai, ha0, ha1, haq⟩ := exists_arc_of_path q.continuous hends
  refine ⟨a, ⟨hac, hai⟩, ha0.trans q.source, ha1.trans q.target, ?_⟩
  apply Set.disjoint_left.mpr
  intro z hza hzD
  obtain ⟨i, hzi⟩ := mem_iUnion.mp hzD
  have hzint : z ∈ interior (E i) := by
    have hz := (hE i (mem_univ i)).2.1 hzi
    rw [← IsClosedDisc.frontier_eq_discBd hS (hEdisc i)] at hz
    exact (mem_interior_iff_notMem_frontier hz.1).mpr hz.2
  have hCout : discComplement E ⊆ (interior (E i))ᶜ := by
    apply closure_minimal
    · intro w hw hwi
      exact hw (mem_iUnion.mpr ⟨i, interior_subset hwi⟩)
    · exact isOpen_interior.isClosed_compl
  exact hCout (hq (haq hza)) hzint

end GraphMinor.GM12
