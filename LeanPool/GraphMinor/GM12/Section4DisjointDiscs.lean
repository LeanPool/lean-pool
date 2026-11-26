/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.Surface.Collar
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.Surface.Triangulate
import Mathlib.Data.Fintype.EquivFin
import LeanPool.GraphMinor.Surface.Circle

/-!
# Finite disjoint disc families in a closed surface

The singleton feasibility argument in XII (4.4), page 251, starts
with one connecting disc for each partition class. Choose finitely
many distinct points on a disc boundary, separate them by disjoint
open neighborhoods, and put a smaller closed disc in each one.
-/

public section

namespace GraphMinor.GM12

open Set Surface GM11

/-- A topological circle has infinitely many points, in any universe. -/
theorem infinite_oArc {X : Type*} [TopologicalSpace X] {F : Set X}
    (hF : IsOArc F) : F.Infinite :=
  hF.infinite

/-- A nonempty closed surface contains any prescribed finite number
of pairwise disjoint closed discs. -/
theorem exists_finite_disjoint_closed_discs
    {S : Type*} [TopologicalSpace S] [T2Space S] [Nonempty S]
    (hS : IsClosedSurface S) (p : ℕ) :
    ∃ D : Fin p → Set S, (∀ i, IsClosedDisc (D i)) ∧
      ∀ i j, i ≠ j → Disjoint (D i) (D j) := by
  classical
  let x : S := Classical.choice inferInstance
  obtain ⟨C, _, hC, _, _, _, _⟩ := exists_closedDisc_nbhd hS isOpen_univ (mem_univ x)
  have : Infinite (discBd C) := (infinite_oArc hC.isOArc_discBd).to_subtype
  let n : ℕ ↪ discBd C := Infinite.natEmbedding _
  let ν : Fin p → S := fun i => (n i.val).val
  have hν : Function.Injective ν := by
    intro i j hij
    apply Fin.ext
    exact n.injective (Subtype.ext hij)
  obtain ⟨U, hU, hUdisj⟩ := (Set.finite_range ν).t2_separation
  have hex : ∀ i : Fin p, ∃ D, IsClosedDisc D ∧ D ⊆ U (ν i) := by
    intro i
    obtain ⟨D, _, hD, _, _, _, hDU, _⟩ := exists_closedDisc_nbhd hS (hU (ν i)).2 (hU (ν i)).1
    exact ⟨D, hD, hDU⟩
  choose D hD hDU using hex
  refine ⟨D, hD, ?_⟩
  intro i j hij
  exact (hUdisj (mem_range_self i) (mem_range_self j) (fun h => hij (hν h))).mono (hDU i) (hDU j)

end GraphMinor.GM12
