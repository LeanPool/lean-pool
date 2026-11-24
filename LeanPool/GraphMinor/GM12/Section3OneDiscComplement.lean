/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3PuncturedBoundary
public import LeanPool.GraphMinor.GM06.Defs
public import LeanPool.GraphMinor.Surface.TopologyStatements
import LeanPool.GraphMinor.Surface.SphereDisc
import LeanPool.GraphMinor.GM11.Section6

/-!
# The complement of one prescribed disc on the sphere

For the last case of XII (3.2), page 247, the punctured surface is
a closed disc. The sphere-disc theorem gives the disc on the other
side of the prescribed boundary circle. It is the closure of the
prescribed disc's complement, and has that same boundary circle.
Thus VI (3.6) applies to the drawing in this complementary disc.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- On the sphere, the closed complement of a closed disc is a closed
disc with the same boundary, as used in XII (3.2), page 247. -/
theorem isClosedDisc_closure_compl_of_sphere
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S) (hs : IsSphere S)
    {Δ : Set S} (hΔ : IsClosedDisc Δ) :
    IsClosedDisc (closure (univ \ Δ)) ∧ discBd (closure (univ \ Δ)) = discBd Δ := by
  obtain ⟨D, E, _, hD, hE, hbD, hbE, hU, hcap, _, huniq⟩ :=
    sphere_disc S hs (discBd Δ) hΔ.isOArc_discBd
  have hex : ∃ E : Set S, IsClosedDisc E ∧ discBd E = discBd Δ ∧
      Δ ∪ E = univ ∧ Δ ∩ E = discBd Δ := by
    rcases huniq Δ hΔ rfl with h | h
    · exact ⟨E, hE, hbE, h ▸ hU, h ▸ hcap⟩
    · refine ⟨D, hD, hbD, ?_, ?_⟩
      · rw [h, union_comm]
        exact hU
      · exact (congrArg (fun X : Set S => X ∩ D) h).trans
          ((inter_comm E D).trans hcap)
  obtain ⟨E, hE, hbE, hU, hcap⟩ := hex
  have hCE : closure (univ \ Δ) = E := by
    apply Subset.antisymm
    · apply closure_minimal _ hE.isCompact.isClosed
      intro x hx
      have h := hU.symm.subset (mem_univ x)
      exact h.resolve_left hx.2
    · intro x hxE
      by_cases hxΔ : x ∈ Δ
      · have hxB := hcap.subset ⟨hxΔ, hxE⟩
        rw [← IsClosedDisc.frontier_eq_discBd hS hΔ, frontier_eq_closure_inter_closure,
          compl_eq_univ_sdiff] at hxB
        exact hxB.2
      · exact subset_closure ⟨mem_univ _, hxΔ⟩
  rw [hCE]
  exact ⟨hE, hbE⟩

/-- The punctured sphere with one deleted disc is a closed disc
space, in the original objects of VI (3.6). -/
theorem isClosedDiscSpace_discComplement_one
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S) (hs : IsSphere S)
    (Δ : Fin 1 → Set S) (hΔ : ∀ i, IsClosedDisc (Δ i)) :
    GM06.IsClosedDiscSpace (discComplement Δ) := by
  have hsingle : (⋃ i, Δ i) = Δ 0 := by
    ext x
    simp only [mem_iUnion, Fin.exists_fin_one]
  have hcomp : discComplement Δ = closure (univ \ Δ 0) := by
    rw [discComplement, hsingle, compl_eq_univ_sdiff]
  change Nonempty (ClosedUnitDisc ≃ₜ discComplement Δ)
  rw [hcomp]
  exact (isClosedDisc_closure_compl_of_sphere hS hs (hΔ 0)).1

end GraphMinor.GM12
