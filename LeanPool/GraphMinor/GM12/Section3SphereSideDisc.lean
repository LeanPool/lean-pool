/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Defs
public import LeanPool.GraphMinor.Surface.TopologyStatements
import LeanPool.GraphMinor.Surface.SphereDisc
import LeanPool.GraphMinor.GM11.Section6
import LeanPool.GraphMinor.GM12.Section3ThetaCircles
import LeanPool.GraphMinor.Surface.SurfaceGraph

/-!
# Choosing the side of a theta circle opposite its third arc

For the one-disc sphere case of XII (3.2), page 247, each union
of the separator line with one boundary arc bounds a disc which
misses the other arc except at its ends. The interior of that other
arc is connected and misses the circle. Of the two sphere discs,
choose the one not containing a point of that arc interior. The
whole arc interior then stays outside the chosen disc.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

private theorem exists_sphere_disc_disjoint_connected
    {S : Type*} [TopologicalSpace S] [T2Space S] (hS : IsClosedSurface S) (hs : IsSphere S)
    {F C : Set S} (hF : IsOArc F) (hC : IsPreconnected C) (hne : C.Nonempty)
    (hCF : Disjoint C F) :
    ∃ D : Set S, IsClosedDisc D ∧ discBd D = F ∧ Disjoint C D := by
  obtain ⟨D, E, _, hD, hE, hbD, hbE, _, hcap, _, _⟩ := sphere_disc S hs F hF
  obtain ⟨x, hx⟩ := hne
  have chooseSide : ∀ D : Set S, IsClosedDisc D → discBd D = F → x ∉ D →
      Disjoint C D := by
    intro D hD hb hxD
    have hfr : frontier D = F := by
      rw [IsClosedDisc.frontier_eq_discBd hS hD, hb]
    apply (subset_or_disjoint_of_frontier hD.isCompact.isClosed hC (hfr.symm ▸ hCF)).resolve_left
    exact fun hsub => hxD (hsub hx)
  by_cases hxD : x ∈ D
  · have hxE : x ∉ E := fun hxE => Set.disjoint_left.mp hCF hx (hcap.subset ⟨hxD, hxE⟩)
    exact ⟨E, hE, hbE, chooseSide E hE hbE hxE⟩
  · exact ⟨D, hD, hbD, chooseSide D hD hbD hxD⟩

/-- A line has a point other than its two ends. -/
theorem line_sdiff_ends_nonempty {S : Type*} [TopologicalSpace S]
    {L : Set S} {a b : S} (hL : IsLineWithEnds L a b) : (L \ {a, b}).Nonempty :=
  Surface.IsLineWithEnds.nonempty_sdiff hL

/-- The side disc used for a boundary arc and separator line in
XII (3.2), page 247. Its opposite arc meets it only at the common ends. -/
theorem exists_sphere_theta_side_disc
    {S : Type*} [TopologicalSpace S] [T2Space S]
    (hS : IsClosedSurface S) (hs : IsSphere S)
    {A B P : Set S} {a b : S} (hA : IsLineWithEnds A a b)
    (hB : IsLineWithEnds B a b) (hP : IsLineWithEnds P a b)
    (hAB : A ∩ B = {a, b}) (hAP : A ∩ P = {a, b}) (hBP : B ∩ P = {a, b}) :
    ∃ D : Set S, IsClosedDisc D ∧ discBd D = B ∪ P ∧
      A ∩ D = {a, b} ∧ ¬ A ⊆ D ∧ A ∪ B ⊆ closure (univ \ D) := by
  have hC : Disjoint (A \ {a, b}) (B ∪ P) := by
    apply Set.disjoint_left.mpr
    intro x hx hxF
    rcases hxF with hxB | hxP
    · exact hx.2 (hAB.subset ⟨hx.1, hxB⟩)
    · exact hx.2 (hAP.subset ⟨hx.1, hxP⟩)
  have hne := line_sdiff_ends_nonempty hA
  obtain ⟨D, hD, hbD, hCD⟩ := exists_sphere_disc_disjoint_connected hS hs
    (isOArc_union_of_lines_inter_eq_ends hB hP hBP)
    (GM11.IsLineWithEnds.isPreconnected_sdiff_pair hA) hne hC
  have hend : ({a, b} : Set S) ⊆ B := fun x hx => (hAB.symm.subset hx).2
  have hBD : B ⊆ discBd D := by rw [hbD]; exact subset_union_left
  have hcap : A ∩ D = {a, b} := by
    apply Subset.antisymm
    · intro x hx
      by_contra hxn
      exact Set.disjoint_left.mp hCD ⟨hx.1, hxn⟩ hx.2
    · intro x hx
      exact ⟨(hAB.symm.subset hx).1, Surface.discBd_subset D (hBD (hend hx))⟩
  have hnot : ¬ A ⊆ D := by
    intro hsub
    obtain ⟨x, hx⟩ := hne
    exact Set.disjoint_left.mp hCD hx (hsub hx.1)
  have hf : discBd D ⊆ closure (univ \ D) := by
    rw [← IsClosedDisc.frontier_eq_discBd hS hD]
    rw [frontier_eq_closure_inter_closure, compl_eq_univ_sdiff]
    exact inter_subset_right
  refine ⟨D, hD, hbD, hcap, hnot, ?_⟩
  rintro x (hxA | hxB)
  · by_cases hxD : x ∈ D
    · have hxend := hcap.subset ⟨hxA, hxD⟩
      exact hf (hBD (hend hxend))
    · exact subset_closure ⟨mem_univ _, hxD⟩
  · exact hf (hBD hxB)

end GraphMinor.GM12
