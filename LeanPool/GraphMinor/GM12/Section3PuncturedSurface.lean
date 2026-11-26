/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CollarManifold
import LeanPool.GraphMinor.GM12.Section3FillingConnected
import LeanPool.GraphMinor.Surface.DiscMerge

/-!
# The remaining space is a surface

XII (3.1), page 245, applies the surface theorem of VII to the closure
of the complement of disjoint discs. Near each disc boundary a collar
avoiding the other discs gives a half-plane chart. Away from the discs,
the inclusion into the original surface is open. Closedness supplies
compactness, so these charts prove the required surface assertion.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface

/-- Boundary points of the prescribed discs are manifold points of the
remaining space, using collars chosen to avoid all the other discs. -/
theorem isManifoldPoint_discComplement_boundary
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    {x : discComplement Δ} {i : ι} (hx : x.val ∈ discBd (Δ i)) :
    IsManifoldPoint x := by
  classical
  let B : Set S := ⋃ j : {j // j ≠ i}, Δ j.val
  have hB : IsClosed B := isClosed_iUnion_of_finite fun j => (hΔ j.val).isCompact.isClosed
  have hsub : discBd (Δ i) ⊆ Bᶜ := by
    intro y hy hmem
    obtain ⟨j, hj⟩ := mem_iUnion.mp hmem
    exact Set.disjoint_left.mp (hdisj j.property.symm) (discBd_subset _ hy) hj
  obtain ⟨E, hE, hDE, hEB⟩ := exists_disc_around
    (fun y => (hS.2.2 y).isManifoldPoint) (hΔ i)
    (fun y _ => hS.2.2 y) hB.isOpen_compl hsub
  have hmiss : ∀ j, j ≠ i → Disjoint E (Δ j) := by
    intro j hji
    apply Set.disjoint_left.mpr
    intro y hyE hyj
    rcases hEB hyE with hyD | hyB
    · exact Set.disjoint_left.mp (hdisj hji.symm) hyD hyj
    · exact hyB (mem_iUnion.mpr ⟨⟨j, hji⟩, hyj⟩)
  obtain ⟨p⟩ := (hΔ i).isOArc_discBd
  obtain ⟨c, c', hc, hc', hcE, _, hl, _, himage, _, hp⟩ :=
    exists_disc_collar (hΔ i) hE hDE p
  obtain ⟨w, hw⟩ := p.surjective ⟨x.val, hx⟩
  have hval : c w = x.val := (hp w).trans (congrArg Subtype.val hw)
  have hm := isManifoldPoint_discComplement_of_collar hS Δ hΔ hdisj i
    hc hc' hcE hmiss hl himage p hp w
  have heq : (⟨c w, disc_boundary_subset_discComplement hS Δ hΔ hdisj i
      (hp w ▸ (p w).property)⟩ : discComplement Δ) = x := Subtype.ext hval
  exact heq ▸ hm

/-- The space Sigma-star used in XII (3.1), page 245, is a compact
surface with boundary. No surface structure on it is assumed. -/
theorem discComplement_isSurface
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j))) :
    IsSurface (discComplement Δ) := by
  let : CompactSpace S := hS.1
  have : CompactSpace (discComplement Δ) :=
    isCompact_iff_compactSpace.mp isClosed_closure.isCompact
  refine ⟨inferInstance, inferInstance, fun x => ?_⟩
  by_cases hx : x.val ∈ ⋃ i, Δ i
  · obtain ⟨i, hxi⟩ := mem_iUnion.mp hx
    exact isManifoldPoint_discComplement_boundary hS Δ hΔ hdisj
      (discComplement_inter_disc_subset_boundary hS Δ hΔ i ⟨x.property, hxi⟩)
  · let O : Set S := (⋃ i, Δ i)ᶜ
    have hO : IsOpen O :=
      (isClosed_iUnion_of_finite fun i => (hΔ i).isCompact.isClosed).isOpen_compl
    have hOC : O ⊆ discComplement Δ := subset_closure
    have hm : IsManifoldPoint (⟨x.val, hx⟩ : O) :=
      (isManifoldPoint_iff_of_isOpenEmbedding hO.isOpenEmbedding_subtypeVal).mp
        (hS.2.2 x.val).isManifoldPoint
    exact isManifoldPoint_of_isOpenEmbedding
      (isOpenEmbedding_inclusion_of_isOpen hO hOC) hm

/-- Removing the disc interiors preserves connectedness in XII (3.1),
page 245. Each closed disc meets the remaining space in its connected
boundary, so a separation would extend to the original surface. -/
theorem discComplement_isConnected
    {S ι : Type*} [TopologicalSpace S] [T2Space S] [ConnectedSpace S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j))) :
    IsConnected (discComplement Δ) := by
  have hmeet : ∀ i, discComplement Δ ∩ Δ i = discBd (Δ i) := by
    intro i
    apply Subset.antisymm (discComplement_inter_disc_subset_boundary hS Δ hΔ i)
    intro x hx
    exact ⟨disc_boundary_subset_discComplement hS Δ hΔ hdisj i hx,
      discBd_subset _ hx⟩
  have hcover : univ ⊆ discComplement Δ ∪ ⋃ i, Δ i := by
    intro x _
    by_cases hx : x ∈ ⋃ i, Δ i
    · exact Or.inr hx
    · exact Or.inl (subset_closure hx)
  have hpre : IsPreconnected (discComplement Δ) :=
    isPreconnected_of_finite_fillings isClosed_closure Δ
      (fun i => (hΔ i).isCompact.isClosed) hdisj
      (fun i => by rw [hmeet i]; exact (hΔ i).isOArc_discBd.isPreconnected)
      hcover
  obtain ⟨x⟩ := (inferInstance : Nonempty S)
  have hne : (discComplement Δ).Nonempty := by
    rcases hcover (mem_univ x) with hxC | hxD
    · exact ⟨x, hxC⟩
    · obtain ⟨i, hxi⟩ := mem_iUnion.mp hxD
      obtain ⟨p⟩ := (hΔ i).isOArc_discBd
      exact ⟨(p 1).val, disc_boundary_subset_discComplement hS Δ hΔ hdisj i (p 1).property⟩
  exact ⟨hne, hpre⟩

end GraphMinor.GM12
