/-
Copyright (c) 2026 MohammadTaghi Hajiaghayi and Mahdi JafariRaviz. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: MohammadTaghi Hajiaghayi, Mahdi JafariRaviz
-/

/- Modified by Lean Pool contributors for the Lean 4.36 port. -/

module

public import LeanPool.GraphMinor.GM12.Section3CapOneDisc
import LeanPool.GraphMinor.GM12.Section3SubspaceArcs
import LeanPool.GraphMinor.Surface.DiscArcs
import LeanPool.GraphMinor.Surface.DiscGrow

/-!
# Surrounding curves bound discs after filling a cuff

For XII (3.1)(v), page 245, a curve surrounding a cuff in VII's sense
must be read as a curve in the original surface. Fill that cuff by its
deleted disc. Planarity in the capped surface supplies a containing
disc, and the disc Jordan theorem supplies the disc bounded by the
curve. Inclusion then returns that disc to the original surface.
-/

public section

namespace GraphMinor.GM12

open Set Topology Surface GM11

/-- A circle surrounding a prescribed cuff bounds a disc in the
original surface which avoids the interiors of all other deleted discs. -/
theorem surrounding_bounds_disc_in_partial_fill
    {S : Type*} {ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (i : ι) {F : Set (discComplement Δ)} (hF : IsOArc F)
    (hs : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i))) :
    ∃ D : Set S, IsClosedDisc D ∧
      discBd D = (Subtype.val : discComplement Δ → S) '' F ∧
      D ⊆ discComplement (fun k : {k // k ≠ i} => Δ k.val) := by
  let C := discComplement Δ
  let T := discComplement (fun k : {k // k ≠ i} => Δ k.val)
  obtain ⟨j, hj, hjval⟩ := exists_cap_discComplement_cuff hS Δ hΔ hdisj i
  obtain ⟨E, hE, hFE⟩ := hs.2.1.2.2 T j (Subtype.val ⁻¹' Δ i) hj
  have hjoarc : IsOArc (j '' F) := by
    obtain ⟨φ⟩ := hF
    exact ⟨φ.trans (hj.isEmbedding.homeomorphImage F)⟩
  obtain ⟨D, hD, _⟩ := disc_oArc E (j '' F) hE hFE hjoarc
  have hamb := isClosedDisc_subtype_image hD.2.1
  refine ⟨Subtype.val '' D, hamb.1, ?_, ?_⟩
  · rw [hamb.2, hD.2.2.1, image_image]
    exact image_congr fun x _ => hjval x
  · rintro x ⟨y, _, rfl⟩
    exact y.property

/-- The disc bounded by a surrounding circle contains the deleted
disc of its cuff. If it did not, it would lie in Sigma-star and make
the circle planar there, contrary to the definition of surrounding. -/
theorem surrounding_bounds_disc_including_deleted_disc
    {S : Type*} {ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (i : ι) {F : Set (discComplement Δ)} (hF : IsOArc F)
    (hs : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i))) :
    ∃ D : Set S, IsClosedDisc D ∧
      discBd D = (Subtype.val : discComplement Δ → S) '' F ∧
      Δ i ⊆ D ∧ D ⊆ discComplement (fun k : {k // k ≠ i} => Δ k.val) := by
  obtain ⟨D, hD, hbd, hDT⟩ := surrounding_bounds_disc_in_partial_fill hS Δ hΔ hdisj i hF hs
  refine ⟨D, hD, hbd, ?_, hDT⟩
  have hdis : Disjoint (discInt (Δ i)) (discBd D) := by
    apply Set.disjoint_left.mpr
    intro x hxI hxB
    rw [hbd] at hxB
    obtain ⟨y, hy, rfl⟩ := hxB
    exact hxI.2 (discComplement_inter_disc_subset_boundary hS Δ hΔ i ⟨y.property, hxI.1⟩)
  rcases hD.side (fun x => (hS.2.2 x).isManifoldPoint)
    (hΔ i).isPreconnected_discInt hdis with hin | hout
  · have hcl : closure (discInt (Δ i)) ⊆ D := by
      rw [← hD.isClosed.closure_eq]
      exact closure_mono (hin.trans (discInt_subset D))
    exact (hΔ i).subset_closure_discInt.trans hcl
  · have hDC : D ⊆ discComplement Δ := by
      intro x hxD
      have hxT := hDT hxD
      rw [discComplement_except_eq_union Δ hΔ hdisj i] at hxT
      rcases hxT with hxC | hxi
      · exact hxC
      · by_cases hxb : x ∈ discBd (Δ i)
        · exact disc_boundary_subset_discComplement hS Δ hΔ hdisj i hxb
        · exact False.elim (Set.disjoint_left.mp hout ⟨hxi, hxb⟩ hxD)
    have hp : IsPlanar F := by
      refine ⟨Subtype.val ⁻¹' D, (isClosedDisc_subtype_preimage hDC hD).1, ?_⟩
      intro y hy
      exact discBd_subset D (hbd.symm ▸ mem_image_of_mem Subtype.val hy)
    exact False.elim (hs.2.2 hp)

/-- The disc bounded by a surrounding circle includes exactly the
deleted disc of its cuff. The other deleted discs have interior points
outside the partially filled surface. -/
theorem surrounding_bounds_disc_including_exactly_one
    {S : Type*} {ι : Type*} [TopologicalSpace S] [T2Space S] [Finite ι]
    (hS : IsClosedSurface S) (Δ : ι → Set S)
    (hΔ : ∀ i, IsClosedDisc (Δ i))
    (hdisj : Pairwise (fun i j => Disjoint (Δ i) (Δ j)))
    (i : ι) {F : Set (discComplement Δ)} (hF : IsOArc F)
    (hs : GM07.SurroundsCuff F (Subtype.val ⁻¹' discBd (Δ i))) :
    ∃ D : Set S, IsClosedDisc D ∧
      discBd D = (Subtype.val : discComplement Δ → S) '' F ∧
      ∀ j, Δ j ⊆ D ↔ j = i := by
  obtain ⟨D, hD, hbd, hiD, hDT⟩ :=
    surrounding_bounds_disc_including_deleted_disc hS Δ hΔ hdisj i hF hs
  refine ⟨D, hD, hbd, fun j => ⟨?_, ?_⟩⟩
  · intro hjD
    by_contra hji
    obtain ⟨y, hy⟩ := (hΔ j).nonempty_discInt
    have hyT := hDT (hjD hy.1)
    have hyB := discComplement_inter_disc_subset_boundary hS
      (fun k : {k // k ≠ i} => Δ k.val) (fun k => hΔ k.val) ⟨j, hji⟩ ⟨hyT, hy.1⟩
    exact hy.2 hyB
  · rintro rfl
    exact hiD

end GraphMinor.GM12
